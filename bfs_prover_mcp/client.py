"""
Socket client for communicating with the BFS-Prover tactic daemon.
"""

import socket
import json
import os
from pathlib import Path
from typing import Dict, List, Optional, Any


class DaemonClient:
    """Client for communicating with the tactic_server.py daemon via socket."""

    def __init__(self, host: str = "localhost", port: int = 5678, timeout: int = 30):
        """
        Initialize the daemon client.

        Args:
            host: Daemon host (default: localhost)
            port: Daemon port (default: 5678)
            timeout: Socket timeout in seconds (default: 30)
        """
        self.host = host
        self.port = port
        self.timeout = timeout
        self.pid_file = Path(".tactic_server.pid")

    def is_daemon_running(self) -> bool:
        """
        Check if the daemon is running by checking PID file and socket connection.

        Returns:
            True if daemon is running and responsive, False otherwise
        """
        # Check PID file exists
        if not self.pid_file.exists():
            return False

        # Try to read PID and check if process exists
        try:
            with open(self.pid_file, 'r') as f:
                pid = int(f.read().strip())

            # Check if process exists (doesn't work on all platforms, but works on Unix)
            try:
                os.kill(pid, 0)  # Signal 0 just checks existence
            except ProcessLookupError:
                return False
            except PermissionError:
                # Process exists but we can't send signals (shouldn't happen for our own process)
                pass

        except (FileNotFoundError, ValueError):
            return False

        # Try socket connection
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(2)  # Short timeout for status check
            sock.connect((self.host, self.port))
            sock.close()
            return True
        except (socket.error, socket.timeout):
            return False

    def get_daemon_status(self) -> Dict[str, Any]:
        """
        Get detailed daemon status information.

        Returns:
            Dictionary with status information
        """
        if not self.pid_file.exists():
            return {
                "status": "stopped",
                "port": self.port,
                "pid": None,
                "model_loaded": False
            }

        try:
            with open(self.pid_file, 'r') as f:
                pid = int(f.read().strip())
        except (FileNotFoundError, ValueError):
            return {
                "status": "stopped",
                "port": self.port,
                "pid": None,
                "model_loaded": False
            }

        # Try to connect
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(2)
            sock.connect((self.host, self.port))
            sock.close()

            return {
                "status": "running",
                "port": self.port,
                "pid": pid,
                "model_loaded": True
            }
        except (socket.error, socket.timeout):
            return {
                "status": "unresponsive",
                "port": self.port,
                "pid": pid,
                "model_loaded": False
            }

    def generate_tactics(
        self,
        proof_state: str,
        num_suggestions: int = 5,
        temperature: float = 0.7,
        max_tokens: int = 128
    ) -> Dict[str, Any]:
        """
        Request tactic suggestions from the daemon.

        Args:
            proof_state: Lean proof state from lean_goal
            num_suggestions: Number of tactics to generate (1-10)
            temperature: Sampling temperature (0.0-1.0)
            max_tokens: Maximum tokens per tactic

        Returns:
            Dictionary with tactics and metadata

        Raises:
            ConnectionRefusedError: If daemon is not running
            TimeoutError: If request times out
            ValueError: If response is invalid
        """
        # Validate inputs
        if not proof_state or not isinstance(proof_state, str):
            raise ValueError("proof_state must be a non-empty string")

        if not (1 <= num_suggestions <= 10):
            raise ValueError("num_suggestions must be between 1 and 10")

        if not (0.0 <= temperature <= 1.0):
            raise ValueError("temperature must be between 0.0 and 1.0")

        # Build request
        request = {
            "state": proof_state,
            "num": num_suggestions,
            "temp": temperature,
            "max_tokens": max_tokens
        }

        # Connect to daemon
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(self.timeout)
            sock.connect((self.host, self.port))
        except ConnectionRefusedError:
            raise ConnectionRefusedError(
                f"Cannot connect to daemon on {self.host}:{self.port}. "
                "Is it running? Try: ./tactic_server.sh start"
            )
        except socket.timeout:
            raise TimeoutError(f"Connection to daemon timed out after {self.timeout}s")

        try:
            # Send request
            request_json = json.dumps(request)
            sock.sendall(request_json.encode('utf-8'))

            # Receive response (up to 1MB)
            response_data = sock.recv(1048576).decode('utf-8')

            if not response_data:
                raise ValueError("Empty response from daemon")

            response = json.loads(response_data)

            # Check for error in response
            if "error" in response:
                raise ValueError(f"Daemon error: {response['error']}")

            return response

        except socket.timeout:
            raise TimeoutError(
                f"Daemon request timed out after {self.timeout}s. "
                "Daemon may be overloaded. Try: ./tactic_server.sh restart"
            )
        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON response from daemon: {e}")
        finally:
            sock.close()
