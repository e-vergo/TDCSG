#!/usr/bin/env python3
"""
BFS-Prover Tactic Server - Persistent daemon that listens on a socket

Usage:
  # Start server (runs in foreground, or use & for background)
  python3 tactic_server.py --port 5678

  # Or use the wrapper script to start/stop
  ./tactic_server.sh start
  ./tactic_server.sh stop
  ./tactic_server.sh status
"""

import sys
import json
import socket
import threading
import time
import os
import signal

# Suppress warnings
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '3'
import warnings
warnings.filterwarnings('ignore')

try:
    from BFS_inference import BFSProver
except ModuleNotFoundError:
    print("Error: BFS-Prover dependencies not installed", file=sys.stderr)
    print("Run: pip install torch transformers", file=sys.stderr)
    sys.exit(1)

class TacticServer:
    def __init__(self, port=5678, model_path="./BFS-Prover-V2-7B"):
        self.port = port
        self.model_path = model_path
        self.prover = None
        self.server_socket = None
        self.running = False

    def load_model(self):
        """Load the model (done once at startup)"""
        print("Loading BFS-Prover model...", file=sys.stderr)
        self.prover = BFSProver(model_path=self.model_path)
        print("Model loaded and ready!", file=sys.stderr)

    def handle_client(self, client_socket, addr):
        """Handle a single client connection"""
        try:
            # Receive request (up to 100KB)
            data = client_socket.recv(102400).decode('utf-8')
            if not data:
                return

            request = json.loads(data)

            # Extract parameters
            state = request.get("state")
            if not state:
                response = {"error": "Missing 'state' field"}
                client_socket.sendall(json.dumps(response).encode('utf-8'))
                return

            num = request.get("num", 3)
            temp = request.get("temp", 0.7)
            max_tokens = request.get("max_tokens", 128)

            # Generate tactics
            start_time = time.time()
            tactics = []

            # Suppress generation output
            old_stdout = sys.stdout
            sys.stdout = open(os.devnull, 'w')

            try:
                for i in range(num):
                    temperature = temp if num == 1 else min(temp * 1.1, 1.0)
                    tactic = self.prover.generate_tactic(
                        state,
                        max_new_tokens=max_tokens,
                        temperature=temperature
                    )
                    tactics.append(tactic)
            finally:
                sys.stdout.close()
                sys.stdout = old_stdout

            elapsed = time.time() - start_time

            # Send response
            response = {
                "tactics": tactics,
                "time": round(elapsed, 2),
                "num_generated": len(tactics)
            }

            client_socket.sendall(json.dumps(response).encode('utf-8'))

        except Exception as e:
            error_response = {"error": str(e)}
            try:
                client_socket.sendall(json.dumps(error_response).encode('utf-8'))
            except:
                pass

        finally:
            client_socket.close()

    def start(self):
        """Start the server"""
        # Load model first
        self.load_model()

        # Create server socket
        self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.server_socket.bind(('localhost', self.port))
        self.server_socket.listen(5)

        self.running = True
        print(f"BFS-Prover server listening on localhost:{self.port}", file=sys.stderr)
        print(f"PID: {os.getpid()}", file=sys.stderr)

        # Write PID file
        with open('.tactic_server.pid', 'w') as f:
            f.write(str(os.getpid()))

        while self.running:
            try:
                # Accept connection with timeout so we can check running flag
                self.server_socket.settimeout(1.0)
                try:
                    client_socket, addr = self.server_socket.accept()
                except socket.timeout:
                    continue

                # Handle in a thread so we can serve multiple requests
                thread = threading.Thread(target=self.handle_client, args=(client_socket, addr))
                thread.daemon = True
                thread.start()

            except KeyboardInterrupt:
                break

        self.shutdown()

    def shutdown(self):
        """Shutdown the server"""
        print("\nShutting down server...", file=sys.stderr)
        self.running = False
        if self.server_socket:
            self.server_socket.close()

        # Remove PID file
        try:
            os.remove('.tactic_server.pid')
        except:
            pass

        print("Server stopped", file=sys.stderr)

def main():
    import argparse

    parser = argparse.ArgumentParser(description="BFS-Prover tactic server")
    parser.add_argument("--port", type=int, default=5678, help="Port to listen on (default: 5678)")
    parser.add_argument("--model-path", type=str, default="./BFS-Prover-V2-7B", help="Path to model")

    args = parser.parse_args()

    server = TacticServer(port=args.port, model_path=args.model_path)

    # Handle shutdown signals
    def signal_handler(sig, frame):
        server.shutdown()
        sys.exit(0)

    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)

    server.start()

if __name__ == "__main__":
    main()
