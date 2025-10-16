#!/usr/bin/env python3
"""
Tactic generation daemon - keeps BFS-Prover model loaded in memory.

Listens on localhost:5678 for proof states and returns tactic suggestions.
"""

import json
import socket
import sys
from pathlib import Path
from typing import List

# Load llama_cpp
try:
    from llama_cpp import Llama
except ImportError:
    print("Error: llama-cpp-python not installed")
    print("Install with: pip install llama-cpp-python")
    sys.exit(1)


class TacticDaemon:
    def __init__(self, model_path: Path, host: str = "localhost", port: int = 5678):
        self.model_path = model_path
        self.host = host
        self.port = port
        self.model = None

    def load_model(self):
        """Load the BFS-Prover model."""
        print(f"Loading model from {self.model_path}...")
        self.model = Llama(
            model_path=str(self.model_path),
            n_ctx=4096,
            n_gpu_layers=-1,  # Use all GPU layers
            verbose=False
        )
        print("Model loaded successfully!")

    def generate_tactics(self, proof_state: str, num_suggestions: int = 10) -> List[str]:
        """Generate tactic suggestions for a proof state."""
        # BFS-Prover prompt format
        prompt = f"[GOAL]{proof_state}[PROOFSTEP]"

        tactics = []
        for _ in range(num_suggestions):
            output = self.model(
                prompt,
                max_tokens=128,
                temperature=0.7,
                stop=["[GOAL]", "\n"],
                echo=False
            )

            tactic = output['choices'][0]['text'].strip()
            if tactic and tactic not in tactics:
                tactics.append(tactic)

        return tactics

    def handle_request(self, data: dict) -> dict:
        """Handle a client request."""
        try:
            proof_state = data.get("proof_state", "")
            num_suggestions = data.get("num_suggestions", 10)

            if not proof_state:
                return {"error": "No proof_state provided"}

            tactics = self.generate_tactics(proof_state, num_suggestions)
            return {"tactics": tactics}

        except Exception as e:
            return {"error": str(e)}

    def run(self):
        """Start the daemon server."""
        self.load_model()

        # Create socket
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.bind((self.host, self.port))
        sock.listen(5)

        print(f"Daemon listening on {self.host}:{self.port}")
        print("Press Ctrl+C to stop")

        try:
            while True:
                client_sock, addr = sock.accept()
                print(f"Connection from {addr}")

                try:
                    # Receive request
                    data = b""
                    while True:
                        chunk = client_sock.recv(4096)
                        if not chunk:
                            break
                        data += chunk
                        if b"\n" in chunk:
                            break

                    if data:
                        request = json.loads(data.decode())
                        print(f"Request: {request.get('proof_state', '')[:50]}...")

                        # Handle request
                        response = self.handle_request(request)

                        # Send response
                        client_sock.sendall(json.dumps(response).encode() + b"\n")
                        print(f"Sent {len(response.get('tactics', []))} tactics")

                except Exception as e:
                    print(f"Error handling request: {e}")
                    error_response = {"error": str(e)}
                    client_sock.sendall(json.dumps(error_response).encode() + b"\n")
                finally:
                    client_sock.close()

        except KeyboardInterrupt:
            print("\nShutting down...")
        finally:
            sock.close()


def main():
    model_path = Path.home() / "Documents/GitHub/TDCSG/BFS-Prover-V2-32B-GGUF/BFS-Prover-V2-32B.Q6_K.gguf"

    if not model_path.exists():
        print(f"Error: Model not found at {model_path}")
        sys.exit(1)

    daemon = TacticDaemon(model_path)
    daemon.run()


if __name__ == "__main__":
    main()
