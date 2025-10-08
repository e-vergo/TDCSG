#!/usr/bin/env python3
"""
Client for BFS-Prover tactic server

Usage:
  python3 tactic_query.py --state "n : ℕ\n⊢ n + 0 = n" --num 3
  echo "proof_state" | python3 tactic_query.py
"""

import sys
import json
import socket
import argparse

def query_server(request, host='localhost', port=5678, timeout=60):
    """Send request to server and get response"""
    try:
        # Connect to server
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(timeout)
        sock.connect((host, port))

        # Send request
        sock.sendall(json.dumps(request).encode('utf-8'))

        # Receive response (up to 1MB)
        response_data = sock.recv(1048576).decode('utf-8')
        response = json.loads(response_data)

        sock.close()
        return response

    except ConnectionRefusedError:
        print("Error: Cannot connect to server. Is it running?", file=sys.stderr)
        print("Start it with: .venv/bin/python3 tactic_server.py &", file=sys.stderr)
        return None
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return None

def main():
    parser = argparse.ArgumentParser(description="Query BFS-Prover tactic server")
    parser.add_argument("--state", type=str, help="Proof state (or read from stdin)")
    parser.add_argument("--num", type=int, default=3, help="Number of suggestions (default: 3)")
    parser.add_argument("--temp", type=float, default=0.7, help="Temperature (default: 0.7)")
    parser.add_argument("--max-tokens", type=int, default=128, help="Max tokens (default: 128)")
    parser.add_argument("--format", choices=["lines", "json"], default="lines", help="Output format")
    parser.add_argument("--port", type=int, default=5678, help="Server port (default: 5678)")
    parser.add_argument("--quiet", action="store_true", help="Suppress timing info")

    args = parser.parse_args()

    # Get proof state
    state = args.state if args.state else sys.stdin.read().strip()
    if not state:
        print("Error: No proof state provided", file=sys.stderr)
        sys.exit(1)

    # Build request
    request = {
        "state": state,
        "num": args.num,
        "temp": args.temp,
        "max_tokens": args.max_tokens
    }

    # Query server
    response = query_server(request, port=args.port)

    if not response:
        sys.exit(1)

    # Handle errors
    if "error" in response:
        print(f"Error: {response['error']}", file=sys.stderr)
        sys.exit(1)

    # Output results
    tactics = response.get("tactics", [])
    gen_time = response.get("time", 0)

    if args.format == "json":
        print(json.dumps(response, indent=2))
    else:
        # Print tactics one per line
        for tactic in tactics:
            print(tactic)

        # Stats to stderr
        if not args.quiet:
            print(f"# {len(tactics)} tactics in {gen_time:.1f}s", file=sys.stderr)

if __name__ == "__main__":
    main()
