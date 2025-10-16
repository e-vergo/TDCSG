#!/usr/bin/env python3
"""
Generate and test Lean tactics using the tactic daemon + lean-lsp MCP.

Usage:
    python suggest_and_test.py <file_path> <line_number> <proof_state>

Example:
    python suggest_and_test.py /path/to/file.lean 10 "n : ℕ\n⊢ n + 0 = n"
"""

import json
import socket
import subprocess
import sys


def request_tactics(proof_state: str, num_suggestions: int = 10,
                   host: str = "localhost", port: int = 5678) -> list[str]:
    """Request tactic suggestions from the daemon."""
    print(f"Requesting {num_suggestions} tactics from daemon...")

    # Connect to daemon
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        sock.connect((host, port))
    except ConnectionRefusedError:
        print(f"Error: Cannot connect to daemon at {host}:{port}")
        print("Start the daemon with: python tactic_daemon.py")
        sys.exit(1)

    try:
        # Send request
        request = {
            "proof_state": proof_state,
            "num_suggestions": num_suggestions
        }
        sock.sendall(json.dumps(request).encode() + b"\n")

        # Receive response
        data = b""
        while True:
            chunk = sock.recv(4096)
            if not chunk:
                break
            data += chunk
            if b"\n" in chunk:
                break

        response = json.loads(data.decode())

        if "error" in response:
            print(f"Daemon error: {response['error']}")
            sys.exit(1)

        tactics = response.get("tactics", [])
        print(f"Received {len(tactics)} tactics\n")
        return tactics

    finally:
        sock.close()


def test_tactics_with_mcp(file_path: str, line_number: int, tactics: list[str]) -> str:
    """Test tactics using lean-lsp MCP."""
    print(f"Testing tactics at {file_path}:{line_number} using lean-lsp MCP...")

    # Start lean-lsp MCP server
    process = subprocess.Popen(
        ['uvx', 'lean-lsp-mcp'],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )

    try:
        # Initialize MCP
        init_request = {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "protocolVersion": "2024-11-05",
                "capabilities": {},
                "clientInfo": {"name": "suggest-and-test", "version": "1.0.0"}
            }
        }

        process.stdin.write(json.dumps(init_request) + '\n')
        process.stdin.flush()
        process.stdout.readline()  # Discard init response

        # Send initialized notification
        initialized = {"jsonrpc": "2.0", "method": "notifications/initialized"}
        process.stdin.write(json.dumps(initialized) + '\n')
        process.stdin.flush()

        # Call lean_multi_attempt
        tool_request = {
            "jsonrpc": "2.0",
            "id": 2,
            "method": "tools/call",
            "params": {
                "name": "lean_multi_attempt",
                "arguments": {
                    "file_path": file_path,
                    "line": line_number,
                    "snippets": tactics
                }
            }
        }

        process.stdin.write(json.dumps(tool_request) + '\n')
        process.stdin.flush()

        # Wait for response (with timeout)
        import select
        print("Waiting for lean-lsp response (timeout: 180s)...")
        ready, _, _ = select.select([process.stdout], [], [], 180)

        if not ready:
            return "Error: Timeout waiting for lean-lsp response"

        print("Response received, parsing...")
        response_line = process.stdout.readline()
        response = json.loads(response_line)

        # Extract result
        if "result" in response and "content" in response["result"]:
            content = response["result"]["content"]
            if isinstance(content, list) and len(content) > 0:
                return content[0].get("text", "")

        return "Error: Unexpected response format"

    except Exception as e:
        return f"Error: {e}"
    finally:
        process.stdin.close()
        process.terminate()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()


def main():
    if len(sys.argv) < 4:
        print(__doc__)
        sys.exit(1)

    file_path = sys.argv[1]
    line_number = int(sys.argv[2])
    proof_state = sys.argv[3]

    print("=" * 80)
    print("BFS-Prover: Suggest and Test")
    print("=" * 80)
    print(f"File: {file_path}")
    print(f"Line: {line_number}")
    print(f"Proof state:\n{proof_state}")
    print("=" * 80)
    print()

    # Get tactics from daemon
    tactics = request_tactics(proof_state)

    print("Generated tactics:")
    for i, tactic in enumerate(tactics, 1):
        print(f"  {i}. {tactic}")
    print()

    # Test tactics with lean-lsp
    results = test_tactics_with_mcp(file_path, line_number, tactics)

    print("=" * 80)
    print("TEST RESULTS")
    print("=" * 80)

    # Parse and format results
    if results.startswith("Error:"):
        print(results)
    else:
        # Parse tactic results - format is "tactic\n:\n status"
        tactic_results = results.strip().split('\n\n')
        success_count = 0

        for result in tactic_results:
            lines = result.strip().split('\n')
            if len(lines) >= 2:
                tactic = lines[0].strip()
                # Skip if it's just ':'
                if tactic == ':' or not tactic:
                    continue

                # Check for "no goals" indicating success
                if "no goals" in result:
                    print(f"✓ SUCCESS: {tactic}")
                    success_count += 1
                elif "severity:" in result:
                    # Extract error message
                    error_lines = [l for l in lines if l and not l.startswith('l') and not l.startswith(':') and not l.startswith(' ')]
                    if len(error_lines) > 1:
                        print(f"✗ FAILED: {tactic}")
                        print(f"   Error: {error_lines[-1][:100]}")
                else:
                    print(f"? UNKNOWN: {tactic}")

        print(f"\nSummary: {success_count}/{len(tactics)} tactics succeeded")

        if success_count > 0:
            print("\n" + "=" * 80)
            print("Full output:")
            print(results[:2000] + ("..." if len(results) > 2000 else ""))


if __name__ == "__main__":
    main()
