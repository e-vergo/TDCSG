#!/usr/bin/env python3
"""
Simple one-shot tactic suggestion tool for BFS-Prover-V2-7B
Takes a Lean proof state, outputs tactic suggestions

Usage:
  python3 tactic_suggest.py --state "n : ℕ\nh : n > 0\n⊢ n + 1 > 0" --num 5
  echo "proof_state" | python3 tactic_suggest.py --num 3
"""

import sys
import os
import argparse

# Suppress TensorFlow/PyTorch warnings
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '3'
import warnings
warnings.filterwarnings('ignore')

try:
    from BFS_inference import BFSProver
except ModuleNotFoundError as e:
    print("Error: Required dependencies not installed.", file=sys.stderr)
    print("\nPlease install the required packages:", file=sys.stderr)
    print("  pip install torch transformers", file=sys.stderr)
    print("\nFor Apple Silicon (M1/M2/M3 Mac):", file=sys.stderr)
    print("  pip install torch torchvision torchaudio", file=sys.stderr)
    print("  pip install transformers accelerate", file=sys.stderr)
    sys.exit(1)

def main():
    parser = argparse.ArgumentParser(
        description="Generate Lean4 tactic suggestions from proof state"
    )

    parser.add_argument(
        "--state",
        type=str,
        help="Proof state string (or read from stdin)"
    )
    parser.add_argument(
        "--num",
        type=int,
        default=3,
        help="Number of tactic suggestions (default: 3)"
    )
    parser.add_argument(
        "--temp",
        "--temperature",
        type=float,
        default=0.7,
        help="Sampling temperature (default: 0.7)"
    )
    parser.add_argument(
        "--max-tokens",
        type=int,
        default=128,
        help="Maximum tokens per tactic (default: 128)"
    )
    parser.add_argument(
        "--model-path",
        type=str,
        default="./BFS-Prover-V2-7B",
        help="Path to model directory"
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Minimal output (just tactics, one per line)"
    )
    parser.add_argument(
        "--format",
        choices=["lines", "json"],
        default="lines",
        help="Output format: lines (one per line) or json (default: lines)"
    )

    args = parser.parse_args()

    # Get proof state from args or stdin
    if args.state:
        state = args.state
    else:
        state = sys.stdin.read().strip()

    if not state:
        print("Error: No proof state provided", file=sys.stderr)
        sys.exit(1)

    # Suppress output if quiet mode
    if args.quiet:
        # Redirect stdout temporarily during model loading
        old_stdout = sys.stdout
        old_stderr = sys.stderr
        sys.stdout = open(os.devnull, 'w')
        sys.stderr = open(os.devnull, 'w')

        prover = BFSProver(model_path=args.model_path)

        # Restore stdout for results
        sys.stdout.close()
        sys.stderr.close()
        sys.stdout = old_stdout
        sys.stderr = old_stderr
    else:
        prover = BFSProver(model_path=args.model_path)

    # Generate tactics
    tactics = []
    for i in range(args.num):
        # Increase temperature slightly for diversity when generating multiple
        temp = args.temp if args.num == 1 else min(args.temp * 1.1, 1.0)

        if args.quiet:
            # Suppress generation output
            old_stdout = sys.stdout
            sys.stdout = open(os.devnull, 'w')
            tactic = prover.generate_tactic(state, max_new_tokens=args.max_tokens, temperature=temp)
            sys.stdout.close()
            sys.stdout = old_stdout
        else:
            if i > 0:
                print(f"\n{'='*70}")
                print(f"Generating suggestion {i+1}/{args.num}")
                print('='*70 + "\n")
            tactic = prover.generate_tactic(state, max_new_tokens=args.max_tokens, temperature=temp)

        tactics.append(tactic)

    # Output results
    if args.quiet or args.format == "lines":
        # Simple format: one tactic per line
        for tactic in tactics:
            print(tactic)
    elif args.format == "json":
        import json
        print(json.dumps({"tactics": tactics}, indent=2))
    else:
        # Formatted output
        print("\n" + "="*70)
        print("TACTIC SUGGESTIONS")
        print("="*70)
        for i, tactic in enumerate(tactics, 1):
            print(f"\n[{i}] {tactic}")

if __name__ == "__main__":
    main()
