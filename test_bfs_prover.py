#!/usr/bin/env python3
"""Test script for BFS-Prover model with fixed error handling."""

import sys
from pathlib import Path

# Add bfs_prover_mcp to path
sys.path.insert(0, str(Path(__file__).parent))

from bfs_prover_mcp.model import BFSProverModel

def test_simple_proof_state():
    """Test with a simple proof state."""
    model_path = Path("BFS-Prover-V2-32B-GGUF/BFS-Prover-V2-32B.Q6_K.gguf")

    print("Loading model...")
    model = BFSProverModel(model_path=model_path, verbose=False)
    model.load()
    print(f"Model loaded in {model.load_time:.2f}s\n")

    # Simple proof state
    proof_state = "⊢ 1 + 1 = 2"

    print(f"Proof state: {proof_state}\n")
    print("Generating 5 tactics...\n")

    tactics = model.generate_tactics(
        proof_state=proof_state,
        num_suggestions=5,
        temperature=0.7,
        max_tokens=128
    )

    print("Generated tactics:")
    for i, tactic in enumerate(tactics, 1):
        print(f"  {i}. {tactic}")

    return len(tactics) > 0

def test_complex_proof_state():
    """Test with a complex proof state that was causing errors."""
    model_path = Path("BFS-Prover-V2-32B-GGUF/BFS-Prover-V2-32B.Q6_K.gguf")

    print("\n" + "="*60)
    print("Testing complex proof state...")
    print("="*60 + "\n")

    model = BFSProverModel(model_path=model_path, verbose=False)
    model.load()

    # Complex proof state (the one that was failing)
    proof_state = """⊢ (1 + TwoDiskSystem.ζ₅ - TwoDiskSystem.ζ₅ ^ 2).re * (1 + TwoDiskSystem.ζ₅ - TwoDiskSystem.ζ₅ ^ 2).re +
      (1 + TwoDiskSystem.ζ₅ - TwoDiskSystem.ζ₅ ^ 2).im * (1 + TwoDiskSystem.ζ₅ - TwoDiskSystem.ζ₅ ^ 2).im =
    3 + φ"""

    print(f"Proof state:\n{proof_state}\n")
    print("Generating 5 tactics...\n")

    try:
        tactics = model.generate_tactics(
            proof_state=proof_state,
            num_suggestions=5,
            temperature=0.7,
            max_tokens=128
        )

        print(f"✓ Successfully generated {len(tactics)} tactics:")
        for i, tactic in enumerate(tactics, 1):
            print(f"  {i}. {tactic}")

        return len(tactics) > 0
    except Exception as e:
        print(f"✗ Error: {e}")
        return False

if __name__ == "__main__":
    success1 = test_simple_proof_state()
    success2 = test_complex_proof_state()

    print("\n" + "="*60)
    if success1 and success2:
        print("✓ All tests passed!")
    else:
        print("✗ Some tests failed")
        sys.exit(1)
