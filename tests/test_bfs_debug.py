#!/usr/bin/env python3
"""Debug BFS-Prover generation issues."""

import sys
sys.path.insert(0, '/Users/eric/Documents/GitHub/TDCSG')

from bfs_prover_mcp.model import BFSProverModel
from bfs_prover_mcp.prompts import format_bfs_prover_prompt
from pathlib import Path

# Test simple proof state
proof_state = """n : ℕ
⊢ n + 0 = n"""

print(f"Testing with proof state:\n{proof_state}\n")

# Check the prompt format
prompt = format_bfs_prover_prompt(proof_state)
print(f"Formatted prompt:\n{repr(prompt)}\n")
print(f"Prompt length: {len(prompt)} chars\n")

# Initialize model
model_path = Path("/Users/eric/Documents/GitHub/TDCSG/BFS-Prover-V2-32B-GGUF/BFS-Prover-V2-32B.Q6_K.gguf")
print(f"Loading model from {model_path}")

model = BFSProverModel(model_path=model_path, verbose=False)
model.load()

print(f"Model loaded in {model.load_time:.2f}s\n")

# Try raw generation first
print("Testing raw llama generation...")
try:
    output = model.model(
        prompt,
        max_tokens=5000,
        temperature=0.7,
        stop=["<|endoftext|>"],
        echo=False,
    )
    print(f"Raw output: {output}")
    print(f"\nText: {output['choices'][0]['text']}")
except Exception as e:
    print(f"Error: {e}")

# Generate with model wrapper
print("\n\nTesting with model.generate_tactics...")
tactics = model.generate_tactics(proof_state, num_suggestions=3, temperature=0.7, max_tokens=128)

print(f"\nGenerated {len(tactics)} tactics:")
for i, tactic in enumerate(tactics, 1):
    print(f"{i}. {tactic}")
