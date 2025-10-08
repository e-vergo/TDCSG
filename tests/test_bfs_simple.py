#!/usr/bin/env python3
"""Test minimal llama-cpp-python generation."""

from llama_cpp import Llama
from pathlib import Path

model_path = Path("/Users/eric/Documents/GitHub/TDCSG/BFS-Prover-V2-32B-GGUF/BFS-Prover-V2-32B.Q6_K.gguf")

print(f"Loading model...")
llm = Llama(
    model_path=str(model_path),
    n_ctx=2048,  # Try smaller context
    n_gpu_layers=-1,
    verbose=False,
    n_threads=4,
)

print(f"Model loaded\n")

# Test 1: Very simple prompt
print("Test 1: Simple prompt")
try:
    output = llm("Q: What is 2+2? A:", max_tokens=10, temperature=0.7, echo=False)
    print(f"Success: {output['choices'][0]['text']}")
except Exception as e:
    print(f"Error: {e}")

# Test 2: Lean tactic prompt
print("\nTest 2: Lean-style prompt")
prompt = "[PROOF STATE]\nn : ℕ\n⊢ n + 0 = n\n\n[TACTIC]\n"
try:
    output = llm(prompt, max_tokens=50, temperature=0.7, echo=False)
    print(f"Success: {output['choices'][0]['text']}")
except Exception as e:
    print(f"Error: {e}")

# Test 3: Try with reset between calls
print("\nTest 3: With reset")
llm.reset()
try:
    output = llm("Hello", max_tokens=10, temperature=0.7, echo=False)
    print(f"Success: {output['choices'][0]['text']}")
except Exception as e:
    print(f"Error: {e}")
