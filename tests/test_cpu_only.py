#!/usr/bin/env python3
"""Test BFS-Prover with CPU-only (no Metal)."""

from llama_cpp import Llama
from pathlib import Path

model_path = Path("/Users/eric/Documents/GitHub/TDCSG/BFS-Prover-V2-32B-GGUF/BFS-Prover-V2-32B.Q6_K.gguf")

print(f"Loading model (CPU only, no Metal)...")
llm = Llama(
    model_path=str(model_path),
    n_ctx=2048,
    n_gpu_layers=0,  # CPU ONLY - no GPU layers
    verbose=False,
    n_threads=8,  # Use more CPU threads
)

print(f"Model loaded\n")

# Test simple generation
print("Testing generation...")
prompt = "[PROOF STATE]\nn : ℕ\n⊢ n + 0 = n\n\n[TACTIC]\n"

try:
    output = llm(
        prompt,
        max_tokens=50,
        temperature=0.7,
        stop=["<|endoftext|>", "\n\n"],
        echo=False,
    )
    text = output['choices'][0]['text'].strip()
    print(f"✓ Success!")
    print(f"Generated: {repr(text)}")
except Exception as e:
    print(f"✗ Error: {e}")

# Try again with different settings
print("\n\nTrying with larger context...")
llm2 = Llama(
    model_path=str(model_path),
    n_ctx=4096,
    n_gpu_layers=0,
    verbose=False,
    n_threads=8,
    n_batch=512,  # Adjust batch size
)

try:
    output = llm2(
        prompt,
        max_tokens=50,
        temperature=0.7,
        stop=["<|endoftext|>", "\n\n"],
        echo=False,
    )
    text = output['choices'][0]['text'].strip()
    print(f"✓ Success!")
    print(f"Generated: {repr(text)}")
except Exception as e:
    print(f"✗ Error: {e}")
