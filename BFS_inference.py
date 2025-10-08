#!/usr/bin/env python3
"""
BFS-Prover-V2-7B Inference Script
Optimized for Mac with Apple Silicon (MPS) or CPU
Generates Lean4 proof tactics from mathematical states
"""

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
import time
from pathlib import Path

class BFSProver:
    def __init__(self, model_path="./models/BFS-Prover-V2-7B", device=None):
        """
        Initialize the BFS-Prover model
        
        Args:
            model_path: Path to the model directory
            device: Device to use ('mps', 'cuda', 'cpu', or None for auto-detect)
        """
        print("="*70)
        print("Initializing BFS-Prover-V2-7B")
        print("="*70)
        
        # Auto-detect device if not specified
        if device is None:
            if torch.backends.mps.is_available():
                device = "mps"
                print("✓ Apple Silicon detected - using MPS acceleration")
            elif torch.cuda.is_available():
                device = "cuda"
                print("✓ CUDA detected - using GPU acceleration")
            else:
                device = "cpu"
                print("✓ Using CPU (no GPU acceleration available)")
        
        self.device = device
        print(f"Device: {device}")
        
        # Load tokenizer
        print("\nLoading tokenizer...")
        self.tokenizer = AutoTokenizer.from_pretrained(model_path)
        
        # Load model
        print("Loading model (this may take a minute)...")
        start_time = time.time()
        
        # For Mac/MPS, load in fp16 to save memory
        if device == "mps":
            self.model = AutoModelForCausalLM.from_pretrained(
                model_path,
                torch_dtype=torch.float16,
                low_cpu_mem_usage=True
            ).to(device)
        else:
            self.model = AutoModelForCausalLM.from_pretrained(
                model_path,
                low_cpu_mem_usage=True
            ).to(device)
        
        load_time = time.time() - start_time
        
        print(f"✓ Model loaded successfully in {load_time:.2f}s")
        print(f"✓ Model size: ~{self._get_model_size_gb():.2f} GB")
        print("="*70 + "\n")
    
    def _get_model_size_gb(self):
        """Calculate model size in GB"""
        param_size = sum(p.nelement() * p.element_size() for p in self.model.parameters())
        buffer_size = sum(b.nelement() * b.element_size() for b in self.model.buffers())
        return (param_size + buffer_size) / (1024**3)
    
    def generate_tactic(self, state, max_new_tokens=128, temperature=0.7, top_p=0.95):
        """
        Generate a Lean4 tactic for the given mathematical state
        
        Args:
            state: Lean4 state string
            max_new_tokens: Maximum tokens to generate
            temperature: Sampling temperature (lower = more deterministic)
            top_p: Nucleus sampling parameter
            
        Returns:
            Generated tactic string
        """
        # Format input with special separator
        separator = ":::"
        prompt = state.strip() + separator
        
        print("Input state:")
        print("-" * 70)
        print(state.strip())
        print("-" * 70)
        
        # Tokenize
        inputs = self.tokenizer(prompt, return_tensors="pt").to(self.device)
        
        # Generate
        print("\nGenerating tactic...")
        start_time = time.time()
        
        with torch.no_grad():
            outputs = self.model.generate(
                **inputs,
                max_new_tokens=max_new_tokens,
                temperature=temperature,
                top_p=top_p,
                do_sample=True,
                pad_token_id=self.tokenizer.eos_token_id
            )
        
        generation_time = time.time() - start_time
        
        # Decode and extract tactic
        full_output = self.tokenizer.decode(outputs[0], skip_special_tokens=True)
        
        # The output should be: state ::: tactic
        # We want to extract just the tactic part
        if separator in full_output:
            tactic = full_output.split(separator, 1)[1].strip()
        else:
            tactic = full_output.strip()
        
        print(f"Generated in {generation_time:.2f}s")
        print("\nGenerated tactic:")
        print("-" * 70)
        print(tactic)
        print("-" * 70)
        
        return tactic

# Example Lean4 states for testing
EXAMPLE_STATES = {
    "imo_1964_p2": """a b c : ℝ
h₀ : 0 < a ∧ 0 < b ∧ 0 < c
h₁ : c < a + b
h₂ : b < a + c
h₃ : a < b + c
⊢ a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c""",
    
    "simple_inequality": """x y : ℝ
hx : 0 ≤ x
hy : 0 ≤ y
⊢ x ^ 2 + y ^ 2 ≥ 2 * x * y""",
    
    "basic_algebra": """n : ℕ
h : n > 0
⊢ n + 1 > 0"""
}

def main():
    """Main function with interactive examples"""
    import argparse
    
    parser = argparse.ArgumentParser(description="Generate Lean4 proof tactics")
    parser.add_argument(
        "--model-path",
        type=str,
        default="./models/BFS-Prover-V2-7B",
        help="Path to the model directory"
    )
    parser.add_argument(
        "--example",
        type=str,
        choices=list(EXAMPLE_STATES.keys()) + ["custom"],
        default=None,
        help="Run a predefined example"
    )
    parser.add_argument(
        "--state",
        type=str,
        default=None,
        help="Custom Lean4 state to prove"
    )
    parser.add_argument(
        "--interactive",
        action="store_true",
        help="Run in interactive mode"
    )
    parser.add_argument(
        "--temperature",
        type=float,
        default=0.7,
        help="Sampling temperature (default: 0.7)"
    )
    parser.add_argument(
        "--max-tokens",
        type=int,
        default=128,
        help="Maximum tokens to generate (default: 128)"
    )
    
    args = parser.parse_args()
    
    # Initialize model
    prover = BFSProver(model_path=args.model_path)
    
    # Run example
    if args.example:
        if args.example == "custom":
            if not args.state:
                print("Error: --state required when using --example custom")
                return
            state = args.state
        else:
            state = EXAMPLE_STATES[args.example]
            print(f"Running example: {args.example}\n")
        
        prover.generate_tactic(
            state,
            max_new_tokens=args.max_tokens,
            temperature=args.temperature
        )
    
    # Interactive mode
    elif args.interactive:
        print("\n" + "="*70)
        print("Interactive Mode - Enter Lean4 states to generate tactics")
        print("Type 'quit' or 'exit' to stop")
        print("Type 'examples' to see available examples")
        print("="*70 + "\n")
        
        while True:
            print("\nEnter Lean4 state (or command):")
            state_lines = []
            
            # Multi-line input
            while True:
                line = input()
                if line.lower() in ['quit', 'exit']:
                    print("Goodbye!")
                    return
                if line.lower() == 'examples':
                    print("\nAvailable examples:")
                    for name in EXAMPLE_STATES.keys():
                        print(f"  - {name}")
                    print("\nTo use an example, type: example:<name>")
                    break
                if line.startswith('example:'):
                    example_name = line.split(':', 1)[1].strip()
                    if example_name in EXAMPLE_STATES:
                        state_lines = [EXAMPLE_STATES[example_name]]
                    else:
                        print(f"Unknown example: {example_name}")
                    break
                if line == "":
                    if state_lines:
                        break
                    else:
                        continue
                state_lines.append(line)
            
            if state_lines:
                state = "\n".join(state_lines)
                print()
                prover.generate_tactic(
                    state,
                    max_new_tokens=args.max_tokens,
                    temperature=args.temperature
                )
    
    # Default: run all examples
    else:
        print("Running all examples...\n")
        for name, state in EXAMPLE_STATES.items():
            print(f"\n{'='*70}")
            print(f"Example: {name}")
            print(f"{'='*70}\n")
            
            prover.generate_tactic(
                state,
                max_new_tokens=args.max_tokens,
                temperature=args.temperature
            )
            
            print("\n")

if __name__ == "__main__":
    main()