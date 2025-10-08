"""Model loading and inference for BFS-Prover GGUF model."""

from typing import List, Optional
import time
from pathlib import Path
from llama_cpp import Llama
import psutil

from .prompts import format_bfs_prover_prompt, extract_tactic


class BFSProverModel:
    """Manages BFS-Prover GGUF model loading and inference."""

    def __init__(
        self,
        model_path: str | Path,
        n_ctx: int = 4096,
        n_gpu_layers: int = -1,  # -1 = all layers on GPU
        verbose: bool = False,
    ):
        self.model_path = Path(model_path)
        self.n_ctx = n_ctx
        self.n_gpu_layers = n_gpu_layers
        self.verbose = verbose

        self.model: Optional[Llama] = None
        self.load_time: Optional[float] = None
        self.start_time = time.time()

    def load(self) -> None:
        """Load the GGUF model into memory."""
        if not self.model_path.exists():
            raise FileNotFoundError(f"Model not found: {self.model_path}")

        start = time.time()
        self.model = Llama(
            model_path=str(self.model_path),
            n_ctx=self.n_ctx,
            n_gpu_layers=self.n_gpu_layers,
            verbose=self.verbose,
            n_threads=4,  # Adjust based on CPU cores
        )
        self.load_time = time.time() - start

    def generate_tactics(
        self,
        proof_state: str,
        num_suggestions: int = 5,
        temperature: float = 0.7,
        max_tokens: int = 128,
    ) -> List[str]:
        """Generate tactic suggestions for a proof state."""
        if self.model is None:
            raise RuntimeError("Model not loaded. Call load() first.")

        # Format prompt for BFS-Prover
        prompt = format_bfs_prover_prompt(proof_state)

        tactics = []
        for _ in range(num_suggestions):
            output = self.model(
                prompt,
                max_tokens=max_tokens,
                temperature=temperature,
                stop=["<|endoftext|>", "\n\n", "[PROOF STATE]"],
                echo=False,
            )

            raw_tactic = output["choices"][0]["text"]
            tactic = extract_tactic(raw_tactic)
            if tactic:
                tactics.append(tactic)

        return tactics

    def get_info(self) -> dict:
        """Get model and system information."""
        process = psutil.Process()
        memory_info = process.memory_info()

        return {
            "model_name": self.model_path.name,
            "model_size_gb": round(self.model_path.stat().st_size / 1e9, 2)
            if self.model_path.exists()
            else 0,
            "model_loaded": self.model is not None,
            "context_length": self.n_ctx,
            "memory_usage_gb": round(memory_info.rss / 1e9, 2),
            "backend": "metal" if self.n_gpu_layers != 0 else "cpu",
            "uptime_seconds": round(time.time() - self.start_time, 2),
        }

    def reload(self, new_model_path: Optional[Path] = None) -> float:
        """Reload the model, optionally from a new path."""
        if new_model_path:
            self.model_path = new_model_path

        # Unload existing model
        if self.model is not None:
            del self.model
            self.model = None

        # Reload
        self.load()
        return self.load_time
