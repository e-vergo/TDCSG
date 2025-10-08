"""Type definitions for BFS-Prover MCP server."""

from typing import List, Optional
from pydantic import BaseModel, Field


class TacticSuggestion(BaseModel):
    """A single tactic suggestion with metadata."""

    tactic: str
    confidence: Optional[float] = None
    tokens: Optional[int] = None


class TacticGenerationResult(BaseModel):
    """Result of tactic generation."""

    tactics: List[str]
    generation_time_ms: float
    model_name: str
    temperature_used: float
    num_generated: int


class ModelInfo(BaseModel):
    """Information about the loaded model."""

    model_name: str
    model_size_gb: float
    model_loaded: bool
    context_length: int
    memory_usage_gb: float
    backend: str
    uptime_seconds: float


class ReloadResult(BaseModel):
    """Result of model reload operation."""

    success: bool
    message: str
    load_time_seconds: float
