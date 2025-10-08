"""Prompt formatting utilities for BFS-Prover model."""


def format_bfs_prover_prompt(proof_state: str) -> str:
    """
    Format a Lean proof state into BFS-Prover's expected input format.

    BFS-Prover-V2 was trained on Lean 4 tactic mode proofs.
    The model expects the proof state followed by a tactic generation marker.

    Args:
        proof_state: Raw Lean goal state with hypotheses and goals

    Returns:
        Formatted prompt string for the model
    """
    # Clean and normalize the proof state
    state = proof_state.strip()

    # BFS-Prover format
    prompt = f"""[PROOF STATE]
{state}

[TACTIC]
"""
    return prompt


def extract_tactic(model_output: str) -> str:
    """
    Extract and clean a tactic from model output.

    Args:
        model_output: Raw text from model generation

    Returns:
        Cleaned tactic string
    """
    # Remove common artifacts
    tactic = model_output.strip()

    # Remove markers if present
    tactic = tactic.replace("[TACTIC]", "").strip()
    tactic = tactic.replace("[PROOF STATE]", "").strip()

    # Take only first line (tactics should be single line)
    if "\n" in tactic:
        tactic = tactic.split("\n")[0].strip()

    return tactic
