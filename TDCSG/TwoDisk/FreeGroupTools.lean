import TDCSG.TwoDisk.GroupAction

/-!
# FreeGroup Word Computation Tools

This file provides computational tools for working with FreeGroup words,
making it easier to compute and simplify group element representations.
-/

open TwoDiskSystem

/-- Compute the word representation of a⁻¹b explicitly -/
def word_a_inv_b : List (Fin 2 × Bool) := [(0, true), (1, false)]

/-- Compute the word representation of a⁻²b⁻¹a⁻¹b⁻¹ for Theorem 2 Case 1 -/
def word_case1 : List (Fin 2 × Bool) :=
  [(0, true), (0, true), (1, true), (0, true), (1, true)]

/-- Compute the word representation of abab² for Theorem 2 Case 2 -/
def word_case2 : List (Fin 2 × Bool) :=
  [(0, false), (1, false), (0, false), (1, false), (1, false)]

/-- Compute the word representation of abab⁻¹a⁻¹b⁻¹ for Theorem 2 Case 3 -/
def word_case3 : List (Fin 2 × Bool) :=
  [(0, false), (1, false), (0, false), (1, true), (0, true), (1, true)]

/-- Simplify a word by canceling adjacent inverse pairs -/
def simplifyWord : List (Fin 2 × Bool) → List (Fin 2 × Bool)
  | [] => []
  | [x] => [x]
  | (g₁, b₁) :: (g₂, b₂) :: rest =>
    if g₁ = g₂ ∧ b₁ ≠ b₂ then
      simplifyWord rest  -- Cancel aa⁻¹ or a⁻¹a
    else
      (g₁, b₁) :: simplifyWord ((g₂, b₂) :: rest)

/-- Apply a word to a point step by step, returning intermediate results -/
noncomputable def applyWordSteps (sys : TwoDiskSystem) (word : List (Fin 2 × Bool)) (z : ℂ) : List ℂ :=
  word.scanl (fun acc gb => applyGenerator sys gb.1 gb.2 acc) z

/-- Compute the final result of applying a word -/
noncomputable def applyWord (sys : TwoDiskSystem) (word : List (Fin 2 × Bool)) (z : ℂ) : ℂ :=
  word.foldl (fun acc gb => applyGenerator sys gb.1 gb.2 acc) z

/-- Check if a word represents a translation on the intersection -/
def isTranslationOnIntersection (sys : TwoDiskSystem) (word : List (Fin 2 × Bool)) : Prop :=
  ∃ v : ℂ, ∀ z ∈ sys.diskIntersection, applyWord sys word z = z + v

/-- Lemma: The explicit word for a⁻¹b matches what we expect -/
lemma word_a_inv_b_correct (sys : TwoDiskSystem) :
    applyWord sys word_a_inv_b =
    fun z => applyGenerator sys 1 false (applyGenerator sys 0 true z) := by
  unfold applyWord word_a_inv_b
  ext z
  simp [List.foldl]