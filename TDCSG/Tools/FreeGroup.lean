import TDCSG.Theory.GroupAction

/-!
# Free Group Computational Tools

This file provides computational tools for working with free groups and word representations.
Consolidated from TwoDisk/FreeGroupTools.lean as part of Layer 3 (Tools).

## Main functions

* `wordToList`: Convert word to list of generators
* `applyWord`: Apply a word to a point
* `computeWord`: Compute specific group element words
-/

open TwoDiskSystem

namespace FreeGroupTools

variable (sys : TwoDiskSystem)

/-- Convert a word representation to a list of generator applications -/
noncomputable def wordToList (word : List (Fin 2 × Bool)) : List (ℂ → ℂ) :=
  word.map (fun gb => applyGenerator sys gb.1 gb.2)

/-- Apply a word directly to a point -/
noncomputable def applyWord (word : List (Fin 2 × Bool)) (z : ℂ) : ℂ :=
  word.foldl (fun acc gb => applyGenerator sys gb.1 gb.2 acc) z

/-- Apply word and track intermediate steps -/
noncomputable def applyWordSteps (word : List (Fin 2 × Bool)) (z : ℂ) : List ℂ :=
  word.scanl (fun acc gb => applyGenerator sys gb.1 gb.2 acc) z

/-- Compute the word for a⁻²b⁻¹a⁻¹b⁻¹ -/
def word_case1 : List (Fin 2 × Bool) :=
  [(0, true), (0, true), (1, true), (0, true), (1, true)]

/-- Compute the word for abab² -/
def word_case2 : List (Fin 2 × Bool) :=
  [(0, false), (1, false), (0, false), (1, false), (1, false)]

/-- Compute the word for abab⁻¹a⁻¹b⁻¹ -/
def word_case3 : List (Fin 2 × Bool) :=
  [(0, false), (1, false), (0, false), (1, true), (0, true), (1, true)]

/-- Helper: Check if a word represents a translation -/
def isTranslation (word : List (Fin 2 × Bool)) (z w : ℂ) : Prop :=
  applyWord sys word w - applyWord sys word z = w - z

/-- Helper: Compute the translation vector of a word -/
noncomputable def translationVector (word : List (Fin 2 × Bool)) (z : ℂ) : ℂ :=
  applyWord sys word z - z

end FreeGroupTools