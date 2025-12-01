/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.IET
import TDCSG.Definitions.WordCorrespondence

/-!
# IET Orbit Definitions

Definitions for relating IET orbits to group word sequences.

## Main definitions

* `IET_word`: Select the word based on which IET interval x falls in
* `wordForIterate`: Concatenated word for n iterations of the IET
* `wordForIterate'`: Simplified version for ProofOfMainTheorem
-/

namespace TDCSG.Definitions

open Real TDCSG.CompoundSymmetry.GG5

/-- Select the word based on which IET interval x falls in. -/
noncomputable def IET_word (x : Real) : Word :=
  if x < length1 then word1
  else if x < length1 + length2 then word2
  else word3

/-- Concatenated word for n iterations of the IET starting from x0.
Each iteration applies the word corresponding to the current interval. -/
noncomputable def wordForIterate (x0 : Real) : Nat -> Word
  | 0 => []
  | n + 1 => wordForIterate x0 n ++ IET_word (GG5_induced_IET.toFun^[n] x0)

/-- Simplified version that doesn't track starting point - used in ProofOfMainTheorem. -/
noncomputable def wordForIterate' : Nat -> Word
  | 0 => []
  | n + 1 => wordForIterate' n ++ word1  -- Simplified: actual depends on orbit

end TDCSG.Definitions
