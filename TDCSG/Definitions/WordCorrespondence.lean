/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core
import TDCSG.Definitions.IET

/-!
# Word Correspondence Definitions for GG(5,5)

This file contains definitions for group words that implement IET steps.

## Main Definitions

- `word1`, `word2`, `word3`: Group words corresponding to IET intervals
- `IET_word`: Selects the appropriate word based on which interval x falls in
- `wordForIterate`: Concatenated word for n iterations of the IET
- `wordForIterate'`: Simplified version for ProofOfMainTheorem
-/

namespace TDCSG.CompoundSymmetry.GG5

open TDCSG.Definitions _root_.CompoundSymmetry.GG5

/-! ### Group words corresponding to IET intervals

The IET on segment E'E is induced by three group words:
- word1: a^{-2}b^{-1}a^{-1}b^{-1} maps E'F' -> GF (interval 0)
- word2: abab^2 maps F'G' -> FE (interval 1)
- word3: abab^{-1}a^{-1}b^{-1} maps G'E -> E'G (interval 2)

Word encoding: (false, true) = A, (false, false) = A^{-1}, (true, true) = B, (true, false) = B^{-1}
Note: applyWord uses foldl, so words are applied left-to-right.
-/

/-- Word 1: a^{-2}b^{-1}a^{-1}b^{-1} (for interval 0: [0, length1)) -/
def word1 : Word :=
  [(false, false), (false, false), (true, false), (false, false), (true, false)]

/-- Word 2: abab^2 (for interval 1: [length1, length1 + length2)) -/
def word2 : Word :=
  [(false, true), (true, true), (false, true), (true, true), (true, true)]

/-- Word 3: abab^{-1}a^{-1}b^{-1} (for interval 2: [length1 + length2, 1)) -/
def word3 : Word :=
  [(false, true), (true, true), (false, true), (true, false), (false, false), (true, false)]

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

end TDCSG.CompoundSymmetry.GG5
