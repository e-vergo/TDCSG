/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import TDCSG.Definitions.Core

/-!
# Word Correspondence

This file defines the three special words that correspond to the three intervals
in the interval exchange transformation induced by GG5.

## Main definitions

- `word1`: The word A A B A B corresponding to the first interval
- `word2`: The word A⁻¹ B⁻¹ A⁻¹ B⁻¹ B⁻¹ corresponding to the second interval
- `word3`: The word A⁻¹ B⁻¹ A⁻¹ B A B corresponding to the third interval

## Implementation notes

These words represent the group elements that map points in each interval
of [0,1] back to the segment E'E in the complex plane. The correspondence
between IET dynamics on [0,1] and group action on ℂ is central to the proof.

## References

* [arXiv:2302.12950v1](https://arxiv.org/abs/2302.12950)
-/

namespace TDCSG.CompoundSymmetry.GG5

open TDCSG.Definitions
open Generator

/-- Word corresponding to the first IET interval: A A B A B. -/
def word1 : Word := [.A, .A, .B, .A, .B]

/-- Word corresponding to the second IET interval: A⁻¹ B⁻¹ A⁻¹ B⁻¹ B⁻¹. -/
def word2 : Word := [.Ainv, .Binv, .Ainv, .Binv, .Binv]

/-- Word corresponding to the third IET interval: A⁻¹ B⁻¹ A⁻¹ B A B. -/
def word3 : Word := [.Ainv, .Binv, .Ainv, .B, .A, .B]

end TDCSG.CompoundSymmetry.GG5
