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

/-- Word corresponding to the first IET interval: A A B A B.

This word maps the first subinterval [E', F'] of the segment E'E back onto the
subinterval [G, F]. In the paper's notation (Section "Geometric Constructions"),
this corresponds to case (1) of the piecewise translation.

The word A^2 B A B represents a composition of rotations:
- B: rotate by -2pi/5 about the right disk center (1,0)
- A: rotate by -2pi/5 about the left disk center (-1,0)
- B: rotate by -2pi/5 about the right disk center
- A^2: rotate by -4pi/5 about the left disk center

The key property is that on the interval [E', F'], the total rotation cancels
and the action is a pure translation by |F - F'|. This translation distance
is incommensurate with the segment length |E - E'|, creating the infinite
orbit structure. -/
def word1 : Word := [.A, .A, .B, .A, .B]

/-- Word corresponding to the second IET interval: A^{-1} B^{-1} A^{-1} B^{-1} B^{-1}.

This word maps the second subinterval [F', G'] of the segment E'E back onto the
subinterval [F, E]. In the paper's notation (Section "Geometric Constructions"),
this corresponds to case (2) of the piecewise translation.

The word A^{-1} B^{-1} A^{-1} B^{-2} is the inverse composition:
- B^{-2}: rotate by +4pi/5 about the right disk center (1,0)
- A^{-1}: rotate by +2pi/5 about the left disk center (-1,0)
- B^{-1}: rotate by +2pi/5 about the right disk center
- A^{-1}: rotate by +2pi/5 about the left disk center

On [F', G'], the cumulative effect is a translation of magnitude |F - F'|,
the same distance as word1 but in a direction that maps this middle interval
onto [F, E]. The golden ratio relationship |E - E'|/|F - F'| = phi ensures
these translations are never eventually periodic. -/
def word2 : Word := [.Ainv, .Binv, .Ainv, .Binv, .Binv]

/-- Word corresponding to the third IET interval: A^{-1} B^{-1} A^{-1} B A B.

This word maps the third subinterval [G', E] of the segment E'E back onto the
subinterval [E', G]. In the paper's notation (Section "Geometric Constructions"),
this corresponds to case (3) of the piecewise translation.

The word A^{-1} B^{-1} A^{-1} B A B is a mixed composition:
- B: rotate by -2pi/5 about the right disk center (1,0)
- A: rotate by -2pi/5 about the left disk center (-1,0)
- B: rotate by -2pi/5 about the right disk center
- A^{-1}: rotate by +2pi/5 about the left disk center
- B^{-1}: rotate by +2pi/5 about the right disk center
- A^{-1}: rotate by +2pi/5 about the left disk center

On [G', E], this produces a translation of magnitude |E - G|, which differs
from |F - F'|. The incommensurability |E - E'|/|F - F'| = phi (golden ratio)
is the fundamental reason GG5 has infinite orbits at the critical radius
r = sqrt(3 + phi). -/
def word3 : Word := [.Ainv, .Binv, .Ainv, .B, .A, .B]

end TDCSG.CompoundSymmetry.GG5
