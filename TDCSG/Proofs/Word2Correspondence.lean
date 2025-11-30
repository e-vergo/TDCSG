/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Proofs.AlgebraicIdentities
import TDCSG.Proofs.RotationFormulas
import TDCSG.Proofs.SegmentGeometry

/-!
# Word 2 Correspondence for GG(5,5)

Proves that word2 produces the correct displacement on segment points.

## Main Results

- `word2_produces_displacement1`: word2 maps segment points by displacement1

## TODO

Complete the cross-disk bounds proof for word2 intermediate points.
-/

namespace TDCSG.CompoundSymmetry.GG5

open Complex Real TDCSG.Definitions

/-- Word 2 action on segment points: translates by displacement1.

word2 = A⁻¹B⁻¹A⁻¹B⁻¹B⁻¹ produces the correct IET translation for interval 1.
Interval 1 corresponds to x ∈ [length1, length1 + length2), equivalently c ∈ [(1-√5)/2, 2-√5].

The proof tracks each rotation through the 5 generators (clockwise convention: A⁻¹ = A⁴ uses ζ₅):
- A⁻¹ uses ζ₅ rotation about -1 (net effect of A⁴, since A uses ζ₅⁴)
- B⁻¹ uses ζ₅ rotation about 1 (net effect of B⁴, since B uses ζ₅⁴)

word2 = [Generator.Ainv, Generator.Binv, Generator.Ainv, Generator.Binv, Generator.Binv]
     = [A⁻¹, B⁻¹, A⁻¹, B⁻¹, B⁻¹] applied left-to-right -/
lemma word2_produces_displacement1 (x : ℝ) (hx : x ∈ Set.Ico 0 1)
    (hx_lo : length1 ≤ x) (hx_hi : x < length1 + length2) :
    applyWord r_crit word2 (segmentPoint x) =
    segmentPoint (x + displacement1) := by
  -- This proof requires cross-disk bounds that depend on E = ζ₅^4 - ζ₅^3 (clockwise convention)
  -- The intermediate rotation points z1-z5 must stay in the appropriate disks
  -- The algebraic identity word2_algebraic_identity provides the translation formula
  sorry

end TDCSG.CompoundSymmetry.GG5
