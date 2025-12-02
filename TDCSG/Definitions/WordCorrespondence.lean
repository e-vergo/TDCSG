/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TDCSG.Definitions.Core

/-!
# Word Correspondence Definitions for GG(5,5)

This file contains definitions for group words that implement IET steps.

## Main Definitions

- `word1`, `word2`, `word3`: Group words corresponding to IET intervals

Word encoding: (false, true) = A, (false, false) = A^{-1}, (true, true) = B, (true, false) = B^{-1}
Note: applyWord uses foldl, so words are applied left-to-right.
-/

namespace TDCSG.CompoundSymmetry.GG5

open TDCSG.Definitions
open Generator

/-! ### Group words corresponding to IET intervals

The IET on segment E'E is induced by three group words, each producing the correct
translation for its interval. The key algebraic fact is that applying [A,A,B,A,B]
to any point on segment E'E produces translation by 2F = 2ψE, where F = ψE and
ψ = (√5-1)/2 is the positive golden conjugate.

- word1: a²bab = AABAB produces translation 2ψE (displacement ψ for interval 0)
- word2: a²bab = AABAB produces translation 2ψE (displacement ψ for interval 1)
- word3: a⁻¹b⁻¹a⁻¹bab = A⁻¹B⁻¹A⁻¹BAB produces translation -2ψ²E (displacement -ψ² for interval 2)
-/

/-- Word 1: a²bab = AABAB (for interval 0: [0, length1))
    This word produces translation by 2F = 2ψE where ψ = (√5-1)/2.
    Algebraically: (ζ₅ + ζ₅⁴)(ζ₅ - ζ₅²) = 1 - ζ₅ + ζ₅² - ζ₅³ = F. -/
def word1 : Word := [.A, .A, .B, .A, .B]

/-- Word 2: a⁻¹b⁻¹a⁻¹b⁻¹b⁻¹ = A⁻¹B⁻¹A⁻¹B⁻¹B⁻¹ (for interval 1: [length1, length1 + length2))
    This word produces translation by 2F = 2ψE where ψ = (√5-1)/2.

    Unlike word1 (AABAB) which works for interval 0, interval 1 requires a different
    word because AABAB's intermediate points leave the disk intersection for
    c ∈ [(1-√5)/2, 2-√5]. The word A⁻¹B⁻¹A⁻¹B⁻¹B⁻¹ keeps all intermediate points
    within the appropriate disks while producing the same displacement 2ψE.

    The algebraic derivation:
    Starting from z₀ = c•E, applying A⁻¹B⁻¹A⁻¹B⁻¹B⁻¹:
    z₁ = -1 + ζ₅⁴(z₀ + 1)
    z₂ = 1 + ζ₅⁴(z₁ - 1)
    z₃ = -1 + ζ₅⁴(z₂ + 1)
    z₄ = 1 + ζ₅⁴(z₃ - 1)
    z₅ = 1 + ζ₅⁴(z₄ - 1)
    The composition gives z₅ = z₀ + 2ψE. -/
def word2 : Word := [.Ainv, .Binv, .Ainv, .Binv, .Binv]

/-- Word 3: a⁻¹b⁻¹a⁻¹bab = A⁻¹B⁻¹A⁻¹BAB (for interval 2: [length1 + length2, 1))
    This word produces translation by -2ψ²E = 2·displacement2·E where ψ² = 1/(1+φ).

    The algebraic derivation:
    Starting from z₀, applying A⁻¹B⁻¹A⁻¹BAB gives z₆ = z₀ + (2 - 4ζ₅ + 4ζ₅² - 2ζ₅³).

    Key identity using √5 = 2(ζ₅ + ζ₅⁴) + 1:
    (√5-3)·ζ₅ = 2 - 2ζ₅ + 2ζ₅²
    (√5-3)·ζ₅² = 2ζ₅ + 2ζ₅³ - 2ζ₅²
    So (√5-3)·(ζ₅ - ζ₅²) = 2 - 4ζ₅ + 4ζ₅² - 2ζ₅³

    Since -2ψ² = √5 - 3, we have:
    2 - 4ζ₅ + 4ζ₅² - 2ζ₅³ = -2ψ²·(ζ₅ - ζ₅²) = -2ψ²·E = 2·displacement2·E ✓

    Note: The original word ABAB⁻¹A⁻¹B⁻¹ produced translation 2 - 2ζ₅² + 4ζ₅³ - 4ζ₅⁴
    which equals 6 + 4ζ₅ + 2ζ₅² + 8ζ₅³ (using cyclotomic). This is NOT a scalar multiple
    of E = ζ₅ - ζ₅² and thus does not preserve segment membership. -/
def word3 : Word := [.Ainv, .Binv, .Ainv, .B, .A, .B]

end TDCSG.CompoundSymmetry.GG5
