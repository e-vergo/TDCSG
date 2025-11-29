#!/usr/bin/env python3
"""
Refined verification for Phase 4: understanding the rotation direction change.

Key question: What exactly needs to change when we switch from counterclockwise
(zeta5) to clockwise (zeta5^4) for the forward rotation?
"""

import numpy as np

# Fifth root of unity
zeta5 = np.exp(2j * np.pi / 5)

# Golden ratio constants
phi = (1 + np.sqrt(5)) / 2
psi = 1 / phi

# E vector (the segment direction)
E = zeta5 - zeta5**2

print("=== The core issue ===")
print()
print("Current algebraic identity for word1 (AABAB):")
print("  Uses: step1 = -1 + zeta5 * (z + 1)  for A")
print("  Produces: z + 2*F where F = 1 - zeta5 + zeta5^2 - zeta5^3")
print()
print("With clockwise convention:")
print("  Uses: step1 = -1 + zeta5^4 * (z + 1)  for A")
print("  The algebra will produce a DIFFERENT result")
print()

# What does word1 (AABAB) produce with clockwise A?
def trace_word1_ccw(z):
    """Trace AABAB with counterclockwise"""
    z1 = -1 + zeta5 * (z + 1)
    z2 = -1 + zeta5 * (z1 + 1)
    z3 = 1 + zeta5 * (z2 - 1)
    z4 = -1 + zeta5 * (z3 + 1)
    z5 = 1 + zeta5 * (z4 - 1)
    return z5

def trace_word1_cw(z):
    """Trace AABAB with clockwise (zeta5^4 for forward)"""
    z1 = -1 + zeta5**4 * (z + 1)
    z2 = -1 + zeta5**4 * (z1 + 1)
    z3 = 1 + zeta5**4 * (z2 - 1)
    z4 = -1 + zeta5**4 * (z3 + 1)
    z5 = 1 + zeta5**4 * (z4 - 1)
    return z5

z = 0
result_ccw = trace_word1_ccw(z)
result_cw = trace_word1_cw(z)

print(f"word1 (AABAB) from z=0:")
print(f"  CCW (zeta5): {result_ccw}")
print(f"  CW (zeta5^4): {result_cw}")
print(f"  Note: result_cw = conj(result_ccw)")
print()

# The key insight: conj(result_ccw) = conj(z) + 2*conj(F)
# Since z=0 is real, conj(z) = z
# And conj(F) = conj(1 - zeta5 + zeta5^2 - zeta5^3)
#             = 1 - zeta5^4 + zeta5^3 - zeta5^2  (using conj(zeta5) = zeta5^4)

F = 1 - zeta5 + zeta5**2 - zeta5**3
F_conj = 1 - zeta5**4 + zeta5**3 - zeta5**2

print(f"F = 1 - zeta5 + zeta5^2 - zeta5^3 = {F}")
print(f"conj(F) = 1 - zeta5^4 + zeta5^3 - zeta5^2 = {F_conj}")
print(f"actual conj(F) = {np.conj(F)}")
print(f"F_conj == conj(F)? {np.isclose(F_conj, np.conj(F))}")
print()

# Check: does F_conj / E give the same displacement coefficient?
print(f"F / E = {F / E} (should be psi = {psi})")
print(f"conj(F) / E = {F_conj / E}")
print(f"conj(F) / conj(E) = {F_conj / np.conj(E)}")
print()

# The issue is that E = zeta5 - zeta5^2 has an imaginary part
# So conj(F) is NOT a scalar multiple of E
# In fact: F = psi * E, but conj(F) = psi * conj(E) != psi * E

print("=== Key realization ===")
print("When we conjugate the rotation direction:")
print(f"  F = psi * E, where E = zeta5 - zeta5^2")
print(f"  conj(F) = psi * conj(E) = psi * (zeta5^4 - zeta5^3)")
print()
print("But the segment E'E is parameterized along E, not conj(E)!")
print("So the displacement changes direction in the imaginary component.")
print()

# However, the paper may define things differently. Let me check what
# the paper's conventions are...

print("=== Alternative: redefine E for clockwise ===")
print()
print("If clockwise is 'forward', then perhaps E should be defined as:")
print("  E_new = zeta5^4 - zeta5^3 = conj(E)")
print()
print("Then the algebra would work out the same way.")
print()

E_new = zeta5**4 - zeta5**3
print(f"E = {E}")
print(f"E_new = conj(E) = {E_new}")
print(f"E_new == conj(E)? {np.isclose(E_new, np.conj(E))}")
print()

# The segment endpoints are E' = -E and E = E
# In complex plane: endpoints at -E and +E
# If we redefine E -> conj(E), the segment becomes conjugated

print("=== What the paper likely does ===")
print()
print("Looking at the plan again:")
print("  Current: A(z) = -1 + zeta5 * (z + 1)   -- counterclockwise")
print("  Target:  A(z) = -1 + zeta5^4 * (z + 1) -- clockwise")
print()
print("The segment E'E stays the same (it's geometrically fixed).")
print("The words stay the same (they're topological/combinatorial).")
print("The algebraic PROOFS need to use zeta5^4 where they used zeta5.")
print()
print("But the displacement formulas should remain the same, since")
print("the IET is defined in terms of the segment geometry, not the")
print("rotation direction convention.")
print()

# Let me verify: if we use the opposite words, do we get the same result?
def trace_word1_equiv_cw(z):
    """Trace A^-1 A^-1 B^-1 A^-1 B^-1 with CW convention (zeta5 for inverse)"""
    z1 = -1 + zeta5 * (z + 1)  # A^-1 in CW uses zeta5
    z2 = -1 + zeta5 * (z1 + 1)  # A^-1
    z3 = 1 + zeta5 * (z2 - 1)   # B^-1
    z4 = -1 + zeta5 * (z3 + 1)  # A^-1
    z5 = 1 + zeta5 * (z4 - 1)   # B^-1
    return z5

z = 0
result_equiv = trace_word1_equiv_cw(z)
print(f"word1_equiv = A^-1 A^-1 B^-1 A^-1 B^-1 with CW (zeta5 for inverse):")
print(f"  Result: {result_equiv}")
print(f"  Same as CCW word1? {np.isclose(result_equiv, result_ccw)}")
print()

print("=== CONCLUSION ===")
print()
print("To switch to clockwise rotation:")
print()
print("1. Change genA/genB to use zeta5^4 for forward rotation")
print("2. applyGen for Ainv/Binv needs to compose 4 forward rotations")
print("   Since (zeta5^4)^4 = zeta5^16 = zeta5, this gives zeta5 for inverse")
print("3. The algebraic identity proofs need to be updated:")
print("   - word1: currently uses zeta5 for A, will need zeta5^4")
print("   - word2: currently uses zeta5^4 for A^-1, will need zeta5")
print("   - word3: mixed, update accordingly")
print()
print("4. The proofs should still work because the algebraic identities")
print("   are invariant under the automorphism zeta5 <-> zeta5^4")
print("   (complex conjugation), but the specific lemmas need rewriting.")
print()
print("5. The word DEFINITIONS stay the same:")
print("   word1 = [A, A, B, A, B]")
print("   word2 = [A^-1, B^-1, A^-1, B^-1, B^-1]")
print("   word3 = [A^-1, B^-1, A^-1, B, A, B]")
print()
print("6. The displacement values remain mathematically the same")
print("   (translations by E multiples), but the algebraic expressions")
print("   in the proofs will look different.")
print()

# Final verification: check that word2 (which currently uses A^-1 = zeta5^4)
# will work correctly when A^-1 uses zeta5

def trace_word2_ccw(z):
    """Current word2: A^-1 B^-1 A^-1 B^-1 B^-1 with zeta5^4 for inverse"""
    z1 = -1 + zeta5**4 * (z + 1)  # A^-1
    z2 = 1 + zeta5**4 * (z1 - 1)   # B^-1
    z3 = -1 + zeta5**4 * (z2 + 1)  # A^-1
    z4 = 1 + zeta5**4 * (z3 - 1)   # B^-1
    z5 = 1 + zeta5**4 * (z4 - 1)   # B^-1
    return z5

def trace_word2_cw(z):
    """New word2: A^-1 B^-1 A^-1 B^-1 B^-1 with zeta5 for inverse"""
    z1 = -1 + zeta5 * (z + 1)  # A^-1 now uses zeta5
    z2 = 1 + zeta5 * (z1 - 1)   # B^-1
    z3 = -1 + zeta5 * (z2 + 1)  # A^-1
    z4 = 1 + zeta5 * (z3 - 1)   # B^-1
    z5 = 1 + zeta5 * (z4 - 1)   # B^-1
    return z5

z = 0
r2_ccw = trace_word2_ccw(z)
r2_cw = trace_word2_cw(z)

print("Checking word2 (A^-1 B^-1 A^-1 B^-1 B^-1):")
print(f"  CCW (zeta5^4 for inverse): {r2_ccw}")
print(f"  CW  (zeta5 for inverse):   {r2_cw}")
print(f"  Expected displacement: {2 * psi * E}")
print(f"  CCW matches expected? {np.isclose(r2_ccw, 2 * psi * E)}")
print(f"  CW matches expected?  {np.isclose(r2_cw, 2 * psi * E)}")
print()

# Now check: what displacement does word2_cw actually produce?
print(f"word2_cw produces displacement: {r2_cw}")
print(f"This is: {r2_cw / E} * E")
print()

# Hmm, word2_cw produces conj(result) not the same result
# So word2 in CW produces displacement 2*psi*conj(E), not 2*psi*E

print("=== FINAL INSIGHT ===")
print()
print("The algebraic proofs show that:")
print("  - word1 (AABAB with zeta5) produces translation by 2*psi*E")
print("  - word2 (A^-1 B^-1 A^-1 B^-1 B^-1 with zeta5^4) produces translation by 2*psi*E")
print()
print("If we switch to clockwise:")
print("  - word1 (AABAB with zeta5^4) produces translation by 2*psi*conj(E)")
print("  - word2 (A^-1 B^-1 A^-1 B^-1 B^-1 with zeta5) produces translation by 2*psi*conj(E)")
print()
print("The segment E'E in the complex plane has endpoints at -E and +E.")
print("Translation by conj(E) is NOT along the segment!")
print()
print("THEREFORE: We must ALSO change how E is defined, or change the words,")
print("or we need to understand that the 'displacement' interpretation changes.")
print()

# Actually, let me re-read the problem...
# The segment is in the disk intersection. Its endpoints are specific complex numbers.
# E' and E are defined as zeta5^2 - zeta5 and zeta5 - zeta5^2 respectively
# (or something like that). Let me check the actual definitions.

print("=== Checking E definition ===")
E_def = zeta5 - zeta5**2
E_prime = -E_def  # = zeta5^2 - zeta5

print(f"E = zeta5 - zeta5^2 = {E_def}")
print(f"E' = -E = {E_prime}")
print()

# The segment from E' to E is parameterized as E' + t*(E - E') = E' + 2t*E
# for t in [0, 1]

# When we translate along E, we move in the direction of E (has positive imag part)
# When we translate along conj(E), we move in the conjugate direction (negative imag part)

# In the geometry of the disk intersection, both are valid translations
# that keep points within the lens-shaped region.

print("=== Geometric interpretation ===")
print()
print("The segment E'E lies along the direction of E in the complex plane.")
print("E has a positive imaginary part (pointing 'up').")
print()
print("If we define forward rotation as clockwise (zeta5^4):")
print("  - Translations will be along conj(E) direction (pointing 'down')")
print("  - The IET displacements will be negative of what they were")
print("  - But since we're also changing the words, it should balance out")
print()

# OK I think I understand now. The key is:
# 1. The words stay the same
# 2. The genA/genB change to use zeta5^4
# 3. The algebraic proofs need to show the NEW algebraic identity
# 4. The displacement will be conjugated, but since E appears explicitly
#    in the displacement formula, it still works

# Let me verify the key algebraic identity with the new convention

print("=== Key algebraic identity verification ===")
print()

# With CCW: word1 produces z + 2*(1 - zeta5 + zeta5^2 - zeta5^3)
#                        = z + 2*psi*(zeta5 - zeta5^2)
#                        = z + 2*psi*E

# With CW: word1 produces z + 2*(1 - zeta5^4 + zeta5^3 - zeta5^2)
#                       = z + 2*psi*(zeta5^4 - zeta5^3)
#                       = z + 2*psi*conj(E)

# So the CW version produces a translation in the conj(E) direction
# not the E direction.

# But wait - maybe the paper uses a different definition of E?
# Let me check if zeta5^4 - zeta5^3 = -(zeta5 - zeta5^2)

print(f"zeta5^4 - zeta5^3 = {zeta5**4 - zeta5**3}")
print(f"-(zeta5 - zeta5^2) = {-(zeta5 - zeta5**2)}")
print(f"Equal? {np.isclose(zeta5**4 - zeta5**3, -(zeta5 - zeta5**2))}")
print()

# They're not equal, they're conjugates of each other
# zeta5^4 - zeta5^3 = conj(zeta5) - conj(zeta5^2) = conj(zeta5 - zeta5^2)

print(f"conj(zeta5 - zeta5^2) = {np.conj(zeta5 - zeta5**2)}")
print(f"Equal to zeta5^4 - zeta5^3? {np.isclose(np.conj(zeta5 - zeta5**2), zeta5**4 - zeta5**3)}")
print()

print("=== RESOLUTION ===")
print()
print("The paper likely defines things so that the algebra works out cleanly.")
print("Since we're just changing rotation convention, and the proofs already")
print("use zeta5^4 for inverse rotations, we need to:")
print()
print("1. In GroupAction.lean: Change genA/genB to use -2pi/5 instead of 2pi/5")
print("   This means using angle -2*pi/5 in rotateAboutC")
print()
print("2. In WordCorrespondence proofs: Swap zeta5 <-> zeta5^4 in the algebraic")
print("   identities. The proofs will have the same structure but with swapped")
print("   powers.")
print()
print("3. The word definitions stay THE SAME because the 'meaning' of A and A^-1")
print("   is defined by the generator semantics, not the algebraic representation.")
print()
print("4. Crucially: word1_algebraic_identity currently shows")
print("   [using zeta5 for forward] produces 2*(1 - zeta5 + zeta5^2 - zeta5^3)")
print("   After the change, it needs to show")
print("   [using zeta5^4 for forward] produces 2*(1 - zeta5^4 + zeta5^3 - zeta5^2)")
print()
print("5. Both expressions equal 2*psi*(respective E definition), so the")
print("   displacement coefficients are the same, just the direction changes.")
print()
print("6. Since E is defined as zeta5 - zeta5^2 (fixed), and the IET is defined")
print("   in terms of real-valued positions on the segment, the change in complex")
print("   direction should not affect the IET behavior - it's all about the")
print("   scalar displacement along the segment.")
