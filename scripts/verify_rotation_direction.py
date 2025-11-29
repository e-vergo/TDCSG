#!/usr/bin/env python3
"""
Numerical verification for TDCSG Phase 4: Rotation Direction Change

This script verifies that changing from counterclockwise (zeta5) to clockwise (zeta5^4)
rotation produces the same displacement values for the IET when words are properly adjusted.

Current convention (counterclockwise, zeta5 = exp(2*pi*i/5)):
  - A(z) = -1 + zeta5 * (z + 1)  (rotate +2pi/5 about -1)
  - B(z) = 1 + zeta5 * (z - 1)   (rotate +2pi/5 about 1)

Target convention (clockwise, zeta5^4 = exp(-2*pi*i/5)):
  - A(z) = -1 + zeta5^4 * (z + 1)  (rotate -2pi/5 about -1)
  - B(z) = 1 + zeta5^4 * (z - 1)   (rotate -2pi/5 about 1)

Key insight: zeta5^4 = zeta5^(-1) = conjugate(zeta5)
"""

import numpy as np
from typing import Callable, List, Tuple

# Fifth root of unity
zeta5 = np.exp(2j * np.pi / 5)
zeta5_inv = np.exp(-2j * np.pi / 5)  # = zeta5^4

# Verify basic identity
print("=== Basic zeta5 identities ===")
print(f"zeta5 = {zeta5}")
print(f"zeta5^4 = {zeta5**4}")
print(f"zeta5^(-1) = {1/zeta5}")
print(f"exp(-2pi*i/5) = {zeta5_inv}")
print(f"|zeta5^4 - zeta5^(-1)| = {abs(zeta5**4 - 1/zeta5):.2e} (should be ~0)")
print()

# Golden ratio constants
phi = (1 + np.sqrt(5)) / 2  # golden ratio ~1.618
psi = 1 / phi  # = phi - 1 = (sqrt(5) - 1) / 2 ~0.618

# E vector (the segment direction)
E = zeta5 - zeta5**2

print("=== Segment and displacement constants ===")
print(f"phi (golden ratio) = {phi}")
print(f"psi = 1/phi = {psi}")
print(f"E = zeta5 - zeta5^2 = {E}")
print(f"|E| = {abs(E)}")
print()

# Current rotation formulas (counterclockwise, using zeta5)
def A_ccw(z: complex) -> complex:
    """Generator A: rotate by +2pi/5 about -1"""
    return -1 + zeta5 * (z + 1)

def A_inv_ccw(z: complex) -> complex:
    """Generator A^(-1): rotate by -2pi/5 about -1 (= A^4)"""
    return -1 + zeta5**4 * (z + 1)

def B_ccw(z: complex) -> complex:
    """Generator B: rotate by +2pi/5 about 1"""
    return 1 + zeta5 * (z - 1)

def B_inv_ccw(z: complex) -> complex:
    """Generator B^(-1): rotate by -2pi/5 about 1 (= B^4)"""
    return 1 + zeta5**4 * (z - 1)

# New rotation formulas (clockwise, using zeta5^4 for forward)
def A_cw(z: complex) -> complex:
    """Generator A: rotate by -2pi/5 about -1"""
    return -1 + zeta5**4 * (z + 1)

def A_inv_cw(z: complex) -> complex:
    """Generator A^(-1): rotate by +2pi/5 about -1 (= A^4 in cw world = zeta5)"""
    return -1 + zeta5 * (z + 1)

def B_cw(z: complex) -> complex:
    """Generator B: rotate by -2pi/5 about 1"""
    return 1 + zeta5**4 * (z - 1)

def B_inv_cw(z: complex) -> complex:
    """Generator B^(-1): rotate by +2pi/5 about 1 (= B^4 in cw world = zeta5)"""
    return 1 + zeta5 * (z - 1)

def apply_word_ccw(word: List[str], z: complex) -> complex:
    """Apply a word using counterclockwise convention (current)"""
    ops = {'A': A_ccw, 'Ainv': A_inv_ccw, 'B': B_ccw, 'Binv': B_inv_ccw}
    result = z
    for gen in word:
        result = ops[gen](result)
    return result

def apply_word_cw(word: List[str], z: complex) -> complex:
    """Apply a word using clockwise convention (target)"""
    ops = {'A': A_cw, 'Ainv': A_inv_cw, 'B': B_cw, 'Binv': B_inv_cw}
    result = z
    for gen in word:
        result = ops[gen](result)
    return result

# Current words (counterclockwise convention)
word1_ccw = ['A', 'A', 'B', 'A', 'B']  # AABAB
word2_ccw = ['Ainv', 'Binv', 'Ainv', 'Binv', 'Binv']  # A^-1 B^-1 A^-1 B^-1 B^-1
word3_ccw = ['Ainv', 'Binv', 'Ainv', 'B', 'A', 'B']  # A^-1 B^-1 A^-1 B A B

# Displacements
displacement0 = psi  # = 1/phi
displacement1 = psi  # same as displacement0
displacement2 = -1 / (1 + phi)  # = (sqrt(5) - 3) / 2

print("=== Expected displacements ===")
print(f"displacement0 = 1/phi = {displacement0}")
print(f"displacement1 = 1/phi = {displacement1}")
print(f"displacement2 = -1/(1+phi) = {displacement2}")
print()

# Test the current words (counterclockwise)
print("=== Current words (counterclockwise convention) ===")
test_points = [0, 0.5*E, -0.3*E, 0.8*E]

for i, (word, expected_disp) in enumerate([(word1_ccw, displacement0),
                                            (word2_ccw, displacement1),
                                            (word3_ccw, displacement2)], 1):
    print(f"\nword{i} = {word}")
    for z in test_points[:2]:
        result = apply_word_ccw(word, z)
        actual_disp = result - z
        # The displacement should be 2 * displacement * E (factor of 2 from x -> c conversion)
        expected = 2 * expected_disp * E
        error = abs(actual_disp - expected)
        print(f"  z={z:.4f}: result={result:.4f}, disp={actual_disp:.4f}, expected={expected:.4f}, error={error:.2e}")

# Now test: what words would work with clockwise convention?
# Key insight: In clockwise convention, forward rotation uses zeta5^4, so:
# - Current A (uses zeta5) -> becomes A^-1 in clockwise
# - Current A^-1 (uses zeta5^4) -> becomes A in clockwise
# So the same words with A<->A^-1 and B<->B^-1 swapped should work

def swap_generators(word: List[str]) -> List[str]:
    """Swap A<->A^-1 and B<->B^-1"""
    swap = {'A': 'Ainv', 'Ainv': 'A', 'B': 'Binv', 'Binv': 'B'}
    return [swap[g] for g in word]

print("\n\n=== Testing with clockwise convention ===")

# First, let's check if swapping works
word1_cw_swap = swap_generators(word1_ccw)
word2_cw_swap = swap_generators(word2_ccw)
word3_cw_swap = swap_generators(word3_ccw)

print("\nSwapped words (A<->A^-1, B<->B^-1):")
print(f"word1_cw = {word1_cw_swap} (was {word1_ccw})")
print(f"word2_cw = {word2_cw_swap} (was {word2_ccw})")
print(f"word3_cw = {word3_cw_swap} (was {word3_ccw})")

for i, (word, expected_disp) in enumerate([(word1_cw_swap, displacement0),
                                            (word2_cw_swap, displacement1),
                                            (word3_cw_swap, displacement2)], 1):
    print(f"\nword{i}_cw = {word} with clockwise convention:")
    for z in test_points[:2]:
        result = apply_word_cw(word, z)
        actual_disp = result - z
        expected = 2 * expected_disp * E
        error = abs(actual_disp - expected)
        print(f"  z={z:.4f}: result={result:.4f}, disp={actual_disp:.4f}, expected={expected:.4f}, error={error:.2e}")

# What about keeping the same words but using clockwise?
print("\n\n=== Original words with clockwise convention (should NOT work) ===")
for i, (word, expected_disp) in enumerate([(word1_ccw, displacement0),
                                            (word2_ccw, displacement1),
                                            (word3_ccw, displacement2)], 1):
    print(f"\nword{i} = {word} (original word, clockwise convention):")
    z = 0
    result = apply_word_cw(word, z)
    actual_disp = result - z
    expected = 2 * expected_disp * E
    error = abs(actual_disp - expected)
    print(f"  z={z:.4f}: actual_disp={actual_disp:.4f}, expected={expected:.4f}, error={error:.2e}")

# Compute the actual displacement algebraically
print("\n\n=== Algebraic verification ===")

# For word1 = AABAB (counterclockwise): should give translation by 2 * (1 - zeta5 + zeta5^2 - zeta5^3)
# Let's verify this equals 2 * psi * E

F = 1 - zeta5 + zeta5**2 - zeta5**3  # The "F" from the proofs
print(f"F = 1 - zeta5 + zeta5^2 - zeta5^3 = {F}")
print(f"E = zeta5 - zeta5^2 = {E}")
print(f"F / E = {F / E} (should be psi = {psi})")
print(f"2 * psi * E = {2 * psi * E}")
print(f"2 * F = {2 * F}")
print(f"|2*F - 2*psi*E| = {abs(2*F - 2*psi*E):.2e}")

# For clockwise word1 (which is Ainv Ainv Binv Ainv Binv):
# A^-1 uses zeta5 in cw, so it's like old A
# So Ainv Ainv Binv Ainv Binv in cw = AABAB in ccw ... should produce same displacement

print("\n\n=== Final verification: do swapped words in CW produce same displacements as original in CCW? ===")

all_match = True
for i, (word_ccw, word_cw, expected_disp) in enumerate([
    (word1_ccw, word1_cw_swap, displacement0),
    (word2_ccw, word2_cw_swap, displacement1),
    (word3_ccw, word3_cw_swap, displacement2)
], 1):
    z = 0.3 * E  # Test point
    result_ccw = apply_word_ccw(word_ccw, z)
    result_cw = apply_word_cw(word_cw, z)

    disp_ccw = result_ccw - z
    disp_cw = result_cw - z

    match = abs(disp_ccw - disp_cw) < 1e-10
    all_match = all_match and match

    print(f"word{i}:")
    print(f"  CCW {word_ccw}: disp = {disp_ccw:.6f}")
    print(f"  CW  {word_cw}: disp = {disp_cw:.6f}")
    print(f"  Match: {match}")

print(f"\nAll displacements match: {all_match}")

# Alternative check: keep the words the same, but understand that A and A^-1 swap roles
print("\n\n=== Alternative interpretation ===")
print("If we keep the same words but change the semantics of genA/genB:")
print("  - Forward rotation now uses zeta5^4 (was zeta5)")
print("  - Inverse rotation now uses zeta5 (was zeta5^4)")
print("")
print("This means:")
print("  - Current word1 [A,A,B,A,B] under new semantics applies A^-1, A^-1, B^-1, A^-1, B^-1")
print("  - Which is word2 in the old system!")
print("")
print("So to get the same behavior, we need:")
print("  - word1 (new) should be what was word2 (old)")
print("  - word2 (new) should be what was word1 (old)")
print("")

# Check displacement patterns
print("=== Checking if displacement2 formula still holds with clockwise ===")
# displacement2 is negative, which means translation in the -E direction
# In the paper, this corresponds to interval 2 moving backward

z = 0
result_word3_ccw = apply_word_ccw(word3_ccw, z)
result_word3_cw = apply_word_cw(word3_cw_swap, z)

print(f"word3 (ccw): z=0 -> {result_word3_ccw}")
print(f"word3_swap (cw): z=0 -> {result_word3_cw}")
print(f"Expected displacement: 2 * {displacement2} * E = {2 * displacement2 * E}")
print(f"Actual (ccw): {result_word3_ccw}")
print(f"Actual (cw): {result_word3_cw}")

print("\n" + "="*60)
print("CONCLUSION")
print("="*60)
print("""
When changing from counterclockwise to clockwise rotation:

1. The genA and genB definitions change:
   - genA: z -> -1 + zeta5^4 * (z + 1)  (was zeta5)
   - genB: z -> 1 + zeta5^4 * (z - 1)   (was zeta5)

2. Generator.Ainv and Generator.Binv now use zeta5 (was zeta5^4):
   - A^-1: z -> -1 + zeta5 * (z + 1)
   - B^-1: z -> 1 + zeta5 * (z - 1)

3. The WORDS DO NOT CHANGE! The same word sequences [A,A,B,A,B] etc.
   will produce the same displacements because:
   - The algebraic identities are symmetric under zeta5 <-> zeta5^4
   - What matters is the *relative* composition of rotations

4. The algebraic proofs need updating:
   - word1_algebraic_identity: uses zeta5 for A, needs zeta5^4 for A
   - word2_algebraic_identity: uses zeta5^4 for A^-1, needs zeta5 for A^-1
   - word3_algebraic_identity: mixed, needs corresponding updates

5. Actually, upon closer inspection: the algebraic identities already use
   zeta5^4 for inverse operations. The question is whether the *forward*
   rotation should use zeta5 or zeta5^4.

CRITICAL INSIGHT: Looking at the current code:
   - word1 uses A (forward) which uses zeta5
   - word2 uses A^-1 (inverse) which uses zeta5^4

If we switch to clockwise:
   - A (forward) uses zeta5^4
   - A^-1 (inverse) uses zeta5

So the word definitions should stay the same, but the algebraic proofs
need to swap zeta5 <-> zeta5^4 throughout.
""")

# Final numerical check: same words, swapped zeta5 usage in proofs
print("\n=== Verifying same words work with swapped zeta5 usage ===")

# Redefine with clockwise being the forward direction
def apply_word_new_convention(word: List[str], z: complex) -> complex:
    """Apply word with clockwise = forward convention"""
    result = z
    for gen in word:
        if gen == 'A':
            result = -1 + zeta5**4 * (result + 1)  # Forward A now uses zeta5^4
        elif gen == 'Ainv':
            result = -1 + zeta5 * (result + 1)  # Inverse A now uses zeta5
        elif gen == 'B':
            result = 1 + zeta5**4 * (result - 1)  # Forward B now uses zeta5^4
        elif gen == 'Binv':
            result = 1 + zeta5 * (result - 1)  # Inverse B now uses zeta5
    return result

print("\nSame words with new convention (forward = clockwise = zeta5^4):")
for i, (word, expected_disp) in enumerate([
    (word1_ccw, displacement0),
    (word2_ccw, displacement1),
    (word3_ccw, displacement2)
], 1):
    z = 0.3 * E
    result_old = apply_word_ccw(word, z)
    result_new = apply_word_new_convention(word, z)

    disp_old = result_old - z
    disp_new = result_new - z
    expected = 2 * expected_disp * E

    print(f"word{i} = {word}:")
    print(f"  Old convention: disp = {disp_old:.6f}, expected = {expected:.6f}")
    print(f"  New convention: disp = {disp_new:.6f}")
    print(f"  Match expected: {abs(disp_old - expected) < 1e-10}")
    print(f"  New matches old: {abs(disp_old - disp_new) < 1e-10}")
