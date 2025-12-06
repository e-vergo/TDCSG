#!/usr/bin/env python3
"""
Verify 3-cycle IET structure for N=10.

We have discovered:
- Left→Middle at depth 6
- Right→Middle at depth 6
- Swap words at depth 4
- Middle reflection at depth 5

This script verifies we can construct a TRUE 3-cycle with infinite orbits.
"""

import numpy as np
from typing import List, Tuple, Dict

class Segment:
    def __init__(self, start, end):
        self.start = np.array(start, dtype=float)
        self.end = np.array(end, dtype=float)
        self._length = np.linalg.norm(self.end - self.start)
        self._direction = (self.end - self.start) / self._length

    def to_t(self, point):
        return np.dot(point - self.start, self._direction) / self._length

    def from_t(self, t):
        return self.start + t * self._length * self._direction

    def perp_distance(self, point):
        t = self.to_t(point)
        closest = self.from_t(t)
        return np.linalg.norm(point - closest)


class GGGroup:
    def __init__(self, n):
        self.n = n
        self.theta = -2 * np.pi / n
        self.center_a = np.array([-1., 0.])
        self.center_b = np.array([1., 0.])

    def rotate(self, point, center, power):
        angle = power * self.theta
        c, s = np.cos(angle), np.sin(angle)
        d = point - center
        return center + np.array([c*d[0] - s*d[1], s*d[0] + c*d[1]])

    def apply_word(self, point, word):
        result = point.copy()
        for gen, power in word:
            center = self.center_a if gen == 'a' else self.center_b
            result = self.rotate(result, center, power)
        return result

    def word_to_string(self, word):
        parts = []
        for gen, power in word:
            if power == 1: parts.append(gen)
            elif power == -1: parts.append(f'{gen}⁻¹')
            else:
                sup = ''.join(['⁰¹²³⁴⁵⁶⁷⁸⁹'[int(d)] if d.isdigit() else '⁻' for d in str(power)])
                parts.append(f'{gen}{sup}')
        return ''.join(parts)


def get_segment(n):
    zeta = np.exp(2j * np.pi / n)
    E = zeta - zeta**2
    return Segment([-E.real, -E.imag], [E.real, E.imag])


def verify_word_mapping(segment, group, word, t_samples, expected_target):
    """Verify a word maps points from one region to another."""
    valid = []
    for t in t_samples:
        point = segment.from_t(t)
        mapped = group.apply_word(point, word)
        perp = segment.perp_distance(mapped)
        ret_t = segment.to_t(mapped)
        if perp < 0.01 and expected_target[0] <= ret_t <= expected_target[1]:
            valid.append((t, ret_t))
    return valid


def test_orbit(segment, group, words_by_interval, start_t, max_steps=500):
    """
    Test orbit using interval-specific words.

    words_by_interval: dict mapping interval bounds to word
        e.g., {(0, 0.382): word1, (0.382, 0.618): word2, (0.618, 1): word3}
    """
    t = start_t
    positions = [t]

    for step in range(max_steps):
        point = segment.from_t(t)

        # Find which interval we're in
        word = None
        for (low, high), w in words_by_interval.items():
            if low <= t <= high:
                word = w
                break

        if word is None:
            return step, positions, "no_word"

        mapped = group.apply_word(point, word)
        perp = segment.perp_distance(mapped)
        new_t = segment.to_t(mapped)

        if perp > 0.01:
            return step, positions, "off_segment"

        if not 0 <= new_t <= 1:
            return step, positions, "out_of_bounds"

        # Check for period
        if step > 2 and abs(new_t - start_t) < 0.0001:
            return step + 1, positions, "periodic"

        t = new_t
        positions.append(t)

    return max_steps, positions, "long"


def main():
    n = 10
    segment = get_segment(n)
    group = GGGroup(n)

    print("=" * 70)
    print("3-CYCLE IET VERIFICATION FOR N=10")
    print("=" * 70)

    phi = (1 + np.sqrt(5)) / 2
    phi_inv = 1 / phi  # ≈ 0.618
    two_minus_phi = 2 - phi  # ≈ 0.382

    print(f"\nInterval boundaries (golden ratio):")
    print(f"  2-φ = {two_minus_phi:.6f}")
    print(f"  1/φ = {phi_inv:.6f}")

    # Define intervals
    I1 = (0, two_minus_phi)      # [0, 0.382]
    I2 = (two_minus_phi, phi_inv)  # [0.382, 0.618]
    I3 = (phi_inv, 1)           # [0.618, 1]

    print(f"\nInterval partition:")
    print(f"  I1 = [{I1[0]:.3f}, {I1[1]:.3f}] (left)")
    print(f"  I2 = [{I2[0]:.3f}, {I2[1]:.3f}] (middle)")
    print(f"  I3 = [{I3[0]:.3f}, {I3[1]:.3f}] (right)")

    # Known words
    # Swap: I1 ↔ I3
    swap_1_to_3 = [('b', -1), ('a', -1), ('b', 1), ('a', 1)]  # b⁻¹a⁻¹ba
    swap_3_to_1 = [('a', -1), ('b', -1), ('a', 1), ('b', 1)]  # a⁻¹b⁻¹ab

    # Middle reflection: I2 → I2
    reflect_middle = [('a', -3), ('b', -3), ('a', -3), ('b', -3), ('a', -3)]

    # Left → Middle (depth 6, from search)
    left_to_middle = [('a', -4), ('b', -2), ('a', -5), ('b', -2), ('a', -4), ('b', -3)]

    # Right → Middle (depth 6, from search)
    right_to_middle = [('a', -3), ('b', -5), ('a', -1), ('b', -5), ('a', -2), ('b', 1)]

    print("\n" + "=" * 70)
    print("VERIFYING MAPPINGS")
    print("=" * 70)

    # Verify I1 → I3 (swap)
    print(f"\nSwap I1→I3: {group.word_to_string(swap_1_to_3)}")
    t_left = np.linspace(0.05, 0.35, 10)
    valid = verify_word_mapping(segment, group, swap_1_to_3, t_left, I3)
    print(f"  Valid mappings: {len(valid)}")
    for f, t in valid[:3]:
        print(f"    {f:.3f} → {t:.3f}")

    # Verify I3 → I1 (swap)
    print(f"\nSwap I3→I1: {group.word_to_string(swap_3_to_1)}")
    t_right = np.linspace(0.65, 0.95, 10)
    valid = verify_word_mapping(segment, group, swap_3_to_1, t_right, I1)
    print(f"  Valid mappings: {len(valid)}")
    for f, t in valid[:3]:
        print(f"    {f:.3f} → {t:.3f}")

    # Verify I1 → I2 (left to middle)
    print(f"\nI1→I2: {group.word_to_string(left_to_middle)}")
    valid = verify_word_mapping(segment, group, left_to_middle, t_left, I2)
    print(f"  Valid mappings: {len(valid)}")
    for f, t in valid[:3]:
        print(f"    {f:.3f} → {t:.3f}")

    # Verify I3 → I2 (right to middle)
    print(f"\nI3→I2: {group.word_to_string(right_to_middle)}")
    valid = verify_word_mapping(segment, group, right_to_middle, t_right, I2)
    print(f"  Valid mappings: {len(valid)}")
    for f, t in valid[:3]:
        print(f"    {f:.3f} → {t:.3f}")

    # For 3-cycle, we need I2 → I3 or I2 → I1
    # Let's search for a middle→right word
    print("\n" + "=" * 70)
    print("SEARCHING FOR MIDDLE→EDGE WORDS")
    print("=" * 70)

    from itertools import product

    def generate_words(max_depth, max_power=5):
        words = []
        for depth in range(1, max_depth + 1):
            for powers in product(range(-max_power, max_power + 1), repeat=depth):
                if 0 in powers:
                    continue
                word = []
                for i, p in enumerate(powers):
                    gen = 'a' if i % 2 == 0 else 'b'
                    word.append((gen, p))
                words.append(word)
                # Also try starting with 'b'
                word_b = []
                for i, p in enumerate(powers):
                    gen = 'b' if i % 2 == 0 else 'a'
                    word_b.append((gen, p))
                words.append(word_b)
        return words

    print("Generating depth 1-6 words...")
    words = generate_words(6)
    print(f"Testing {len(words)} words")

    t_middle = np.linspace(0.40, 0.58, 10)

    middle_to_right = []
    middle_to_left = []

    for word in words:
        # Check middle → right
        valid = verify_word_mapping(segment, group, word, t_middle, I3)
        if len(valid) >= 3:
            middle_to_right.append({
                'word': word,
                'word_str': group.word_to_string(word),
                'depth': len(word),
                'valid': valid
            })

        # Check middle → left
        valid = verify_word_mapping(segment, group, word, t_middle, I1)
        if len(valid) >= 3:
            middle_to_left.append({
                'word': word,
                'word_str': group.word_to_string(word),
                'depth': len(word),
                'valid': valid
            })

    if middle_to_right:
        middle_to_right.sort(key=lambda x: x['depth'])
        print(f"\nMiddle→Right: {len(middle_to_right)} words found!")
        for m in middle_to_right[:5]:
            print(f"  {m['word_str']} (d{m['depth']})")
            for f, t in m['valid'][:2]:
                print(f"    {f:.3f} → {t:.3f}")

    if middle_to_left:
        middle_to_left.sort(key=lambda x: x['depth'])
        print(f"\nMiddle→Left: {len(middle_to_left)} words found!")
        for m in middle_to_left[:5]:
            print(f"  {m['word_str']} (d{m['depth']})")
            for f, t in m['valid'][:2]:
                print(f"    {f:.3f} → {t:.3f}")

    # Now construct and test 3-cycles
    print("\n" + "=" * 70)
    print("TESTING 3-CYCLE CONFIGURATIONS")
    print("=" * 70)

    if middle_to_right:
        best_m2r = middle_to_right[0]

        # 3-cycle: I1 → I2 → I3 → I1
        cycle_words = {
            I1: left_to_middle,   # I1 → I2
            I2: best_m2r['word'], # I2 → I3
            I3: swap_3_to_1       # I3 → I1
        }

        print(f"\nCycle A: I1 → I2 → I3 → I1")
        print(f"  I1→I2: {group.word_to_string(left_to_middle)}")
        print(f"  I2→I3: {best_m2r['word_str']}")
        print(f"  I3→I1: {group.word_to_string(swap_3_to_1)}")

        # Test orbits
        print("\n  Testing orbits:")
        for start in [0.1, 0.2, 0.3, 0.45, 0.55, 0.7, 0.8, 0.9]:
            length, positions, status = test_orbit(segment, group, cycle_words, start, max_steps=500)
            print(f"    t={start:.2f}: length={length}, status={status}")
            if status == "long":
                print(f"      First 10 positions: {[f'{p:.3f}' for p in positions[:10]]}")

    if middle_to_left:
        best_m2l = middle_to_left[0]

        # Alternative 3-cycle: I3 → I2 → I1 → I3
        cycle_words = {
            I3: right_to_middle,  # I3 → I2
            I2: best_m2l['word'], # I2 → I1
            I1: swap_1_to_3       # I1 → I3
        }

        print(f"\nCycle B: I3 → I2 → I1 → I3")
        print(f"  I3→I2: {group.word_to_string(right_to_middle)}")
        print(f"  I2→I1: {best_m2l['word_str']}")
        print(f"  I1→I3: {group.word_to_string(swap_1_to_3)}")

        # Test orbits
        print("\n  Testing orbits:")
        for start in [0.1, 0.2, 0.3, 0.45, 0.55, 0.7, 0.8, 0.9]:
            length, positions, status = test_orbit(segment, group, cycle_words, start, max_steps=500)
            print(f"    t={start:.2f}: length={length}, status={status}")
            if status == "long":
                print(f"      First 10 positions: {[f'{p:.3f}' for p in positions[:10]]}")


if __name__ == '__main__':
    main()
