#!/usr/bin/env python3
"""
Fast test of known words for N=10 3-cycle IET.

Uses words discovered from previous searches without regenerating all words.
"""

import numpy as np

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


def test_word_mapping(segment, group, word, t_values):
    """Test how a word maps a set of t values."""
    results = []
    for t in t_values:
        point = segment.from_t(t)
        mapped = group.apply_word(point, word)
        perp = segment.perp_distance(mapped)
        ret_t = segment.to_t(mapped)
        results.append((t, ret_t, perp))
    return results


def main():
    n = 10
    segment = get_segment(n)
    group = GGGroup(n)

    print("=" * 70)
    print("N=10 KNOWN WORD VERIFICATION")
    print("=" * 70)

    phi = (1 + np.sqrt(5)) / 2
    phi_inv = 1 / phi  # ≈ 0.618
    two_minus_phi = 2 - phi  # ≈ 0.382

    print(f"\nGolden ratio boundaries: 2-φ = {two_minus_phi:.6f}, 1/φ = {phi_inv:.6f}")

    # Define known words from our search
    words = {
        # Depth 4 swaps
        "swap_L_to_R": [('b', -1), ('a', -1), ('b', 1), ('a', 1)],   # b⁻¹a⁻¹ba
        "swap_R_to_L": [('a', -1), ('b', -1), ('a', 1), ('b', 1)],   # a⁻¹b⁻¹ab

        # Depth 5 middle reflection
        "middle_reflect": [('a', -3), ('b', -3), ('a', -3), ('b', -3), ('a', -3)],

        # Depth 6 left→middle (from search: a⁻⁴b⁻²a⁻⁵b⁻²a⁻⁴b⁻³)
        "L_to_M_v1": [('a', -4), ('b', -2), ('a', -5), ('b', -2), ('a', -4), ('b', -3)],
        "L_to_M_v2": [('a', -4), ('b', -5), ('a', -2), ('b', -2), ('a', -5), ('b', 3)],

        # Depth 6 right→middle (from search: a⁻³b⁻⁵a⁻¹b⁻⁵a⁻²b)
        "R_to_M_v1": [('a', -3), ('b', -5), ('a', -1), ('b', -5), ('a', -2), ('b', 1)],
        "R_to_M_v2": [('a', -3), ('b', -1), ('a', -5), ('b', -2), ('a', -2), ('b', -2)],
    }

    # Test regions
    left_ts = np.linspace(0.05, 0.35, 10)
    middle_ts = np.linspace(0.40, 0.58, 10)
    right_ts = np.linspace(0.65, 0.95, 10)

    print("\n" + "=" * 70)
    print("TESTING KNOWN WORDS")
    print("=" * 70)

    for name, word in words.items():
        print(f"\n{name}: {group.word_to_string(word)}")

        if 'L_to' in name or 'swap_L' in name:
            test_ts = left_ts
        elif 'R_to' in name or 'swap_R' in name:
            test_ts = right_ts
        else:
            test_ts = middle_ts

        results = test_word_mapping(segment, group, word, test_ts)
        valid = [(t, rt, p) for t, rt, p in results if p < 0.01 and 0 <= rt <= 1]

        if valid:
            print(f"  Valid mappings: {len(valid)}/{len(results)}")
            for t, rt, p in valid[:5]:
                print(f"    {t:.3f} → {rt:.3f} (perp={p:.6f})")
        else:
            print(f"  No valid mappings found")

    # Now search for middle→edge words
    print("\n" + "=" * 70)
    print("SEARCHING FOR MIDDLE→EDGE WORDS (depth 4-6)")
    print("=" * 70)

    # Generate only depth 4-6 alternating words
    middle_to_right_words = []
    middle_to_left_words = []

    for depth in range(4, 7):
        print(f"\nSearching depth {depth}...")
        found_m2r = 0
        found_m2l = 0

        # Generate all alternating words of this depth
        from itertools import product
        max_power = 5

        for start in ['a', 'b']:
            for powers in product(range(-max_power, max_power + 1), repeat=depth):
                if 0 in powers:
                    continue

                word = []
                for i, p in enumerate(powers):
                    if start == 'a':
                        gen = 'a' if i % 2 == 0 else 'b'
                    else:
                        gen = 'b' if i % 2 == 0 else 'a'
                    word.append((gen, p))

                # Test on middle points
                valid_right = 0
                valid_left = 0

                for t in [0.42, 0.50, 0.56]:
                    point = segment.from_t(t)
                    mapped = group.apply_word(point, word)
                    perp = segment.perp_distance(mapped)
                    ret_t = segment.to_t(mapped)

                    if perp < 0.01:
                        if phi_inv <= ret_t <= 1:  # Maps to right
                            valid_right += 1
                        elif 0 <= ret_t <= two_minus_phi:  # Maps to left
                            valid_left += 1

                if valid_right >= 2:
                    middle_to_right_words.append({
                        'word': word,
                        'word_str': group.word_to_string(word),
                        'depth': depth
                    })
                    found_m2r += 1

                if valid_left >= 2:
                    middle_to_left_words.append({
                        'word': word,
                        'word_str': group.word_to_string(word),
                        'depth': depth
                    })
                    found_m2l += 1

        print(f"  Found {found_m2r} middle→right, {found_m2l} middle→left words")

    print("\n" + "=" * 70)
    print("MIDDLE→EDGE WORDS FOUND")
    print("=" * 70)

    if middle_to_right_words:
        print(f"\nMiddle→Right: {len(middle_to_right_words)} words")
        for m in middle_to_right_words[:10]:
            print(f"  {m['word_str']} (depth {m['depth']})")
            # Test mapping
            results = test_word_mapping(segment, group, m['word'], middle_ts)
            for t, rt, p in results[:3]:
                if p < 0.01 and phi_inv <= rt <= 1:
                    print(f"    {t:.3f} → {rt:.3f}")

    if middle_to_left_words:
        print(f"\nMiddle→Left: {len(middle_to_left_words)} words")
        for m in middle_to_left_words[:10]:
            print(f"  {m['word_str']} (depth {m['depth']})")
            results = test_word_mapping(segment, group, m['word'], middle_ts)
            for t, rt, p in results[:3]:
                if p < 0.01 and 0 <= rt <= two_minus_phi:
                    print(f"    {t:.3f} → {rt:.3f}")

    # If we found middle→edge words, test 3-cycles
    if middle_to_right_words or middle_to_left_words:
        print("\n" + "=" * 70)
        print("TESTING 3-CYCLE CONFIGURATIONS")
        print("=" * 70)

        def test_orbit(word_map, start_t, max_steps=1000):
            """Test orbit length."""
            t = start_t
            for step in range(max_steps):
                point = segment.from_t(t)

                # Find which interval
                if t < two_minus_phi:
                    word = word_map.get('I1')
                elif t < phi_inv:
                    word = word_map.get('I2')
                else:
                    word = word_map.get('I3')

                if word is None:
                    return step, "no_word"

                mapped = group.apply_word(point, word)
                perp = segment.perp_distance(mapped)
                new_t = segment.to_t(mapped)

                if perp > 0.01 or new_t < 0 or new_t > 1:
                    return step, "off_segment"

                if step > 2 and abs(new_t - start_t) < 0.0001:
                    return step + 1, "periodic"

                t = new_t

            return max_steps, "long"

        # Test cycle: I1 → I2 → I3 → I1
        if middle_to_right_words:
            best_m2r = middle_to_right_words[0]['word']
            word_map = {
                'I1': words['L_to_M_v1'],  # I1 → I2
                'I2': best_m2r,             # I2 → I3
                'I3': words['swap_R_to_L']  # I3 → I1
            }

            print(f"\nCycle A: I1 → I2 → I3 → I1")
            print(f"  I1→I2: {group.word_to_string(words['L_to_M_v1'])}")
            print(f"  I2→I3: {group.word_to_string(best_m2r)}")
            print(f"  I3→I1: {group.word_to_string(words['swap_R_to_L'])}")

            print("\n  Orbit tests:")
            for start in [0.1, 0.2, 0.3, 0.45, 0.5, 0.55, 0.7, 0.8, 0.9]:
                length, status = test_orbit(word_map, start)
                print(f"    t={start:.2f}: length={length}, status={status}")

        # Test cycle: I3 → I2 → I1 → I3
        if middle_to_left_words:
            best_m2l = middle_to_left_words[0]['word']
            word_map = {
                'I3': words['R_to_M_v1'],  # I3 → I2
                'I2': best_m2l,             # I2 → I1
                'I1': words['swap_L_to_R']  # I1 → I3
            }

            print(f"\nCycle B: I3 → I2 → I1 → I3")
            print(f"  I3→I2: {group.word_to_string(words['R_to_M_v1'])}")
            print(f"  I2→I1: {group.word_to_string(best_m2l)}")
            print(f"  I1→I3: {group.word_to_string(words['swap_L_to_R'])}")

            print("\n  Orbit tests:")
            for start in [0.1, 0.2, 0.3, 0.45, 0.5, 0.55, 0.7, 0.8, 0.9]:
                length, status = test_orbit(word_map, start)
                print(f"    t={start:.2f}: length={length}, status={status}")


if __name__ == '__main__':
    main()
