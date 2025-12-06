#!/usr/bin/env python3
"""
Search specifically for words that map EDGES to the MIDDLE interval.

For a true 3-cycle in N=10, we need:
- I1 [0, 0.38] → I2 [0.38, 0.62]  OR
- I3 [0.62, 1] → I2 [0.38, 0.62]

This is the missing piece for cyclic IET.
"""

import numpy as np
from typing import List, Tuple


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


def generate_all_words(n, max_depth):
    """Generate all alternating words up to max_depth."""
    max_power = n // 2
    words = []

    def extend(word, depth):
        if depth == 0:
            return
        last_gen = word[-1][0]
        next_gen = 'b' if last_gen == 'a' else 'a'
        for power in range(-max_power, max_power + 1):
            if power == 0:
                continue
            new_word = word + [(next_gen, power)]
            words.append(new_word)
            extend(new_word, depth - 1)

    for start_gen in ['a', 'b']:
        for start_power in range(-max_power, max_power + 1):
            if start_power == 0:
                continue
            word = [(start_gen, start_power)]
            words.append(word)
            extend(word, max_depth - 1)

    return words


def main():
    n = 10
    max_depth = 8

    segment = get_segment(n)
    group = GGGroup(n)

    print(f"Searching for EDGE → MIDDLE mappings in GG({n},{n})")
    print("=" * 70)

    # Edge regions
    left_ts = np.linspace(0.05, 0.35, 30)   # I1 = [0, 0.38]
    right_ts = np.linspace(0.65, 0.95, 30)  # I3 = [0.62, 1]

    # Middle region
    middle_range = (0.40, 0.60)  # I2 = [0.38, 0.62]

    print(f"Looking for words that map:")
    print(f"  Left  [0.05, 0.35] → Middle [{middle_range[0]:.2f}, {middle_range[1]:.2f}]")
    print(f"  Right [0.65, 0.95] → Middle [{middle_range[0]:.2f}, {middle_range[1]:.2f}]")
    print()

    print(f"Generating words up to depth {max_depth}...")
    words = generate_all_words(n, max_depth)
    print(f"Generated {len(words)} words")
    print()

    left_to_middle = []
    right_to_middle = []

    print("Analyzing words...")
    for i, word in enumerate(words):
        if i % 100000 == 0 and i > 0:
            print(f"  Progress: {i}/{len(words)}")

        # Check left → middle
        valid_from_left = []
        valid_to = []
        for t in left_ts:
            point = segment.from_t(t)
            mapped = group.apply_word(point, word)
            perp = segment.perp_distance(mapped)
            ret_t = segment.to_t(mapped)

            if perp < 0.01 and middle_range[0] <= ret_t <= middle_range[1]:
                valid_from_left.append(t)
                valid_to.append(ret_t)

        if len(valid_from_left) >= 5:
            left_to_middle.append({
                'word': word,
                'word_str': group.word_to_string(word),
                'depth': len(word),
                'from_center': np.mean(valid_from_left),
                'to_center': np.mean(valid_to),
                'samples': len(valid_from_left)
            })

        # Check right → middle
        valid_from_right = []
        valid_to = []
        for t in right_ts:
            point = segment.from_t(t)
            mapped = group.apply_word(point, word)
            perp = segment.perp_distance(mapped)
            ret_t = segment.to_t(mapped)

            if perp < 0.01 and middle_range[0] <= ret_t <= middle_range[1]:
                valid_from_right.append(t)
                valid_to.append(ret_t)

        if len(valid_from_right) >= 5:
            right_to_middle.append({
                'word': word,
                'word_str': group.word_to_string(word),
                'depth': len(word),
                'from_center': np.mean(valid_from_right),
                'to_center': np.mean(valid_to),
                'samples': len(valid_from_right)
            })

    print()
    print("=" * 70)
    print("RESULTS")
    print("=" * 70)

    if left_to_middle:
        left_to_middle.sort(key=lambda x: x['depth'])
        print(f"\nLEFT → MIDDLE: Found {len(left_to_middle)} words!")
        for m in left_to_middle[:15]:
            print(f"  {m['word_str']} (d{m['depth']}): {m['from_center']:.3f} → {m['to_center']:.3f} ({m['samples']} pts)")
    else:
        print("\nLEFT → MIDDLE: NO WORDS FOUND")
        print("This is why cyclic IET doesn't exist on standard segment!")

    if right_to_middle:
        right_to_middle.sort(key=lambda x: x['depth'])
        print(f"\nRIGHT → MIDDLE: Found {len(right_to_middle)} words!")
        for m in right_to_middle[:15]:
            print(f"  {m['word_str']} (d{m['depth']}): {m['from_center']:.3f} → {m['to_center']:.3f} ({m['samples']} pts)")
    else:
        print("\nRIGHT → MIDDLE: NO WORDS FOUND")
        print("This is why cyclic IET doesn't exist on standard segment!")

    # If we found both, check for 3-cycle potential
    if left_to_middle and right_to_middle:
        print("\n" + "=" * 70)
        print("POTENTIAL 3-CYCLE CONSTRUCTION:")
        print("=" * 70)

        # Best candidates
        l_word = left_to_middle[0]
        r_word = right_to_middle[0]

        print(f"\n3-CYCLE:")
        print(f"  I1 [0, 0.38] → I2 [0.38, 0.62] via {l_word['word_str']}")
        print(f"  I2 [0.38, 0.62] → I3 [0.62, 1] via ??? (use middle→edge words)")
        print(f"  I3 [0.62, 1] → I1 [0, 0.38] via a⁻¹b⁻¹ab")

        print(f"\nOR:")
        print(f"  I1 [0, 0.38] → I3 [0.62, 1] via b⁻¹a⁻¹ba")
        print(f"  I3 [0.62, 1] → I2 [0.38, 0.62] via {r_word['word_str']}")
        print(f"  I2 [0.38, 0.62] → I1 [0, 0.38] via ??? (use middle→edge words)")


if __name__ == '__main__':
    main()
