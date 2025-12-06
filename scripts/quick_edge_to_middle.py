#!/usr/bin/env python3
"""
Quick search for edge-to-middle mappings at depth 6.
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


def generate_words(n, max_depth):
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
    max_depth = 6  # Faster search

    segment = get_segment(n)
    group = GGGroup(n)

    print(f"Quick edge→middle search for GG({n},{n})")
    print("=" * 70)

    # Edge and middle regions
    left_ts = np.linspace(0.05, 0.35, 15)
    right_ts = np.linspace(0.65, 0.95, 15)
    middle_range = (0.40, 0.60)

    print(f"Generating words up to depth {max_depth}...")
    words = generate_words(n, max_depth)
    print(f"Generated {len(words)} words")

    left_to_middle = []
    right_to_middle = []

    for word in words:
        # Check left → middle
        valid_left = []
        for t in left_ts:
            point = segment.from_t(t)
            mapped = group.apply_word(point, word)
            perp = segment.perp_distance(mapped)
            ret_t = segment.to_t(mapped)
            if perp < 0.01 and middle_range[0] <= ret_t <= middle_range[1]:
                valid_left.append((t, ret_t))

        if len(valid_left) >= 3:
            left_to_middle.append({
                'word': word,
                'word_str': group.word_to_string(word),
                'depth': len(word),
                'mappings': valid_left
            })

        # Check right → middle
        valid_right = []
        for t in right_ts:
            point = segment.from_t(t)
            mapped = group.apply_word(point, word)
            perp = segment.perp_distance(mapped)
            ret_t = segment.to_t(mapped)
            if perp < 0.01 and middle_range[0] <= ret_t <= middle_range[1]:
                valid_right.append((t, ret_t))

        if len(valid_right) >= 3:
            right_to_middle.append({
                'word': word,
                'word_str': group.word_to_string(word),
                'depth': len(word),
                'mappings': valid_right
            })

    print()
    print("=" * 70)
    print("RESULTS")
    print("=" * 70)

    if left_to_middle:
        left_to_middle.sort(key=lambda x: x['depth'])
        print(f"\nLEFT → MIDDLE: Found {len(left_to_middle)} words")
        for m in left_to_middle[:10]:
            print(f"  {m['word_str']} (d{m['depth']}): {len(m['mappings'])} points")
            for (f, t) in m['mappings'][:3]:
                print(f"    {f:.3f} → {t:.3f}")
    else:
        print("\nLEFT → MIDDLE: NONE FOUND at depth 6")

    if right_to_middle:
        right_to_middle.sort(key=lambda x: x['depth'])
        print(f"\nRIGHT → MIDDLE: Found {len(right_to_middle)} words")
        for m in right_to_middle[:10]:
            print(f"  {m['word_str']} (d{m['depth']}): {len(m['mappings'])} points")
            for (f, t) in m['mappings'][:3]:
                print(f"    {f:.3f} → {t:.3f}")
    else:
        print("\nRIGHT → MIDDLE: NONE FOUND at depth 6")

    # Verify known words
    print("\n" + "=" * 70)
    print("Verifying known mappings:")
    print("=" * 70)

    # Middle reflection word
    reflect_word = [('a', -3), ('b', -3), ('a', -3), ('b', -3), ('a', -3)]
    print(f"\nReflection word: {group.word_to_string(reflect_word)}")
    middle_ts = np.linspace(0.4, 0.6, 20)
    for t in middle_ts[::4]:
        point = segment.from_t(t)
        mapped = group.apply_word(point, reflect_word)
        perp = segment.perp_distance(mapped)
        ret_t = segment.to_t(mapped)
        print(f"  {t:.3f} → {ret_t:.3f} (perp={perp:.4f})")

    # Swap words
    swap_fwd = [('b', -1), ('a', -1), ('b', 1), ('a', 1)]
    swap_back = [('a', -1), ('b', -1), ('a', 1), ('b', 1)]

    print(f"\nSwap forward: {group.word_to_string(swap_fwd)}")
    for t in [0.1, 0.2, 0.3]:
        point = segment.from_t(t)
        mapped = group.apply_word(point, swap_fwd)
        perp = segment.perp_distance(mapped)
        ret_t = segment.to_t(mapped)
        print(f"  {t:.3f} → {ret_t:.3f} (perp={perp:.4f})")

    print(f"\nSwap back: {group.word_to_string(swap_back)}")
    for t in [0.7, 0.8, 0.9]:
        point = segment.from_t(t)
        mapped = group.apply_word(point, swap_back)
        perp = segment.perp_distance(mapped)
        ret_t = segment.to_t(mapped)
        print(f"  {t:.3f} → {ret_t:.3f} (perp={perp:.4f})")


if __name__ == '__main__':
    main()
