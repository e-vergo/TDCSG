#!/usr/bin/env python3
"""
Explore what group words do to a single point on the segment.
"""

import numpy as np
from typing import List, Tuple
import argparse


class Segment:
    def __init__(self, start, end):
        self.start = np.array(start)
        self.end = np.array(end)

    @property
    def length(self):
        return np.linalg.norm(self.end - self.start)

    @property
    def direction(self):
        return (self.end - self.start) / self.length

    def to_t(self, point):
        return np.dot(point - self.start, self.direction) / self.length

    def from_t(self, t):
        return self.start + t * self.length * self.direction

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
            if power == 1:
                parts.append(gen)
            elif power == -1:
                parts.append(f"{gen}⁻¹")
            else:
                sup = ''.join(['⁰¹²³⁴⁵⁶⁷⁸⁹'[int(d)] if d.isdigit() else '⁻' for d in str(power)])
                parts.append(f"{gen}{sup}")
        return ''.join(parts)


def get_segment(n):
    zeta = np.exp(2j * np.pi / n)
    E = zeta - zeta**2
    return Segment([-E.real, -E.imag], [E.real, E.imag])


def generate_words(n, max_depth):
    words = []
    max_power = n // 2

    def extend(word, depth):
        if depth == 0:
            return

        last_gen = word[-1][0] if word else None
        next_gens = ['b'] if last_gen == 'a' else (['a'] if last_gen == 'b' else ['a', 'b'])

        for gen in next_gens:
            for power in range(-max_power, max_power + 1):
                if power == 0:
                    continue
                new_word = word + [(gen, power)]
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


def explore_point(n, t, max_depth=6, tol=0.01):
    segment = get_segment(n)
    group = GGGroup(n)

    print(f"GG({n},{n}) Point Exploration")
    print("=" * 60)
    print(f"Segment: ({segment.start[0]:.6f}, {segment.start[1]:.6f}) to "
          f"({segment.end[0]:.6f}, {segment.end[1]:.6f})")
    print(f"Point t={t:.4f}: ({segment.from_t(t)[0]:.6f}, {segment.from_t(t)[1]:.6f})")
    print()

    words = generate_words(n, max_depth)
    words.sort(key=len)

    point = segment.from_t(t)
    mappings = []

    for word in words:
        mapped = group.apply_word(point, word)
        perp = segment.perp_distance(mapped)

        if perp < tol:
            ret_t = segment.to_t(mapped)
            if 0 <= ret_t <= 1:
                mappings.append({
                    'word': word,
                    'word_str': group.word_to_string(word),
                    'return_t': ret_t,
                    'depth': len(word),
                    'perp': perp
                })

    # Group by depth
    by_depth = {}
    for m in mappings:
        d = m['depth']
        if d not in by_depth:
            by_depth[d] = []
        by_depth[d].append(m)

    print(f"Found {len(mappings)} words that return point to segment")
    print()

    for depth in sorted(by_depth.keys()):
        items = by_depth[depth]
        print(f"Depth {depth} ({len(items)} words):")
        # Group by return location
        by_ret = {}
        for m in items:
            key = round(m['return_t'], 3)
            if key not in by_ret:
                by_ret[key] = []
            by_ret[key].append(m)

        for ret_t in sorted(by_ret.keys()):
            words_at_ret = by_ret[ret_t]
            print(f"  → t≈{ret_t:.3f}: {', '.join(m['word_str'] for m in words_at_ret[:5])}")
            if len(words_at_ret) > 5:
                print(f"              ... and {len(words_at_ret)-5} more")
        print()


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, required=True)
    parser.add_argument('--t', type=float, required=True, help='Point parameter in [0,1]')
    parser.add_argument('--depth', type=int, default=6)
    args = parser.parse_args()

    explore_point(args.n, args.t, args.depth)
