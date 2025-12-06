#!/usr/bin/env python3
"""
Search for CYCLIC IET structure for N=10

Looking for 3 words W1, W2, W3 that form a cycle:
  W1: I1 → I2
  W2: I2 → I3
  W3: I3 → I1

This cyclic structure produces infinite orbits.
"""

import numpy as np
from typing import List, Tuple, Dict, Set
from itertools import product
from collections import defaultdict


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
    """Generate alternating words."""
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


def analyze_word_mapping(word, segment, group, num_samples=20, tol=0.01):
    """Analyze what interval a word maps from and to."""
    t_samples = np.linspace(0.01, 0.99, num_samples)

    valid_from = []
    valid_to = []

    for t in t_samples:
        point = segment.from_t(t)
        mapped = group.apply_word(point, word)
        perp = segment.perp_distance(mapped)
        ret_t = segment.to_t(mapped)

        if perp < tol and 0 <= ret_t <= 1:
            valid_from.append(t)
            valid_to.append(ret_t)

    if not valid_from:
        return None

    return {
        'from_min': min(valid_from),
        'from_max': max(valid_from),
        'to_min': min(valid_to),
        'to_max': max(valid_to),
        'from_center': (min(valid_from) + max(valid_from)) / 2,
        'to_center': (min(valid_to) + max(valid_to)) / 2,
    }


def find_cyclic_iet(n, max_depth=6):
    """Search for cyclic IET structure."""

    segment = get_segment(n)
    group = GGGroup(n)

    print(f"Searching for cyclic IET in GG({n},{n})")
    print("=" * 70)
    print()

    print(f"Generating words up to depth {max_depth}...")
    words = generate_words(n, max_depth)
    words.sort(key=len)
    print(f"Generated {len(words)} words")
    print()

    print("Analyzing word mappings...")
    word_mappings = []

    for i, word in enumerate(words):
        if i % 500 == 0:
            print(f"  Progress: {i}/{len(words)}")

        mapping = analyze_word_mapping(word, segment, group)
        if mapping:
            word_mappings.append({
                'word': word,
                'word_str': group.word_to_string(word),
                'depth': len(word),
                **mapping
            })

    print(f"\nFound {len(word_mappings)} words that map segment to itself")
    print()

    # Group by approximate (from_center, to_center) to find distinct mappings
    distinct_mappings = {}
    for m in word_mappings:
        key = (round(m['from_center'], 2), round(m['to_center'], 2))
        if key not in distinct_mappings or m['depth'] < distinct_mappings[key]['depth']:
            distinct_mappings[key] = m

    print(f"Found {len(distinct_mappings)} distinct mapping types")
    print()

    # Look for cyclic structure
    print("Looking for cyclic permutation (I1→I2→I3→I1)...")
    print()

    # Partition [0,1] into candidate intervals
    boundaries = set([0.0, 1.0])
    for m in distinct_mappings.values():
        boundaries.add(round(m['from_min'], 3))
        boundaries.add(round(m['from_max'], 3))
        boundaries.add(round(m['to_min'], 3))
        boundaries.add(round(m['to_max'], 3))

    boundaries = sorted(boundaries)
    print(f"Candidate boundaries: {[f'{b:.3f}' for b in boundaries]}")
    print()

    # For each triple of intervals, check if we have a cycle
    intervals = [(boundaries[i], boundaries[i+1]) for i in range(len(boundaries)-1)]
    intervals = [(a, b) for a, b in intervals if b - a > 0.05]  # Filter tiny intervals

    print(f"Checking {len(intervals)} candidate intervals for cycles...")

    cycles_found = []

    for i1 in range(len(intervals)):
        for i2 in range(len(intervals)):
            if i2 == i1:
                continue
            for i3 in range(len(intervals)):
                if i3 == i1 or i3 == i2:
                    continue

                int1, int2, int3 = intervals[i1], intervals[i2], intervals[i3]

                # Find words that map int1 → int2
                w1_candidates = []
                for m in word_mappings:
                    if (m['from_min'] <= (int1[0] + int1[1])/2 <= m['from_max'] and
                        m['to_min'] <= (int2[0] + int2[1])/2 <= m['to_max']):
                        w1_candidates.append(m)

                # Find words that map int2 → int3
                w2_candidates = []
                for m in word_mappings:
                    if (m['from_min'] <= (int2[0] + int2[1])/2 <= m['from_max'] and
                        m['to_min'] <= (int3[0] + int3[1])/2 <= m['to_max']):
                        w2_candidates.append(m)

                # Find words that map int3 → int1
                w3_candidates = []
                for m in word_mappings:
                    if (m['from_min'] <= (int3[0] + int3[1])/2 <= m['from_max'] and
                        m['to_min'] <= (int1[0] + int1[1])/2 <= m['to_max']):
                        w3_candidates.append(m)

                if w1_candidates and w2_candidates and w3_candidates:
                    # Found a potential cycle!
                    w1 = min(w1_candidates, key=lambda x: x['depth'])
                    w2 = min(w2_candidates, key=lambda x: x['depth'])
                    w3 = min(w3_candidates, key=lambda x: x['depth'])

                    cycles_found.append({
                        'intervals': (int1, int2, int3),
                        'words': (w1, w2, w3),
                        'total_depth': w1['depth'] + w2['depth'] + w3['depth']
                    })

    if cycles_found:
        # Sort by total depth
        cycles_found.sort(key=lambda x: x['total_depth'])

        print(f"\nFound {len(cycles_found)} potential cycles!")
        print()

        for i, cycle in enumerate(cycles_found[:5]):  # Show top 5
            print(f"Cycle {i+1} (total depth {cycle['total_depth']}):")
            i1, i2, i3 = cycle['intervals']
            w1, w2, w3 = cycle['words']
            print(f"  I1=[{i1[0]:.3f}, {i1[1]:.3f}] → I2=[{i2[0]:.3f}, {i2[1]:.3f}] via {w1['word_str']}")
            print(f"  I2=[{i2[0]:.3f}, {i2[1]:.3f}] → I3=[{i3[0]:.3f}, {i3[1]:.3f}] via {w2['word_str']}")
            print(f"  I3=[{i3[0]:.3f}, {i3[1]:.3f}] → I1=[{i1[0]:.3f}, {i1[1]:.3f}] via {w3['word_str']}")
            print()
    else:
        print("No cyclic structure found at this depth.")
        print()
        print("Showing all distinct mappings:")
        for (fc, tc), m in sorted(distinct_mappings.items()):
            print(f"  [{m['from_min']:.3f}, {m['from_max']:.3f}] → [{m['to_min']:.3f}, {m['to_max']:.3f}] via {m['word_str']}")

    return cycles_found


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, default=10)
    parser.add_argument('--depth', type=int, default=6)
    args = parser.parse_args()

    find_cyclic_iet(args.n, args.depth)
