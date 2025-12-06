#!/usr/bin/env python3
"""
Targeted Cyclic IET Search for N=10

Strategy:
1. Use smart pruning during word generation
2. Focus on finding 3-cycles (not swaps)
3. Verify orbits are truly infinite (not periodic)
4. Consider multiple candidate segments
"""

import numpy as np
from typing import List, Tuple, Dict, Optional, Set
from itertools import permutations
import sys


class Segment:
    def __init__(self, start, end):
        self.start = np.array(start, dtype=float)
        self.end = np.array(end, dtype=float)
        self._length = np.linalg.norm(self.end - self.start)
        self._direction = (self.end - self.start) / self._length

    @property
    def length(self): return self._length

    @property
    def direction(self): return self._direction

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
        self.theta = -2 * np.pi / n  # clockwise
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


def get_standard_segment(n):
    """Standard segment E'E where E = ζₙ - ζₙ²"""
    zeta = np.exp(2j * np.pi / n)
    E = zeta - zeta**2
    return Segment([-E.real, -E.imag], [E.real, E.imag])


def generate_words_with_pruning(n, max_depth, segment, group, tol=1.0):
    """
    Generate words with distance-based pruning.
    Only keep words where at least one test point stays near the segment line.
    """
    max_power = n // 2
    # More test points, especially in middle region
    test_ts = [0.1, 0.2, 0.3, 0.4, 0.45, 0.5, 0.55, 0.6, 0.7, 0.8, 0.9]
    test_points = [segment.from_t(t) for t in test_ts]

    words = []
    pruned = 0

    def check_near(word):
        """Check if any test point maps near the segment line."""
        for pt in test_points:
            mapped = group.apply_word(pt, word)
            if segment.perp_distance(mapped) < tol:
                return True
        return False

    def extend(word, depth):
        nonlocal pruned
        if depth == 0:
            return

        last_gen = word[-1][0]
        next_gen = 'b' if last_gen == 'a' else 'a'

        for power in range(-max_power, max_power + 1):
            if power == 0:
                continue

            new_word = word + [(next_gen, power)]

            if not check_near(new_word):
                pruned += 1
                continue

            words.append(new_word)
            extend(new_word, depth - 1)

    # Start with each generator
    for start_gen in ['a', 'b']:
        for start_power in range(-max_power, max_power + 1):
            if start_power == 0:
                continue
            word = [(start_gen, start_power)]
            if check_near(word):
                words.append(word)
                extend(word, max_depth - 1)
            else:
                pruned += 1

    return words, pruned


def find_interval_mappings(segment, group, words, tol=0.005, min_samples=5):
    """
    Find words that map intervals to intervals on the segment.
    Returns dict: (from_interval, to_interval) -> word info
    """
    mappings = {}

    # Sample points
    sample_ts = np.linspace(0.02, 0.98, 50)

    for word in words:
        valid_from = []
        valid_to = []

        for t in sample_ts:
            point = segment.from_t(t)
            mapped = group.apply_word(point, word)
            perp = segment.perp_distance(mapped)
            ret_t = segment.to_t(mapped)

            if perp < tol and 0 <= ret_t <= 1:
                valid_from.append(t)
                valid_to.append(ret_t)

        if len(valid_from) >= min_samples:
            from_min, from_max = min(valid_from), max(valid_from)
            to_min, to_max = min(valid_to), max(valid_to)

            # Round to 2 decimal places for grouping
            key = (round(from_min, 2), round(from_max, 2),
                   round(to_min, 2), round(to_max, 2))

            if key not in mappings or len(word) < mappings[key]['depth']:
                mappings[key] = {
                    'word': word,
                    'word_str': group.word_to_string(word),
                    'depth': len(word),
                    'from_interval': (from_min, from_max),
                    'to_interval': (to_min, to_max)
                }

    return mappings


def is_swap(perm):
    """Check if permutation is a swap (2-cycle) rather than true 3-cycle."""
    # perm is like (0, 1, 2) -> (1, 2, 0)
    # A swap would be like (0, 1, 2) -> (1, 0, 2) or (2, 1, 0), etc.
    return perm in [(1, 0, 2), (0, 2, 1), (2, 1, 0)]


def find_cyclic_structures(mappings, segment, group, min_separation=0.1):
    """
    Look for genuine cyclic permutations among the mappings.
    A 3-cycle: I1 → I2 → I3 → I1 where all intervals are distinct.
    """
    # Extract distinct intervals
    intervals = set()
    for key, m in mappings.items():
        from_int = m['from_interval']
        to_int = m['to_interval']
        intervals.add((round(from_int[0], 2), round(from_int[1], 2)))
        intervals.add((round(to_int[0], 2), round(to_int[1], 2)))

    intervals = list(intervals)
    print(f"Found {len(intervals)} distinct intervals")

    # Build mapping graph
    # edge: (from_interval) -> [(to_interval, word_info), ...]
    graph = {}
    for key, m in mappings.items():
        from_int = (round(m['from_interval'][0], 2), round(m['from_interval'][1], 2))
        to_int = (round(m['to_interval'][0], 2), round(m['to_interval'][1], 2))

        if from_int not in graph:
            graph[from_int] = []
        graph[from_int].append((to_int, m))

    # Find 3-cycles
    cycles = []

    for i1 in intervals:
        if i1 not in graph:
            continue

        for (i2, m1) in graph[i1]:
            if i2 not in graph:
                continue
            if abs(i2[0] - i1[0]) < min_separation and abs(i2[1] - i1[1]) < min_separation:
                continue  # Same interval

            for (i3, m2) in graph[i2]:
                if i3 not in graph:
                    continue
                if abs(i3[0] - i1[0]) < min_separation and abs(i3[1] - i1[1]) < min_separation:
                    continue
                if abs(i3[0] - i2[0]) < min_separation and abs(i3[1] - i2[1]) < min_separation:
                    continue

                # Check if i3 → i1 exists
                for (back, m3) in graph.get(i3, []):
                    if abs(back[0] - i1[0]) < 0.05 and abs(back[1] - i1[1]) < 0.05:
                        # Found a 3-cycle!
                        total_depth = m1['depth'] + m2['depth'] + m3['depth']
                        cycles.append({
                            'intervals': (i1, i2, i3),
                            'words': (m1, m2, m3),
                            'total_depth': total_depth
                        })

    return cycles


def verify_cycle_orbits(cycle, segment, group, num_starts=20, max_steps=500):
    """
    Verify that a cycle produces infinite (or very long) orbits.
    Returns (has_infinite, orbit_lengths)
    """
    i1, i2, i3 = cycle['intervals']
    w1, w2, w3 = cycle['words']

    # Determine which word to use based on position
    def get_word_for_t(t):
        # Find which interval t is closest to
        d1 = min(abs(t - i1[0]), abs(t - i1[1]))
        d2 = min(abs(t - i2[0]), abs(t - i2[1]))
        d3 = min(abs(t - i3[0]), abs(t - i3[1]))

        if i1[0] <= t <= i1[1]:
            return w1['word']
        elif i2[0] <= t <= i2[1]:
            return w2['word']
        elif i3[0] <= t <= i3[1]:
            return w3['word']
        else:
            # Default to closest
            if d1 <= d2 and d1 <= d3:
                return w1['word']
            elif d2 <= d3:
                return w2['word']
            else:
                return w3['word']

    orbit_lengths = []

    # Test from multiple starting points
    start_ts = np.linspace(0.05, 0.95, num_starts)

    for start_t in start_ts:
        t = start_t
        visited = set()

        for step in range(max_steps):
            t_key = round(t, 5)
            if t_key in visited:
                orbit_lengths.append(step)
                break
            visited.add(t_key)

            point = segment.from_t(t)
            word = get_word_for_t(t)

            if word is None:
                orbit_lengths.append(step)
                break

            mapped = group.apply_word(point, word)
            new_t = segment.to_t(mapped)

            if not 0 <= new_t <= 1:
                orbit_lengths.append(step)
                break

            t = new_t
        else:
            orbit_lengths.append(max_steps)  # Didn't close

    has_infinite = any(l >= max_steps for l in orbit_lengths)
    return has_infinite, orbit_lengths


def main():
    n = 10
    max_depth = 8  # Go deeper with relaxed pruning

    segment = get_standard_segment(n)
    group = GGGroup(n)

    print(f"Cyclic IET Search for GG({n},{n})")
    print("=" * 70)
    print(f"Segment: ({segment.start[0]:.6f}, {segment.start[1]:.6f}) to ({segment.end[0]:.6f}, {segment.end[1]:.6f})")
    print(f"Length: {segment.length:.6f}")
    print()

    print(f"Generating words up to depth {max_depth} with pruning...")
    words, pruned = generate_words_with_pruning(n, max_depth, segment, group, tol=0.8)
    print(f"Generated {len(words)} words (pruned {pruned})")
    print()

    print("Finding interval mappings...")
    mappings = find_interval_mappings(segment, group, words)
    print(f"Found {len(mappings)} distinct interval mappings")
    print()

    # Show some mappings
    print("Sample mappings:")
    by_depth = {}
    for key, m in mappings.items():
        d = m['depth']
        if d not in by_depth:
            by_depth[d] = []
        by_depth[d].append(m)

    for depth in sorted(by_depth.keys())[:4]:
        items = by_depth[depth][:3]
        for m in items:
            fi, ti = m['from_interval'], m['to_interval']
            print(f"  [{fi[0]:.2f},{fi[1]:.2f}] → [{ti[0]:.2f},{ti[1]:.2f}] by {m['word_str']}")
    print()

    print("Searching for 3-cycles...")
    cycles = find_cyclic_structures(mappings, segment, group, min_separation=0.08)

    if cycles:
        # Sort by total depth
        cycles.sort(key=lambda x: x['total_depth'])
        print(f"Found {len(cycles)} potential 3-cycles")

        # Test top candidates
        verified = []
        print("\nVerifying cycles...")

        for i, cycle in enumerate(cycles[:30]):
            has_infinite, lengths = verify_cycle_orbits(cycle, segment, group)

            if has_infinite:
                verified.append((cycle, lengths))
                print(f"  ✓ Cycle {i+1}: infinite orbits found")
            else:
                max_len = max(lengths) if lengths else 0
                if max_len >= 100:
                    print(f"  ? Cycle {i+1}: max orbit {max_len}")

        if verified:
            print("\n" + "=" * 70)
            print("VERIFIED CYCLIC IET STRUCTURES WITH INFINITE ORBITS:")
            print("=" * 70)

            for (cycle, lengths) in verified[:5]:
                i1, i2, i3 = cycle['intervals']
                w1, w2, w3 = cycle['words']

                print(f"\nTotal depth: {cycle['total_depth']}")
                print(f"  [{i1[0]:.3f}, {i1[1]:.3f}] → [{i2[0]:.3f}, {i2[1]:.3f}] by {w1['word_str']}")
                print(f"  [{i2[0]:.3f}, {i2[1]:.3f}] → [{i3[0]:.3f}, {i3[1]:.3f}] by {w2['word_str']}")
                print(f"  [{i3[0]:.3f}, {i3[1]:.3f}] → [{i1[0]:.3f}, {i1[1]:.3f}] by {w3['word_str']}")

                # Show orbit length distribution
                orbit_dist = {}
                for l in lengths:
                    bucket = l // 100 * 100
                    orbit_dist[bucket] = orbit_dist.get(bucket, 0) + 1
                print(f"  Orbit lengths: {dict(sorted(orbit_dist.items()))}")
        else:
            print("\nNo verified infinite orbit cycles found.")
            print("All candidates have periodic orbits.")
    else:
        print("No 3-cycles found.")

    # Look for words that map middle interval to somewhere ELSE
    print("\n" + "=" * 70)
    print("Searching for words that move the MIDDLE interval...")
    print("Middle interval: [0.382, 0.618]")

    middle_ts = np.linspace(0.4, 0.6, 20)
    middle_mappings = []

    for word in words:
        valid_from = []
        valid_to = []

        for t in middle_ts:
            point = segment.from_t(t)
            mapped = group.apply_word(point, word)
            perp = segment.perp_distance(mapped)
            ret_t = segment.to_t(mapped)

            if perp < 0.01 and 0 <= ret_t <= 1:
                valid_from.append(t)
                valid_to.append(ret_t)

        if len(valid_from) >= 5:
            from_center = np.mean(valid_from)
            to_center = np.mean(valid_to)
            # Check if it maps to edges (not back to middle)
            if to_center < 0.35 or to_center > 0.65:
                middle_mappings.append({
                    'word': word,
                    'word_str': group.word_to_string(word),
                    'depth': len(word),
                    'from_center': from_center,
                    'to_center': to_center,
                })

    if middle_mappings:
        middle_mappings.sort(key=lambda x: x['depth'])
        print(f"Found {len(middle_mappings)} words mapping middle to edges:")
        for m in middle_mappings[:10]:
            print(f"  {m['word_str']} (depth {m['depth']}): {m['from_center']:.3f} → {m['to_center']:.3f}")
    else:
        print("No words found that map middle interval to edges!")
        print("This explains why we only get swap structure.")

    # Also look for 4-cycles
    print("\n" + "=" * 70)
    print("Checking for known swap structure...")

    # The swap structure
    swap_words = {
        'forward': [('b', -1), ('a', -1), ('b', 1), ('a', 1)],  # b⁻¹a⁻¹ba
        'back': [('a', -1), ('b', -1), ('a', 1), ('b', 1)],     # a⁻¹b⁻¹ab
    }

    for name, word in swap_words.items():
        print(f"\n{name}: {group.word_to_string(word)}")
        valid_from = []
        valid_to = []

        for t in np.linspace(0.02, 0.98, 50):
            point = segment.from_t(t)
            mapped = group.apply_word(point, word)
            perp = segment.perp_distance(mapped)
            ret_t = segment.to_t(mapped)

            if perp < 0.005 and 0 <= ret_t <= 1:
                valid_from.append(t)
                valid_to.append(ret_t)

        if valid_from:
            print(f"  Domain: [{min(valid_from):.3f}, {max(valid_from):.3f}]")
            print(f"  Image:  [{min(valid_to):.3f}, {max(valid_to):.3f}]")
            delta = np.mean(np.array(valid_to) - np.array(valid_from))
            print(f"  Translation: Δt ≈ {delta:.4f}")


if __name__ == '__main__':
    main()
