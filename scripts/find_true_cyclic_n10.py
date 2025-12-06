#!/usr/bin/env python3
"""
Find TRUE cyclic IET for N=10

The key insight from N=5 is that we need:
1. A cyclic permutation (not just swap)
2. The composition of the 3 words gives an irrational rotation

This script searches for genuine cyclic structures by:
1. Finding all interval-preserving words
2. Looking for triples with different destinations
3. Verifying the cycle actually produces infinite orbits
"""

import numpy as np
from typing import List, Tuple, Dict, Set, Optional
from itertools import product

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
        self.theta = -2 * np.pi / n  # Clockwise
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
    """Generate alternating words up to max_depth."""
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


def find_return_words_for_t(t, segment, group, words, tol=0.005):
    """Find all words that return point at t back to segment, with their destinations."""
    point = segment.from_t(t)
    results = []

    for word in words:
        mapped = group.apply_word(point, word)
        perp = segment.perp_distance(mapped)

        if perp < tol:
            ret_t = segment.to_t(mapped)
            if 0 <= ret_t <= 1 and abs(ret_t - t) > 0.01:  # Must move significantly
                results.append({
                    'word': word,
                    'word_str': group.word_to_string(word),
                    'from_t': t,
                    'to_t': ret_t,
                    'depth': len(word)
                })

    return results


def test_orbit_length(start_t, word_map, segment, group, max_steps=100):
    """
    Test how long an orbit is before returning to start or being lost.

    word_map: dict mapping interval index to (word, target_interval)
    Returns: orbit length, or -1 if infinite (didn't close after max_steps)
    """
    t = start_t
    visited = set()

    for step in range(max_steps):
        # Round to avoid floating point accumulation
        t_key = round(t, 6)
        if t_key in visited:
            return step
        visited.add(t_key)

        # Find which interval we're in and apply the corresponding word
        point = segment.from_t(t)

        # Try all words to find one that works
        found = False
        for interval_range, (word, _) in word_map.items():
            low, high = interval_range
            if low <= t <= high:
                mapped = group.apply_word(point, word)
                new_t = segment.to_t(mapped)
                if 0 <= new_t <= 1:
                    t = new_t
                    found = True
                    break

        if not found:
            return step  # Lost from segment

    return -1  # Didn't close - potentially infinite


def analyze_mapping_structure(segment, group, words, num_samples=100):
    """Analyze the mapping structure by sampling many points."""

    print("Sampling segment to understand mapping structure...")

    # Collect all mappings from sample points
    all_mappings = []
    t_samples = np.linspace(0.02, 0.98, num_samples)

    for t in t_samples:
        mappings = find_return_words_for_t(t, segment, group, words)
        for m in mappings:
            all_mappings.append(m)

    # Group by (from_region, to_region)
    # Use rounded centers
    by_direction = {}
    for m in all_mappings:
        from_r = round(m['from_t'], 2)
        to_r = round(m['to_t'], 2)
        key = (from_r, to_r)
        if key not in by_direction:
            by_direction[key] = []
        by_direction[key].append(m)

    print(f"Found {len(by_direction)} distinct (from, to) pairs")

    # Find the shortest word for each direction
    best_words = {}
    for (from_r, to_r), mappings in by_direction.items():
        best = min(mappings, key=lambda x: x['depth'])
        best_words[(from_r, to_r)] = best

    return best_words


def find_cyclic_structure(best_words, min_separation=0.1):
    """
    Look for cyclic permutation structure among the mappings.

    For a 3-cycle: I1 → I2 → I3 → I1
    We need:
    - A mapping from I1 to I2
    - A mapping from I2 to I3
    - A mapping from I3 to I1
    With I1, I2, I3 all distinct
    """

    # Extract unique regions
    all_regions = set()
    for (from_r, to_r) in best_words.keys():
        all_regions.add(from_r)
        all_regions.add(to_r)

    regions = sorted(all_regions)
    print(f"Unique regions: {regions}")

    # Look for 3-cycles
    cycles = []

    for r1 in regions:
        for r2 in regions:
            if abs(r2 - r1) < min_separation:
                continue

            # Does r1 → r2 exist?
            found_12 = None
            for (f, t), m in best_words.items():
                if abs(f - r1) < 0.05 and abs(t - r2) < 0.05:
                    found_12 = m
                    break

            if not found_12:
                continue

            for r3 in regions:
                if abs(r3 - r1) < min_separation or abs(r3 - r2) < min_separation:
                    continue

                # Does r2 → r3 exist?
                found_23 = None
                for (f, t), m in best_words.items():
                    if abs(f - r2) < 0.05 and abs(t - r3) < 0.05:
                        found_23 = m
                        break

                if not found_23:
                    continue

                # Does r3 → r1 exist?
                found_31 = None
                for (f, t), m in best_words.items():
                    if abs(f - r3) < 0.05 and abs(t - r1) < 0.05:
                        found_31 = m
                        break

                if found_31:
                    # Found a potential cycle!
                    cycles.append({
                        'regions': (r1, r2, r3),
                        'words': (found_12, found_23, found_31),
                        'total_depth': found_12['depth'] + found_23['depth'] + found_31['depth']
                    })

    return cycles


def verify_cycle_produces_infinite_orbits(cycle, segment, group, num_tests=10, max_steps=200):
    """
    Verify that a cycle actually produces infinite (or very long) orbits.
    """
    r1, r2, r3 = cycle['regions']
    w1, w2, w3 = cycle['words']

    print(f"\nVerifying cycle: {r1:.2f} → {r2:.2f} → {r3:.2f} → {r1:.2f}")
    print(f"  Words: {w1['word_str']}, {w2['word_str']}, {w3['word_str']}")

    # Test points from each region
    test_points = [
        r1 + 0.01,  # Just inside region 1
        (r1 + r2) / 2 if r2 > r1 else r1 - 0.05,
        r2 + 0.01,
        r3 + 0.01,
    ]

    orbit_lengths = []

    for start_t in test_points:
        if not 0 < start_t < 1:
            continue

        t = start_t
        visited_positions = [t]

        for step in range(max_steps):
            point = segment.from_t(t)

            # Determine which region and apply corresponding word
            word = None
            if abs(t - r1) < abs(t - r2) and abs(t - r1) < abs(t - r3):
                word = w1['word']
            elif abs(t - r2) < abs(t - r1) and abs(t - r2) < abs(t - r3):
                word = w2['word']
            else:
                word = w3['word']

            if word is None:
                break

            mapped = group.apply_word(point, word)
            new_t = segment.to_t(mapped)

            if not 0 <= new_t <= 1:
                break

            # Check if we've returned to near start
            if step > 0 and abs(new_t - start_t) < 0.001:
                orbit_lengths.append(step + 1)
                break

            t = new_t
            visited_positions.append(t)
        else:
            orbit_lengths.append(max_steps)  # Didn't close

    print(f"  Orbit lengths from test points: {orbit_lengths}")

    # Infinite if any orbit didn't close
    has_infinite = any(l >= max_steps for l in orbit_lengths)
    return has_infinite, orbit_lengths


def main():
    n = 10
    max_depth = 6

    segment = get_segment(n)
    group = GGGroup(n)

    print(f"TRUE Cyclic IET Search for GG({n},{n})")
    print("=" * 70)
    print(f"Segment: ({segment.start[0]:.6f}, {segment.start[1]:.6f}) to "
          f"({segment.end[0]:.6f}, {segment.end[1]:.6f})")
    print(f"Length: {segment.length:.6f}")
    print()

    print(f"Generating words up to depth {max_depth}...")
    words = generate_words(n, max_depth)
    words.sort(key=len)
    print(f"Generated {len(words)} words")
    print()

    # Analyze mapping structure
    best_words = analyze_mapping_structure(segment, group, words, num_samples=200)

    print("\nBest words by direction:")
    for (from_r, to_r), m in sorted(best_words.items()):
        if abs(to_r - from_r) > 0.05:  # Non-trivial movement
            print(f"  {from_r:.2f} → {to_r:.2f}: {m['word_str']} (depth {m['depth']})")

    # Look for cyclic structure
    print("\nSearching for 3-cycles...")
    cycles = find_cyclic_structure(best_words, min_separation=0.08)

    if cycles:
        print(f"Found {len(cycles)} potential cycles")

        # Sort by total depth
        cycles.sort(key=lambda x: x['total_depth'])

        # Test top candidates
        verified_cycles = []
        for i, cycle in enumerate(cycles[:10]):
            is_infinite, lengths = verify_cycle_produces_infinite_orbits(cycle, segment, group)
            if is_infinite:
                verified_cycles.append((cycle, lengths))

        if verified_cycles:
            print("\n" + "=" * 70)
            print("VERIFIED INFINITE ORBIT CYCLES:")
            print("=" * 70)
            for cycle, lengths in verified_cycles:
                r1, r2, r3 = cycle['regions']
                w1, w2, w3 = cycle['words']
                print(f"\nRegions: {r1:.3f} → {r2:.3f} → {r3:.3f}")
                print(f"  {w1['word_str']}: [{w1['from_t']:.3f}] → [{w1['to_t']:.3f}]")
                print(f"  {w2['word_str']}: [{w2['from_t']:.3f}] → [{w2['to_t']:.3f}]")
                print(f"  {w3['word_str']}: [{w3['from_t']:.3f}] → [{w3['to_t']:.3f}]")
                print(f"  Orbit lengths: {lengths}")
        else:
            print("\nNo verified infinite orbit cycles found.")
    else:
        print("No cyclic structure found.")

    # Also check for 2-cycles with different structure
    print("\n" + "=" * 70)
    print("Looking for 2-cycles (swaps)...")
    for (f1, t1), m1 in best_words.items():
        for (f2, t2), m2 in best_words.items():
            if abs(f1 - t2) < 0.05 and abs(t1 - f2) < 0.05 and abs(f1 - f2) > 0.1:
                print(f"  Swap: {f1:.2f} ↔ {t1:.2f}")
                print(f"    Forward: {m1['word_str']}")
                print(f"    Back: {m2['word_str']}")


if __name__ == '__main__':
    main()
