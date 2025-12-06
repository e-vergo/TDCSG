#!/usr/bin/env python3
"""
Smart IET Search for N=10 with Aggressive Pruning

Key insights:
1. Only keep words that bring points back to the segment line
2. Early termination: if a partial word moves too far, prune
3. Focus on words with specific algebraic properties
"""

import numpy as np
from typing import List, Tuple, Dict, Optional

class Segment:
    def __init__(self, start, end):
        self.start = np.array(start)
        self.end = np.array(end)
        self._length = np.linalg.norm(end - start)
        self._direction = (end - start) / self._length

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
    return Segment(np.array([-E.real, -E.imag]), np.array([E.real, E.imag]))


def generate_words_pruned(n, max_depth, segment, group, test_points, tol=0.5, final_tol=0.01):
    """
    Generate words with aggressive pruning.

    Pruning strategy:
    - After each generator application, check if test points are still "near" segment
    - Near = perpendicular distance < tol (relaxed during construction)
    - Only keep words that bring at least one point back with final_tol
    """
    max_power = n // 2
    good_words = []
    pruned_count = 0
    total_checked = 0

    def check_points_near_line(word):
        """Check if any test points are near the segment after applying word."""
        for t in test_points:
            point = segment.from_t(t)
            mapped = group.apply_word(point, word)
            perp = segment.perp_distance(mapped)
            if perp < tol:
                return True
        return False

    def check_final_return(word):
        """Check if word returns any point to segment with strict tolerance."""
        for t in test_points:
            point = segment.from_t(t)
            mapped = group.apply_word(point, word)
            perp = segment.perp_distance(mapped)
            if perp < final_tol:
                ret_t = segment.to_t(mapped)
                if 0 <= ret_t <= 1 and abs(ret_t - t) > 0.05:
                    return True, t, ret_t
        return False, None, None

    def extend(word, depth):
        nonlocal pruned_count, total_checked
        if depth == 0:
            return

        last_gen = word[-1][0] if word else None
        next_gens = ['b'] if last_gen == 'a' else (['a'] if last_gen == 'b' else ['a', 'b'])

        for gen in next_gens:
            for power in range(-max_power, max_power + 1):
                if power == 0:
                    continue

                new_word = word + [(gen, power)]
                total_checked += 1

                # Early pruning: check if still near line
                if not check_points_near_line(new_word):
                    pruned_count += 1
                    continue

                # Check if this word returns points
                returns, from_t, to_t = check_final_return(new_word)
                if returns:
                    good_words.append({
                        'word': new_word[:],
                        'word_str': group.word_to_string(new_word),
                        'from_t': from_t,
                        'to_t': to_t,
                        'depth': len(new_word)
                    })

                extend(new_word, depth - 1)

    for start_gen in ['a', 'b']:
        for start_power in range(-max_power, max_power + 1):
            if start_power == 0:
                continue
            word = [(start_gen, start_power)]
            total_checked += 1

            if not check_points_near_line(word):
                pruned_count += 1
                continue

            returns, from_t, to_t = check_final_return(word)
            if returns:
                good_words.append({
                    'word': word[:],
                    'word_str': group.word_to_string(word),
                    'from_t': from_t,
                    'to_t': to_t,
                    'depth': 1
                })

            extend(word, max_depth - 1)

    return good_words, total_checked, pruned_count


def find_cyclic_iet(mappings, min_sep=0.1):
    """Find 3-cycles among mappings."""

    # Group by source region
    by_source = {}
    for m in mappings:
        key = round(m['from_t'], 1)
        if key not in by_source:
            by_source[key] = []
        by_source[key].append(m)

    # Find cycles
    cycles = []
    regions = sorted(by_source.keys())

    for r1 in regions:
        for m1 in by_source.get(r1, []):
            t1 = round(m1['to_t'], 1)
            for m2 in by_source.get(t1, []):
                if abs(m2['from_t'] - m1['to_t']) > 0.15:
                    continue
                t2 = round(m2['to_t'], 1)
                for m3 in by_source.get(t2, []):
                    if abs(m3['from_t'] - m2['to_t']) > 0.15:
                        continue
                    if abs(m3['to_t'] - r1) < 0.15:
                        # Found a cycle!
                        if m1['word_str'] != m2['word_str'] and m2['word_str'] != m3['word_str']:
                            cycles.append((m1, m2, m3))

    return cycles


def test_orbit(segment, group, cycle, start_t, max_steps=200):
    """Test orbit length for a 3-cycle."""
    m1, m2, m3 = cycle
    t = start_t
    positions = [t]

    for step in range(max_steps):
        # Determine which word to use based on position
        point = segment.from_t(t)

        # Try each word and see which one maps the point onto segment
        best_word = None
        best_dist = float('inf')
        best_ret = None

        for m in [m1, m2, m3]:
            mapped = group.apply_word(point, m['word'])
            perp = segment.perp_distance(mapped)
            ret_t = segment.to_t(mapped)
            if perp < 0.01 and 0 <= ret_t <= 1:
                if perp < best_dist:
                    best_dist = perp
                    best_word = m
                    best_ret = ret_t

        if best_word is None:
            return step, positions, "lost"

        t = best_ret
        positions.append(t)

        # Check if returned to start
        if step > 0 and abs(t - start_t) < 0.001:
            return step + 1, positions, "periodic"

    return max_steps, positions, "long"


def main():
    n = 10
    max_depth = 6  # Go deeper but with pruning

    segment = get_segment(n)
    group = GGGroup(n)

    print(f"Smart IET Search for GG({n},{n})")
    print("=" * 70)
    print(f"Segment: ({segment.start[0]:.4f}, {segment.start[1]:.4f}) to ({segment.end[0]:.4f}, {segment.end[1]:.4f})")
    print()

    # Test points for pruning
    test_points = np.linspace(0.1, 0.9, 20)

    print(f"Generating words up to depth {max_depth} with pruning...")
    good_words, total, pruned = generate_words_pruned(
        n, max_depth, segment, group, test_points, tol=0.3, final_tol=0.01
    )

    print(f"Checked {total} words, pruned {pruned}, kept {len(good_words)}")
    print()

    # Group by (from, to)
    unique_mappings = {}
    for w in good_words:
        key = (round(w['from_t'], 2), round(w['to_t'], 2))
        if key not in unique_mappings or w['depth'] < unique_mappings[key]['depth']:
            unique_mappings[key] = w

    print(f"Found {len(unique_mappings)} unique mappings")
    print()

    # Show mappings
    print("Mappings by direction:")
    by_delta = {}
    for (f, t), m in unique_mappings.items():
        delta = round(t - f, 2)
        if delta not in by_delta:
            by_delta[delta] = []
        by_delta[delta].append(m)

    for delta in sorted(by_delta.keys()):
        items = by_delta[delta]
        if abs(delta) > 0.05:
            example = items[0]
            print(f"  Δ={delta:+.2f}: {len(items)} mappings, e.g. {example['word_str']} (depth {example['depth']})")

    # Find cycles
    print()
    print("Searching for 3-cycles...")
    cycles = find_cyclic_iet(list(unique_mappings.values()), min_sep=0.08)

    if cycles:
        print(f"Found {len(cycles)} potential 3-cycles")

        # Test cycles
        verified = []
        for cycle in cycles[:20]:  # Test top 20
            m1, m2, m3 = cycle
            total_depth = m1['depth'] + m2['depth'] + m3['depth']

            # Test from multiple starting points
            orbit_lengths = []
            for t0 in [0.1, 0.3, 0.5, 0.7, 0.9]:
                length, _, status = test_orbit(segment, group, cycle, t0)
                orbit_lengths.append((length, status))

            has_long = any(l >= 100 for l, _ in orbit_lengths)
            if has_long:
                verified.append((cycle, orbit_lengths, total_depth))

        if verified:
            print()
            print("=" * 70)
            print("VERIFIED LONG-ORBIT CYCLES:")
            print("=" * 70)
            for (m1, m2, m3), orbits, depth in sorted(verified, key=lambda x: x[2])[:5]:
                print(f"\nTotal depth {depth}:")
                print(f"  {m1['from_t']:.2f} → {m1['to_t']:.2f} via {m1['word_str']}")
                print(f"  {m2['from_t']:.2f} → {m2['to_t']:.2f} via {m2['word_str']}")
                print(f"  {m3['from_t']:.2f} → {m3['to_t']:.2f} via {m3['word_str']}")
                print(f"  Orbit tests: {orbits}")
        else:
            print("\nNo long-orbit cycles found among candidates.")
    else:
        print("No 3-cycles found.")


if __name__ == '__main__':
    main()
