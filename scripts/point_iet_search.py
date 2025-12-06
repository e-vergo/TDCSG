#!/usr/bin/env python3
"""
Point-Based IET Discovery for GG(n,n)

Algorithm:
1. Distribute sample points along the segment
2. For each point, find group words that return it to the segment
3. Use binary search to find exact interval boundaries where words change
"""

import numpy as np
from typing import List, Tuple, Optional, Dict, Set
from dataclasses import dataclass


@dataclass
class Segment:
    start: np.ndarray
    end: np.ndarray

    @property
    def length(self) -> float:
        return np.linalg.norm(self.end - self.start)

    @property
    def direction(self) -> np.ndarray:
        return (self.end - self.start) / self.length

    def to_t(self, point: np.ndarray) -> float:
        return np.dot(point - self.start, self.direction) / self.length

    def from_t(self, t: float) -> np.ndarray:
        return self.start + t * self.length * self.direction

    def perp_distance(self, point: np.ndarray) -> float:
        t = self.to_t(point)
        closest = self.from_t(t)
        return np.linalg.norm(point - closest)


class GGGroup:
    def __init__(self, n: int):
        self.n = n
        self.theta = -2 * np.pi / n
        self.center_a = np.array([-1., 0.])
        self.center_b = np.array([1., 0.])

    def rotate(self, point: np.ndarray, center: np.ndarray, power: int) -> np.ndarray:
        angle = power * self.theta
        c, s = np.cos(angle), np.sin(angle)
        d = point - center
        return center + np.array([c*d[0] - s*d[1], s*d[0] + c*d[1]])

    def apply_word(self, point: np.ndarray, word: List[Tuple[str, int]]) -> np.ndarray:
        result = point.copy()
        for gen, power in word:
            center = self.center_a if gen == 'a' else self.center_b
            result = self.rotate(result, center, power)
        return result

    def word_to_string(self, word: List[Tuple[str, int]]) -> str:
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

    def word_to_tuple(self, word: List[Tuple[str, int]]) -> tuple:
        return tuple(word)


def get_segment(n: int) -> Segment:
    """Get the E'E segment for given n."""
    zeta = np.exp(2j * np.pi / n)
    E = zeta - zeta**2
    return Segment(
        start=np.array([-E.real, -E.imag]),
        end=np.array([E.real, E.imag])
    )


def generate_alternating_words(n: int, max_depth: int) -> List[List[Tuple[str, int]]]:
    """Generate alternating words up to given depth."""
    words = []
    max_power = n // 2

    def extend(word: List[Tuple[str, int]], depth: int):
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


def find_return_word(
    t: float,
    segment: Segment,
    group: GGGroup,
    words: List[List[Tuple[str, int]]],
    tol: float = 0.005
) -> Optional[Tuple[List[Tuple[str, int]], float]]:
    """Find shortest word that maps point at t back to segment."""
    point = segment.from_t(t)
    best = None

    for word in words:
        mapped = group.apply_word(point, word)
        perp = segment.perp_distance(mapped)

        if perp < tol:
            ret_t = segment.to_t(mapped)
            if 0 <= ret_t <= 1 and abs(ret_t - t) > 0.01:  # Must move significantly
                if best is None or len(word) < len(best[0]):
                    best = (word, ret_t)

    return best


def same_word(w1: List[Tuple[str, int]], w2: List[Tuple[str, int]]) -> bool:
    """Check if two words are the same."""
    if len(w1) != len(w2):
        return False
    return all(a == b for a, b in zip(w1, w2))


def find_left_boundary(
    t_inside: float,
    target_word: List[Tuple[str, int]],
    segment: Segment,
    group: GGGroup,
    words: List[List[Tuple[str, int]]],
    tol: float = 1e-6,
    max_iter: int = 50
) -> float:
    """Binary search leftward to find where word starts working."""
    t_low, t_high = 0.0, t_inside

    for _ in range(max_iter):
        if t_high - t_low < tol:
            break
        t_mid = (t_low + t_high) / 2
        result = find_return_word(t_mid, segment, group, words)

        if result and same_word(result[0], target_word):
            t_high = t_mid  # Word works here, search further left
        else:
            t_low = t_mid   # Word doesn't work, boundary is to the right

    return (t_low + t_high) / 2


def find_right_boundary(
    t_inside: float,
    target_word: List[Tuple[str, int]],
    segment: Segment,
    group: GGGroup,
    words: List[List[Tuple[str, int]]],
    tol: float = 1e-6,
    max_iter: int = 50
) -> float:
    """Binary search rightward to find where word stops working."""
    t_low, t_high = t_inside, 1.0

    for _ in range(max_iter):
        if t_high - t_low < tol:
            break
        t_mid = (t_low + t_high) / 2
        result = find_return_word(t_mid, segment, group, words)

        if result and same_word(result[0], target_word):
            t_low = t_mid   # Word works here, search further right
        else:
            t_high = t_mid  # Word doesn't work, boundary is to the left

    return (t_low + t_high) / 2


def discover_iet(n: int, max_depth: int = 6, num_samples: int = 50):
    """Discover IET structure using point-based search."""

    segment = get_segment(n)
    group = GGGroup(n)

    print(f"Point-Based IET Discovery for GG({n},{n})")
    print("=" * 70)
    print(f"Segment: ({segment.start[0]:.6f}, {segment.start[1]:.6f}) to "
          f"({segment.end[0]:.6f}, {segment.end[1]:.6f})")
    print(f"Length: {segment.length:.6f}")
    print()

    print(f"Generating words up to depth {max_depth}...")
    words = generate_alternating_words(n, max_depth)
    # Sort by length for finding shortest
    words.sort(key=len)
    print(f"Generated {len(words)} words")
    print()

    # Phase 1: Sample points densely and find shortest word for each
    print("Phase 1: Sampling points and finding shortest return words...")
    t_samples = np.linspace(0.001, 0.999, num_samples)

    # For each sample, record the shortest word
    point_words = []  # list of (t, word, return_t)

    for t in t_samples:
        result = find_return_word(t, segment, group, words)
        if result:
            word, ret_t = result
            point_words.append((t, word, ret_t))

    print(f"Found {len(point_words)} points with return words")
    print()

    # Phase 2: Find contiguous regions with same word
    print("Phase 2: Identifying contiguous regions...")
    regions = []
    if point_words:
        current_word = point_words[0][1]
        current_start = point_words[0][0]
        current_ret = point_words[0][2]
        prev_t = point_words[0][0]

        for t, word, ret_t in point_words[1:]:
            if not same_word(word, current_word):
                # Word changed - end current region
                regions.append({
                    'sample_start': current_start,
                    'sample_end': prev_t,
                    'word': current_word,
                    'return_t': current_ret
                })
                current_word = word
                current_start = t
                current_ret = ret_t
            prev_t = t

        # Don't forget last region
        regions.append({
            'sample_start': current_start,
            'sample_end': prev_t,
            'word': current_word,
            'return_t': current_ret
        })

    print(f"Found {len(regions)} contiguous regions")
    print()

    # Phase 3: Refine boundaries with binary search
    print("Phase 3: Refining boundaries with binary search...")
    intervals = []

    for region in regions:
        word = region['word']
        t_mid = (region['sample_start'] + region['sample_end']) / 2

        left_bound = find_left_boundary(t_mid, word, segment, group, words)
        right_bound = find_right_boundary(t_mid, word, segment, group, words)

        intervals.append({
            'left': left_bound,
            'right': right_bound,
            'word': word,
            'word_str': group.word_to_string(word),
            'return_t': region['return_t']
        })

    # Sort by left boundary
    intervals.sort(key=lambda x: x['left'])

    print()
    print("=" * 70)
    print("DISCOVERED IET STRUCTURE")
    print("=" * 70)
    print()

    print("Intervals and their mappings:")
    for i, intv in enumerate(intervals):
        length = intv['right'] - intv['left']
        print(f"  [{intv['left']:.6f}, {intv['right']:.6f}] (length {length:.6f})")
        print(f"    → maps to ~{intv['return_t']:.6f} via {intv['word_str']}")
        print()

    # Check coverage
    print("Coverage analysis:")
    sorted_intervals = sorted(intervals, key=lambda x: x['left'])
    gaps = []
    prev_right = 0
    for intv in sorted_intervals:
        if intv['left'] > prev_right + 0.001:
            gaps.append((prev_right, intv['left']))
        prev_right = max(prev_right, intv['right'])
    if prev_right < 0.999:
        gaps.append((prev_right, 1.0))

    if gaps:
        print(f"  GAPS found (may need deeper search):")
        for g in gaps:
            print(f"    [{g[0]:.6f}, {g[1]:.6f}]")
    else:
        print("  Full coverage achieved!")

    # Verify lengths sum to ~1
    total_length = sum(intv['right'] - intv['left'] for intv in intervals)
    print(f"\n  Total interval length: {total_length:.6f}")

    return intervals


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, default=10)
    parser.add_argument('--depth', type=int, default=6)
    parser.add_argument('--samples', type=int, default=50)
    args = parser.parse_args()

    discover_iet(args.n, args.depth, args.samples)
