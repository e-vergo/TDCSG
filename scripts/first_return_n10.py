#!/usr/bin/env python3
"""
First Return Map Investigation for GG(10,10) IET

Investigates whether points in the middle interval [0.382, 0.618]
that leave the segment E'E eventually return, and what the first
return map structure looks like.
"""

import numpy as np
from typing import List, Tuple, Optional, Dict
from dataclasses import dataclass
from collections import defaultdict


@dataclass
class Segment:
    """A line segment defined by two endpoints."""
    start: np.ndarray
    end: np.ndarray

    @property
    def length(self) -> float:
        return np.linalg.norm(self.end - self.start)

    @property
    def direction(self) -> np.ndarray:
        return (self.end - self.start) / self.length

    def to_t(self, point: np.ndarray) -> float:
        """Project point onto segment, return parameter t in [0,1]."""
        return np.dot(point - self.start, self.direction) / self.length

    def from_t(self, t: float) -> np.ndarray:
        """Convert parameter t to point on segment."""
        return self.start + t * self.length * self.direction

    def perp_distance(self, point: np.ndarray) -> float:
        """Perpendicular distance from point to segment line."""
        t = self.to_t(point)
        closest = self.from_t(t)
        return np.linalg.norm(point - closest)

    def is_on_segment(self, point: np.ndarray, tol: float = 0.001) -> bool:
        """Check if point is on segment (within tolerance)."""
        t = self.to_t(point)
        perp = self.perp_distance(point)
        return perp < tol and -0.01 <= t <= 1.01


class GGGroup:
    """GG(n,n) compound symmetry group with centers at (-1,0) and (1,0)."""

    def __init__(self, n: int):
        self.n = n
        self.theta = -2 * np.pi / n  # Negative = clockwise
        self.center_a = np.array([-1., 0.])
        self.center_b = np.array([1., 0.])

    def rotate(self, point: np.ndarray, center: np.ndarray, power: int) -> np.ndarray:
        """Rotate point about center by power * theta."""
        angle = power * self.theta
        c, s = np.cos(angle), np.sin(angle)
        d = point - center
        return center + np.array([c*d[0] - s*d[1], s*d[0] + c*d[1]])

    def apply_word(self, point: np.ndarray, word: List[Tuple[str, int]]) -> np.ndarray:
        """Apply a group word to a point."""
        result = point.copy()
        for gen, power in word:
            center = self.center_a if gen == 'a' else self.center_b
            result = self.rotate(result, center, power)
        return result

    def word_to_string(self, word: List[Tuple[str, int]]) -> str:
        """Convert word to readable string."""
        parts = []
        for gen, power in word:
            if power == 1:
                parts.append(gen)
            elif power == -1:
                parts.append(f"{gen}⁻¹")
            else:
                parts.append(f"{gen}^{power}")
        return ''.join(parts)


def get_n10_segment() -> Segment:
    """Get the E'E segment for n=10."""
    n = 10
    zeta = np.exp(2j * np.pi / n)
    E = zeta - zeta**2
    return Segment(
        start=np.array([-E.real, -E.imag]),
        end=np.array([E.real, E.imag])
    )


def generate_words_up_to_depth(n: int, max_depth: int) -> List[List[Tuple[str, int]]]:
    """Generate alternating words up to given depth."""
    words = []
    max_power = n // 2

    def extend(word: List[Tuple[str, int]], depth: int):
        if depth == 0:
            if word:
                words.append(word[:])
            return

        if word:
            last_gen = word[-1][0]
            next_gen = 'b' if last_gen == 'a' else 'a'
        else:
            next_gen = None

        gens_to_try = [next_gen] if next_gen else ['a', 'b']

        for gen in gens_to_try:
            for power in range(-max_power, max_power + 1):
                if power == 0:
                    continue
                word.append((gen, power))
                words.append(word[:])  # Save at each step
                extend(word, depth - 1)
                word.pop()

    for start_gen in ['a', 'b']:
        for start_power in range(-max_power, max_power + 1):
            if start_power == 0:
                continue
            extend([(start_gen, start_power)], max_depth - 1)

    return words


def find_mappings_for_point(
    point: np.ndarray,
    segment: Segment,
    group: GGGroup,
    words: List[List[Tuple[str, int]]],
    tol: float = 0.005
) -> List[Dict]:
    """Find all words that map a point back onto the segment."""
    results = []
    for word in words:
        new_point = group.apply_word(point, word)
        if segment.is_on_segment(new_point, tol):
            t = segment.to_t(new_point)
            if 0 <= t <= 1:
                results.append({
                    'word': word,
                    'word_str': group.word_to_string(word),
                    'return_t': t,
                    'depth': len(word),
                    'perp_error': segment.perp_distance(new_point)
                })
    return results


def analyze_middle_interval():
    """Analyze the first return map for the middle interval."""

    segment = get_n10_segment()
    group = GGGroup(10)

    print("GG(10,10) First Return Map Investigation")
    print("=" * 70)
    print(f"Segment E'E: ({segment.start[0]:.6f}, {segment.start[1]:.6f}) to "
          f"({segment.end[0]:.6f}, {segment.end[1]:.6f})")
    print(f"Length: {segment.length:.6f}")
    print()

    # The known boundaries from 2-interval swap
    phi = (1 + np.sqrt(5)) / 2
    boundary1 = 1/phi - 0.5  # ~0.118
    boundary2 = 0.5 - 1/phi + 0.5  # ~0.382
    boundary3 = 1 - boundary2  # ~0.618
    boundary4 = 1 - boundary1  # ~0.882

    print(f"Expected boundaries: {boundary1:.4f}, {boundary2:.4f}, {boundary3:.4f}, {boundary4:.4f}")
    print()

    # Generate words
    print("Generating words up to depth 8...")
    words = generate_words_up_to_depth(10, 8)
    print(f"Generated {len(words)} words")
    print()

    # Sample the middle interval more densely
    print("Analyzing middle interval [0.38, 0.62]...")
    middle_start, middle_end = 0.38, 0.62
    num_samples = 100
    t_samples = np.linspace(middle_start, middle_end, num_samples)

    returns_by_t = {}

    for i, t in enumerate(t_samples):
        if i % 20 == 0:
            print(f"  Progress: {i}/{num_samples}")

        point = segment.from_t(t)
        mappings = find_mappings_for_point(point, segment, group, words)

        if mappings:
            # Keep shortest word for each distinct return location
            best_by_return = {}
            for m in mappings:
                key = round(m['return_t'], 3)
                if key not in best_by_return or m['depth'] < best_by_return[key]['depth']:
                    best_by_return[key] = m
            returns_by_t[t] = best_by_return

    print()
    print("=" * 70)
    print("RESULTS")
    print("=" * 70)
    print()

    if returns_by_t:
        print(f"Found returns for {len(returns_by_t)}/{num_samples} points")
        print()

        # Group by destination
        by_destination = defaultdict(list)
        for init_t, mappings in returns_by_t.items():
            for ret_t, m in mappings.items():
                by_destination[ret_t].append((init_t, m))

        print("Return destinations (grouped):")
        for ret_t in sorted(by_destination.keys()):
            items = by_destination[ret_t]
            init_ts = [x[0] for x in items]
            word = items[0][1]['word_str']
            print(f"  → t≈{ret_t:.3f}: from [{min(init_ts):.3f}, {max(init_ts):.3f}] via {word}")

        print()
        print("Detailed sample mappings:")
        for t in [0.40, 0.45, 0.50, 0.55, 0.60]:
            if t in returns_by_t:
                print(f"  t={t:.2f}:")
                for ret_t, m in sorted(returns_by_t[t].items()):
                    print(f"    → {ret_t:.4f} via {m['word_str']} (depth {m['depth']})")
            else:
                # Find closest
                closest_t = min(returns_by_t.keys(), key=lambda x: abs(x - t))
                print(f"  t={t:.2f} (using {closest_t:.3f}):")
                for ret_t, m in sorted(returns_by_t[closest_t].items()):
                    print(f"    → {ret_t:.4f} via {m['word_str']} (depth {m['depth']})")
    else:
        print("No returns found! Need deeper search or different approach.")

    # Check what happens to the very center (origin)
    print()
    print("Special check: t=0.5 (the origin)")
    center = segment.from_t(0.5)
    print(f"  Point: ({center[0]:.6f}, {center[1]:.6f})")

    # The origin should be fixed by certain words
    fixed_words = []
    for word in words:
        mapped = group.apply_word(center, word)
        if np.linalg.norm(mapped - center) < 0.001:
            fixed_words.append(group.word_to_string(word))

    if fixed_words:
        print(f"  Fixed by {len(fixed_words)} words, e.g.: {fixed_words[:5]}")


if __name__ == '__main__':
    analyze_middle_interval()
