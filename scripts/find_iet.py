#!/usr/bin/env python3
"""
IET Word Finder for GG(n,n) Compound Symmetry Groups

Finds group words that map parts of a given line segment to itself.

Rotation centers are fixed at (-1, 0) and (1, 0).
- Generator a: rotation by -2π/n about (-1, 0) (clockwise)
- Generator b: rotation by -2π/n about (1, 0) (clockwise)

Usage:
    python find_iet.py --n 5 --segment x1,y1,x2,y2
    python find_iet.py --n 5  # Uses default E'E segment
    python find_iet.py --n 10 --segment -0.5,0.363271264,0.5,-0.363271264
"""

import numpy as np
import argparse
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass


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


class GGGroup:
    """GG(n,n) compound symmetry group with centers at (-1,0) and (1,0)."""

    def __init__(self, n: int):
        self.n = n
        self.theta = -2 * np.pi / n  # Negative = clockwise (matches Lean convention)
        self.center_a = np.array([-1., 0.])
        self.center_b = np.array([1., 0.])

    def rotate(self, point: np.ndarray, center: np.ndarray, power: int) -> np.ndarray:
        """Rotate point about center by power * theta."""
        angle = power * self.theta
        c, s = np.cos(angle), np.sin(angle)
        d = point - center
        return center + np.array([c*d[0] - s*d[1], s*d[0] + c*d[1]])

    def apply_word(self, point: np.ndarray, word: List[Tuple[str, int]]) -> np.ndarray:
        """Apply a group word to a point. Word is list of ('a', power) or ('b', power)."""
        result = point.copy()
        for gen, power in word:
            center = self.center_a if gen == 'a' else self.center_b
            result = self.rotate(result, center, power)
        return result

    def word_to_string(self, word: List[Tuple[str, int]]) -> str:
        """Convert word to readable string like 'a^2b^-1a'."""
        parts = []
        for gen, power in word:
            if power == 1:
                parts.append(gen)
            elif power == -1:
                parts.append(f"{gen}⁻¹")
            else:
                parts.append(f"{gen}^{power}")
        return ''.join(parts)


def get_default_segment(n: int) -> Segment:
    """Get the default E'E segment for given n."""
    zeta = np.exp(2j * np.pi / n)
    E = zeta - zeta**2
    return Segment(
        start=np.array([-E.real, -E.imag]),
        end=np.array([E.real, E.imag])
    )


def generate_words(n: int, max_depth: int, alternating: bool = True) -> List[List[Tuple[str, int]]]:
    """Generate group words up to given depth."""
    words = []
    max_power = n // 2 + 1
    powers = [p for p in range(-max_power, max_power + 1) if p != 0]

    def extend(word: List[Tuple[str, int]], depth: int):
        if depth == 0:
            if word:
                words.append(word)
            return

        # Determine which generators to try
        if alternating and word:
            last_gen = word[-1][0]
            gens = ['b'] if last_gen == 'a' else ['a']
        else:
            gens = ['a', 'b']

        for gen in gens:
            for power in powers:
                extend(word + [(gen, power)], depth - 1)

    for depth in range(1, max_depth + 1):
        for start_gen in ['a', 'b']:
            for start_power in powers:
                extend([(start_gen, start_power)], depth - 1)

    return words


def find_segment_mappings(group: GGGroup, segment: Segment, max_depth: int = 5,
                          tol: float = 0.01, verbose: bool = True) -> List[Dict]:
    """
    Find all group words that map the segment (approximately) to itself.

    Returns list of dicts with word info and mapping parameters.
    """
    results = []

    # Sample points along segment
    num_samples = 50
    t_samples = np.linspace(0, 1, num_samples)
    sample_points = [segment.from_t(t) for t in t_samples]

    words = generate_words(group.n, max_depth, alternating=True)

    if verbose:
        print(f"Testing {len(words)} words up to depth {max_depth}...")

    for word in words:
        # Map sample points
        mapped_points = [group.apply_word(p, word) for p in sample_points]
        mapped_ts = [segment.to_t(p) for p in mapped_points]
        perp_dists = [segment.perp_distance(p) for p in mapped_points]

        max_perp = max(perp_dists)

        # Check if mapped points stay on segment line
        if max_perp < tol:
            t_start, t_end = mapped_ts[0], mapped_ts[-1]
            t_min, t_max = min(mapped_ts), max(mapped_ts)

            # Record this transformation
            result = {
                'word': word,
                'word_str': group.word_to_string(word),
                'depth': len(word),
                't_start': t_start,
                't_end': t_end,
                't_range': (t_min, t_max),
                'max_perp_error': max_perp,
                'is_identity': abs(t_start) < 0.01 and abs(t_end - 1) < 0.01,
                'maps_within_unit': t_min >= -0.1 and t_max <= 1.1,
                'reverses': t_end < t_start
            }
            results.append(result)

    return results


def analyze_iet_structure(results: List[Dict], verbose: bool = True) -> Dict:
    """
    Analyze results to find IET partition and permutation.

    For an IET, we look for words where:
    - The image [t_start, t_end] overlaps with [0, 1]
    - The word maps a portion of [0,1] to another portion of [0,1]
    """
    # Filter to transformations that OVERLAP with [0,1] (not just fully contained)
    iet_candidates = []
    for r in results:
        if r['is_identity']:
            continue
        t_min, t_max = r['t_range']
        # Check if image overlaps with [0,1]
        if t_max > 0 and t_min < 1:
            # Calculate which portion of domain maps to [0,1]
            # If word maps [0,1] to [t_start, t_end], then
            # the domain [d0, d1] maps to [0,1] where:
            # d0 = (0 - t_start) / (t_end - t_start)
            # d1 = (1 - t_start) / (t_end - t_start)
            t_start, t_end = r['t_start'], r['t_end']
            if abs(t_end - t_start) > 0.001:  # Avoid division by zero
                slope = t_end - t_start
                d0 = max(0, (0 - t_start) / slope)
                d1 = min(1, (1 - t_start) / slope)
                if d1 > d0:  # Valid domain portion
                    r['domain_portion'] = (d0, d1)
                    r['image_portion'] = (max(0, t_start + slope * d0), min(1, t_start + slope * d1))
                    iet_candidates.append(r)

    if verbose:
        print(f"\nFound {len(iet_candidates)} transformations overlapping [0,1]")

    # Group by the image portion (where in [0,1] does this map TO)
    by_image = {}
    for r in iet_candidates:
        if 'image_portion' in r:
            key = (round(r['image_portion'][0], 3), round(r['image_portion'][1], 3))
            if key not in by_image:
                by_image[key] = []
            by_image[key].append(r)

    if verbose:
        print("\nTransformations by image portion (where they map TO in [0,1]):")
        for img, items in sorted(by_image.items()):
            # Show shortest word first
            items_sorted = sorted(items, key=lambda x: x['depth'])
            print(f"  Image [{img[0]:.4f}, {img[1]:.4f}]:")
            for item in items_sorted[:3]:
                d = item.get('domain_portion', (0, 1))
                print(f"    {item['word_str']:25s} from domain [{d[0]:.4f}, {d[1]:.4f}]")

    return {
        'candidates': iet_candidates,
        'by_image': by_image
    }


def main():
    parser = argparse.ArgumentParser(description='Find IET group words')
    parser.add_argument('--n', type=int, required=True, help='Order of rotation group')
    parser.add_argument('--segment', type=str, help='Segment endpoints: x1,y1,x2,y2')
    parser.add_argument('--depth', type=int, default=5, help='Maximum word depth')
    parser.add_argument('--tol', type=float, default=0.01, help='Tolerance for segment mapping')
    parser.add_argument('--all', action='store_true', help='Show all results')
    args = parser.parse_args()

    # Parse segment or use default
    if args.segment:
        coords = [float(x) for x in args.segment.split(',')]
        segment = Segment(
            start=np.array([coords[0], coords[1]]),
            end=np.array([coords[2], coords[3]])
        )
    else:
        segment = get_default_segment(args.n)

    print(f"GG({args.n},{args.n}) IET Word Search")
    print("=" * 50)
    print(f"Rotation centers: (-1, 0) and (1, 0)")
    print(f"Segment: ({segment.start[0]:.6f}, {segment.start[1]:.6f}) to ({segment.end[0]:.6f}, {segment.end[1]:.6f})")
    print(f"Length: {segment.length:.6f}")
    print(f"Max depth: {args.depth}")
    print()

    group = GGGroup(args.n)
    results = find_segment_mappings(group, segment, max_depth=args.depth, tol=args.tol)

    print(f"\nFound {len(results)} transformations mapping segment to itself")

    if args.all:
        print("\nAll transformations:")
        for r in sorted(results, key=lambda x: (x['depth'], x['t_range'])):
            status = "IDENTITY" if r['is_identity'] else ("IN [0,1]" if r['maps_within_unit'] else "outside")
            print(f"  {r['word_str']:25s} [{r['t_start']:7.4f}, {r['t_end']:7.4f}] {status}")

    # Look for IET partition
    print("\n" + "=" * 50)
    print("IET Analysis")
    print("=" * 50)

    analysis = analyze_iet_structure(results)

    # Summarize potential IET
    if analysis['by_image']:
        print("\n--- Potential IET Partition ---")
        print("Looking for words that partition [0,1] and permute intervals...")

        # Find the shortest words for each distinct image portion
        best_words = {}
        for r in analysis['candidates']:
            if 'domain_portion' in r:
                d0, d1 = r['domain_portion']
                key = (round(d0, 3), round(d1, 3))
                if key not in best_words or r['depth'] < best_words[key]['depth']:
                    best_words[key] = r

        print("\nShortest words for each domain portion:")
        for (d0, d1), r in sorted(best_words.items()):
            img = r.get('image_portion', (0, 1))
            print(f"  [{d0:.4f}, {d1:.4f}] -> [{img[0]:.4f}, {img[1]:.4f}]  by  {r['word_str']}")


if __name__ == '__main__':
    main()
