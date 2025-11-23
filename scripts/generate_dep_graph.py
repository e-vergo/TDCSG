#!/usr/bin/env python3
r"""
Generate dependency graph from blueprint LaTeX file
Extracts \label{} and \uses{} to create GraphViz visualization
"""

import re
import sys
from pathlib import Path
from typing import Dict, Set, Tuple, List

def parse_blueprint(tex_file: Path) -> Tuple[Dict[str, Tuple[str, str]], Dict[str, Set[str]]]:
    """
    Parse blueprint LaTeX file to extract items and dependencies.

    Returns:
        (items, deps) where:
        - items: {label: (type, name)}
        - deps: {label: {dep1, dep2, ...}}
    """
    content = tex_file.read_text()

    items = {}  # label -> (type, name)
    deps = {}   # label -> set of dependencies

    # Pattern to match theorem environments with labels and uses
    # Match: \begin{theorem}[Name]\label{label} ... \uses{deps} ... \end{theorem}
    env_pattern = r'\\begin\{(theorem|lemma|definition|axiom)\}(?:\[(.*?)\])?\s*\\label\{(.*?)\}'
    uses_pattern = r'\\uses\{([^}]+)\}'

    for match in re.finditer(env_pattern, content, re.DOTALL):
        env_type = match.group(1)
        name = match.group(2) if match.group(2) else ""
        label = match.group(3)

        # Store item
        items[label] = (env_type, name)

        # Find uses in the rest of the environment
        start_pos = match.end()
        end_pattern = f'\\\\end{{{env_type}}}'
        end_match = re.search(end_pattern, content[start_pos:])

        if end_match:
            env_content = content[start_pos:start_pos + end_match.start()]
            uses_match = re.search(uses_pattern, env_content)

            if uses_match:
                # Parse comma-separated dependencies
                deps_str = uses_match.group(1)
                dep_labels = {d.strip() for d in deps_str.split(',')}
                deps[label] = dep_labels
            else:
                deps[label] = set()
        else:
            deps[label] = set()

    return items, deps


def generate_dot(items: Dict[str, Tuple[str, str]],
                 deps: Dict[str, Set[str]],
                 output_file: Path):
    """Generate GraphViz DOT file from dependencies."""

    # Color scheme
    colors = {
        'theorem': '#93c5fd',     # blue
        'lemma': '#86efac',       # green
        'definition': '#fde047',  # yellow
        'axiom': '#fca5a5'        # red
    }

    dot_lines = [
        'digraph Dependencies {',
        '  rankdir=TB;',
        '  node [shape=box, style="rounded,filled", fontname="Arial"];',
        '  edge [color="#64748b"];',
        ''
    ]

    # Add nodes
    for label, (item_type, name) in items.items():
        color = colors.get(item_type, '#e2e8f0')
        display_name = name if name else label
        # Escape quotes
        display_name = display_name.replace('"', '\\"')
        dot_lines.append(f'  "{label}" [label="{display_name}", fillcolor="{color}"];')

    dot_lines.append('')

    # Add edges
    for label, dep_set in deps.items():
        for dep in dep_set:
            if dep in items:  # Only add edge if dependency exists
                dot_lines.append(f'  "{dep}" -> "{label}";')

    # Add legend
    dot_lines.extend([
        '',
        '  // Legend',
        '  subgraph cluster_legend {',
        '    label="Legend";',
        '    style=filled;',
        '    fillcolor="#f8fafc";',
        '    node [shape=box, style="rounded,filled"];',
    ])

    for item_type, color in colors.items():
        dot_lines.append(f'    legend_{item_type} [label="{item_type.capitalize()}", fillcolor="{color}"];')

    dot_lines.extend([
        '  }',
        '}'
    ])

    output_file.write_text('\n'.join(dot_lines))


def generate_svg(dot_file: Path, svg_file: Path):
    """Generate SVG from DOT file using GraphViz."""
    import subprocess

    try:
        subprocess.run(
            ['dot', '-Tsvg', str(dot_file), '-o', str(svg_file)],
            check=True,
            capture_output=True
        )
        return True
    except FileNotFoundError:
        print("ERROR: GraphViz 'dot' command not found. Please install GraphViz:")
        print("  brew install graphviz")
        return False
    except subprocess.CalledProcessError as e:
        print(f"ERROR: Failed to generate SVG: {e.stderr.decode()}")
        return False


def main():
    # Paths
    project_root = Path(__file__).parent.parent
    blueprint_file = project_root / 'blueprint' / 'src' / 'content.tex'
    output_dir = project_root / 'blueprint' / 'web'
    output_dir.mkdir(parents=True, exist_ok=True)

    dot_file = output_dir / 'dep_graph.dot'
    svg_file = output_dir / 'dep_graph.svg'

    print(f"📖 Parsing blueprint: {blueprint_file}")

    if not blueprint_file.exists():
        print(f"ERROR: Blueprint file not found: {blueprint_file}")
        sys.exit(1)

    # Parse blueprint
    items, deps = parse_blueprint(blueprint_file)

    print(f"✓ Found {len(items)} items ({sum(len(d) for d in deps.values())} dependencies)")

    # Count by type
    type_counts = {}
    for item_type, _ in items.values():
        type_counts[item_type] = type_counts.get(item_type, 0) + 1

    for item_type, count in sorted(type_counts.items()):
        print(f"  - {item_type}: {count}")

    # Generate DOT file
    print(f"\n📊 Generating DOT file: {dot_file}")
    generate_dot(items, deps, dot_file)
    print(f"✓ Generated {dot_file}")

    # Generate SVG
    print(f"\n🎨 Generating SVG: {svg_file}")
    if generate_svg(dot_file, svg_file):
        print(f"✓ Generated {svg_file}")
        print(f"\n✅ Dependency graph created successfully!")
        print(f"   View at: {svg_file}")
    else:
        print(f"\n⚠️  SVG generation failed, but DOT file is available")
        print(f"   You can generate SVG manually with:")
        print(f"   dot -Tsvg {dot_file} -o {svg_file}")


if __name__ == '__main__':
    main()
