# TDCSG Analysis Scripts

This directory contains tools for analyzing the TDCSG formal verification codebase.

## Dead Code Analysis

Identifies unreachable declarations that are not used by the main theorem proof.

### Quick Start

Run the complete analysis workflow:

```bash
./scripts/analyze_dead_code.sh
```

This will:
1. Trace dependencies from the main theorem
2. Identify unreachable declarations
3. Check for `@[simp]` attributes (dangerous to delete)
4. Generate comprehensive reports

### Generated Reports

- **docs/dead_code_analysis.md** - Human-readable report with:
  - Summary statistics
  - Safety warnings
  - Declarations grouped by file with line numbers
  - Recommendations for safe deletion

- **docs/dead_code.txt** - Simple list format for programmatic processing

- **docs/dead_code_safety.txt** - Critical list of `@[simp]` declarations that **MUST NOT** be deleted

### Manual Usage

Run individual components:

```bash
# 1. Run Lean dead code analyzer
lake exe find_dead_code

# 2. Check for @[simp] attributes
python3 scripts/check_simp_attrs.py
```

### Key Features

- **Auto-generated code filtering**: Excludes modules like `TDCSG.CompoundSymmetry.GG5`
- **Compiler artifact filtering**: Ignores `._proof`, `inst*`, and other generated declarations
- **@[simp] detection**: Python script reads source files to identify dangerous deletions
- **Line numbers**: All reports include exact file locations

### Before Deleting Code

1. Review `docs/dead_code_safety.txt` for `@[simp]` declarations
2. Manually verify the declaration is truly unused
3. After deletion, always run:
   ```bash
   lake build && lake env lean --run KMVerify/Main.lean
   ```

## Dependency Graph Tools

Generate visual dependency graphs:

```bash
./scripts/build_dep_graph.sh
```

Outputs:
- `docs/deps.dot` - GraphViz DOT format
- `docs/deps_static.svg` - Static SVG visualization
- `docs/dep_graph.html` - Interactive HTML graph (searchable, zoomable)
