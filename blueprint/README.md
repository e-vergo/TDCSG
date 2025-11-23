# TDCSG Blueprint

This blueprint documents the formal verification of the critical radius theorem for two-disk compound symmetry groups.

## Current Status

✅ **Blueprint Created Successfully**
- LaTeX source with 80+ theorems, lemmas, definitions, and axioms
- HTML output generated at `blueprint/web/index.html`
- Complete dependency annotations using `\uses{}` commands
- All major results documented with Lean declaration names

## Structure

The blueprint covers:

1. **Main Theorem** (GG5_infinite_at_critical_radius)
2. **Foundations**
   - Critical radius definition and properties
   - Fifth roots of unity (ζ₅)
   - Geometric points (E, E', F, G)
   - Segment structure and golden ratio
3. **Two-Disk System**
   - Generators and isometries
   - Disk preservation properties
4. **Segment Maps** (map1, map2, map3)
   - Endpoint mappings
   - Bijection proofs
5. **Interval Exchange Transformation**
   - IET structure with golden ratio lengths
   - Irrationality proofs
6. **Orbit Theory**
   - Finite orbit characterization
   - Keane's theorem application
   - Infinite orbit existence

## Viewing the Blueprint

### Local Web Server
```bash
cd /Users/eric/Documents/GitHub/TDCSG/blueprint/web
python3 -m http.server 8080
# Visit http://localhost:8080
```

### Current Limitations

1. **Math Rendering**: Mathematical symbols show as broken image links because:
   - PlasTeX tried to generate images via pdflatex (failed)
   - MathJax configuration needs to be added to the HTML template

2. **Dependency Graph**: Not yet visualized because:
   - Requires additional plastexdepgraph post-processing
   - Graph visualization typically generated separately from main HTML

## Files

- `src/content.tex` - Main blueprint content (theorems, definitions, dependencies)
- `src/web.tex` - Web version wrapper with blueprint package
- `src/print.tex` - Print version wrapper
- `src/plastex.cfg` - PlasTeX configuration
- `src/blueprint.py` - Blueprint package Python plugin
- `src/blueprint.sty` - Blueprint LaTeX style file
- `web/index.html` - Generated HTML blueprint (52KB, 351 lines)

## Next Steps

### To Fix Math Rendering
Add MathJax to the HTML template or configure PlasTeX to use MathJax instead of images.

### To Generate Dependency Graph
Run the plastexdepgraph post-processor:
```bash
# This typically requires additional configuration
# Graph generation may need custom scripting
```

### Alternative: Use Lake importGraph
For file-level dependencies:
```bash
cd /Users/eric/Documents/GitHub/TDCSG
lake exe graph
```

## Axioms Summary

The formalization uses 7 axioms, all documented in the blueprint:

**Computational (5)**:
- `map1_new_z1_in_left_disk` through `map1_new_z4_in_right_disk`
- `lens_intersection_preserved_by_rotation`

**Ergodic Theory (2)**:
- `IET_irrational_rotation_no_periodic_orbits` (Keane 1975)
- `IET_maps_to_self`

## Build Commands

```bash
# Generate web version
cd /Users/eric/Documents/GitHub/TDCSG
leanblueprint web

# Generate PDF version (requires LaTeX)
leanblueprint pdf

# Generate both and check declarations
leanblueprint all
```
