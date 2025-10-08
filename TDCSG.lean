/-
# Two-Disk Compound Symmetry Groups - Main Import File

This is the main entry point for the TDCSG formalization project.
The project is organized in 5 layers:

1. **Core**: Basic definitions and mathematical objects
2. **Theory**: Mathematical theory and proofs
3. **Tools**: Computational and helper tools
4. **Analysis**: Specific analysis and properties
5. **Theorems**: Main theorem statements and proofs

## Import Structure
-/

-- Layer 1: Core definitions
import TDCSG.Core.Basic
import TDCSG.Core.Complex
import TDCSG.Core.Constants

-- Layer 2: Theory
import TDCSG.Theory.GroupAction
import TDCSG.Theory.IsometrySimple
import TDCSG.Theory.Pentagon

-- Layer 3: Tools
import TDCSG.Tools.FreeGroup
import TDCSG.Tools.ComplexNormSimple
import TDCSG.Tools.Density

-- Layer 4: Analysis
import TDCSG.Analysis.GG5Properties
import TDCSG.Analysis.Translations

-- Layer 5: Main Theorems
import TDCSG.Theorems.Theorem1
import TDCSG.Theorems.Theorem2

/-!
## Project Overview

This formalization proves **Theorem 2** from "Two-Disk Compound Symmetry Groups":
GG₅ (5-fold rotational symmetry on both disks) has an infinite group at the
critical radius r = √(3 + φ) where φ is the golden ratio.

## Key Results

- **Theorem 1**: Characterizes when two-disk groups are finite (crystallographic restriction)
- **Theorem 2**: Proves GG₅ is infinite at the critical radius using dense orbit arguments

## Architecture Benefits

The 5-layer architecture provides:
- Clear separation of concerns
- No circular dependencies
- Reusable components
- Easy navigation
- Parallel development capability

-/
