import TDCSG.Basic
import TDCSG.Properties
import TDCSG.Composition
import TDCSG.MeasurePreserving
import TDCSG.Ergodic
import TDCSG.Finite
import TDCSG.IntervalExchange
import TDCSG.Examples

/-!
# Piecewise Isometries - Main Module

This is the main entry point for the piecewise isometries formalization.
Import this file to get access to the complete piecewise isometry API.

## Module Organization

- `TDCSG.Basic`: Core definitions (PiecewiseIsometry structure, CoeFun, discontinuitySet)
- `TDCSG.Properties`: Basic properties and lemmas about partitions and isometries
- `TDCSG.Composition`: Composition and iteration of piecewise isometries
- `TDCSG.MeasurePreserving`: Measure-preserving piecewise isometries and measure theory
- `TDCSG.Ergodic`: Ergodic piecewise isometries and ergodic theory connections
- `TDCSG.Finite`: Finite partition specializations
- `TDCSG.IntervalExchange`: Interval exchange transformations
- `TDCSG.Examples`: Concrete examples and construction patterns

## Quick Start

```lean
import TDCSG

-- Define a simple piecewise isometry
def myPI : PiecewiseIsometry ℝ := PiecewiseIsometry.id

-- Work with interval exchange transformations
def myIET : IntervalExchangeTransformation 2 := ...

-- Convert to piecewise isometry
def myPI_from_IET : PiecewiseIsometry ℝ := myIET.toPiecewiseIsometry
```

-/
