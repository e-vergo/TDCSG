import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.DenseEmbedding

-- Scratch file to explore available lemmas for ergodic_of_minimal

open MeasureTheory

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
variable (μ : Measure α) [IsProbabilityMeasure μ]

-- Check what we have about Dense sets
#check Dense
#check Dense.exists_mem_open
#check DenseRange.exists_mem_open

-- Check outer regularity
#check Measure.OuterRegular
#check Measure.OuterRegular.outerRegular
#check Measure.WeaklyRegular

-- Try full path
variable [Measure.WeaklyRegular μ]

-- Check ergodicity
#check Ergodic
#check PreErgodic.measure_self_or_compl_eq_zero

-- Check measure preservation
#check MeasurePreserving
#check MeasurePreserving.measure_preimage

-- Check if we can find approximation lemmas
-- #check exists_isOpen_le_measure

-- Check ENNReal lemmas
#check ENNReal.pos_iff_ne_zero
#check ENNReal.zero_lt_iff_ne_zero
