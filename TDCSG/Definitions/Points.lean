import TDCSG.Definitions.Geometry
import Mathlib.NumberTheory.Real.GoldenRatio

namespace TDCSG.Definitions

open Complex Real

noncomputable def E : ℂ := ζ₅^4 - ζ₅^3

noncomputable def E' : ℂ := -E

noncomputable def F : ℂ := 1 - ζ₅^4 + ζ₅^3 - ζ₅^2

noncomputable def G : ℂ := 2 * F - E

noncomputable abbrev psi : ℝ := -Real.goldenConj

noncomputable def t_F : ℝ := (1 + Real.sqrt 5) / 4

noncomputable abbrev t_G : ℝ := psi

noncomputable def segmentPoint (t : ℝ) : ℂ := E' + t • (E - E')

noncomputable def translation_length_1 : ℝ := ‖F - (-F)‖

noncomputable def translation_length_2 : ℝ := ‖E - G‖

noncomputable def segment_length : ℝ := ‖E - E'‖

end TDCSG.Definitions
