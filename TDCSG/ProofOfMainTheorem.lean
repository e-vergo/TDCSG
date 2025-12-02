import TDCSG.MainTheorem
import TDCSG.Proofs.GroupTheory

open TDCSG.Definitions TDCSG.CompoundSymmetry.GG5

theorem GG5_infinite_at_critical_radius : StatementOfTheorem := by

  obtain ⟨x₀, hx₀_mem, hx₀_inf⟩ := GG5_IET_has_infinite_orbit

  have h_word_inf : (orbit r_crit (segmentPoint x₀)).Infinite :=
    IET_orbit_infinite_implies_group_orbit_infinite x₀ hx₀_mem hx₀_inf

  rw [orbit_eq_groupOrbit] at h_word_inf

  exact infinite_orbit_implies_infinite_group (segmentPoint x₀) h_word_inf
