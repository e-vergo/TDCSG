import TDCSG.Definitions.Geometry
import TDCSG.Definitions.GroupAction
import Mathlib.Algebra.Group.Subgroup.Lattice

open Real Complex
open scoped Circle
open TDCSG.Definitions (leftDisk rightDisk leftCenter rightCenter rotateAboutC
  genA_n genB_n genA_n_bijective genB_n_bijective r_crit φ)

noncomputable def genA_n_perm (n : ℕ) (hn : n ≥ 1) (r : ℝ) : Equiv.Perm ℂ :=
  Equiv.ofBijective (genA_n n r) (genA_n_bijective n hn r)

noncomputable def genB_n_perm (n : ℕ) (hn : n ≥ 1) (r : ℝ) : Equiv.Perm ℂ :=
  Equiv.ofBijective (genB_n n r) (genB_n_bijective n hn r)

noncomputable def TwoDiskCompoundSymmetryGroup (n : ℕ) (hn : n ≥ 1) (r : ℝ) :
    Subgroup (Equiv.Perm ℂ) :=
  Subgroup.closure {genA_n_perm n hn r, genB_n_perm n hn r}

noncomputable def GG5_At_Critical_radius : Subgroup (Equiv.Perm ℂ) :=
  TwoDiskCompoundSymmetryGroup 5 (by norm_num) r_crit

def StatementOfTheorem : Prop :=
  Infinite GG5_At_Critical_radius
