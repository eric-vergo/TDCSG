/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.Five

/-! # Integer labels for the centers of the fivefold disk rotations -/

@[expose] public section

namespace TDCSG.Five.Walls

/-- Integer coefficients of the five unit directions. -/
abbrev Label := Fin 5 → ℤ

/-- Moving to the other center in direction `j` adds this vector. -/
def basis (j : Fin 5) : Label := Pi.single j 1

/-- The unit direction indexed by `j`. -/
noncomputable def dir (j : Fin 5) : ℂ := zeta ^ j.val

/-- Physical projection of a center label. -/
noncomputable def proj (n : Label) : ℂ := ∑ j, (n j : ℂ) * dir j

/-- Sum of the coordinates, distinguishing the two kinds of centers. -/
def weight (n : Label) : ℤ := ∑ j, n j

/-- Projection is additive on integer labels. -/
theorem proj_add (n m : Label) : proj (n + m) = proj n + proj m := by
  simp [proj, add_mul, Finset.sum_add_distrib]

/-- A unit label projects to its indexed unit direction. -/
theorem proj_basis (j : Fin 5) : proj (basis j) = dir j := by
  classical
  simp [proj, basis, Pi.single_apply]

/-- A unit label has weight one. -/
theorem weight_basis (j : Fin 5) : weight (basis j) = 1 := by
  classical
  simp [weight, basis, Pi.single_apply]

/-- Each projected direction has unit length. -/
theorem norm_dir (j : Fin 5) : ‖dir j‖ = 1 := by
  simp [dir, norm_pow, norm_zeta]

/-- Adding a unit label increases its weight by one. -/
theorem weight_add_basis (n : Label) (k : Fin 5) :
    weight (n + basis k) = weight n + 1 := by
  classical
  simp [weight, basis, Pi.single_apply, Finset.sum_add_distrib]

end TDCSG.Five.Walls
