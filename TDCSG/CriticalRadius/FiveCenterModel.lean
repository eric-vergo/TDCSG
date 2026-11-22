/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.FiveConjugate

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

end TDCSG.Five.Walls
