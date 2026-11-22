/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.FiveCenterBounds
public import TDCSG.CriticalRadius.FiveCenterOrbits
public import TDCSG.CriticalRadius.FiveWalls
public import TDCSG.CriticalRadius.FiveStatements

/-! # The exact critical radius for fivefold disk rotations -/

@[expose] public section

open scoped Real goldenRatio

namespace TDCSG.CriticalRadius

/-- Every fivefold group below the closed-form threshold is finite. -/
theorem finiteBelowClosedFormFive : FiniteBelowClosedFormFive := by
  intro r hr
  by_cases h : 0 ≤ r
  · have h4 : √(3 + φ) < 4 :=
      (Real.sqrt_lt' (by norm_num)).2 (by linarith [Real.goldenRatio_lt_two])
    exact Five.Walls.finite_GG_of_centerBox (hr.trans h4).le
      (Five.Walls.centerBox_of_walls (Five.Walls.exists_walls h hr))
  · exact TDCSG.finite_GG_of_lt_one 5 (by linarith)

/-- The critical radius for fivefold disk rotations is the square root of three plus φ. -/
theorem criticalRadius_five_eq : criticalRadius 5 = √(3 + φ) :=
  criticalRadiusEqFive_of_finiteBelowClosedFormFive finiteBelowClosedFormFive

/-- The closed-disk group is finite exactly on the open subcritical half-line. -/
theorem finite_GG_five_iff (r : ℝ) : Finite (GG 5 5 r r) ↔ r < √(3 + φ) := by
  refine ⟨fun h ↦ lt_of_not_ge fun hr ↦ ?_, finiteBelowClosedFormFive r⟩
  exact not_finite_iff_infinite.2 (infinite_GG_five hr) h

/-- The supremum of the finite radii in the paper equals the closed form. -/
theorem sSup_finiteRadii_five : sSup {r : ℝ | Finite (GG 5 5 r r)} = √(3 + φ) := by
  have h : {r : ℝ | Finite (GG 5 5 r r)} = Set.Iio √(3 + φ) :=
    Set.ext fun r ↦ finite_GG_five_iff r
  rw [h, csSup_Iio]

/-- The paper's supremum agrees with the library's infimum of the infinite radii. -/
theorem sSup_finiteRadii_eq_criticalRadius_five :
    sSup {r : ℝ | Finite (GG 5 5 r r)} = criticalRadius 5 :=
  sSup_finiteRadii_five.trans criticalRadius_five_eq.symm

end TDCSG.CriticalRadius
