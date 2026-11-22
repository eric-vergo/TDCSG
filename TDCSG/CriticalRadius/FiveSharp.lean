/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.FiveCenterBounds
public import TDCSG.CriticalRadius.FiveCenterOrbits
public import TDCSG.CriticalRadius.FiveWalls
public import TDCSG.CriticalRadius.Statements

/-! # The exact critical radius for fivefold disk rotations -/

@[expose] public section

open scoped Real goldenRatio

namespace TDCSG.CriticalRadius

/-- Every fivefold group below the closed-form threshold is finite. -/
theorem finiteBelowClosedFormFive : FiniteBelowClosedFormFive := by
  intro r hr
  by_cases h : 0 ≤ r
  · have hφ : φ < 2 := by nlinarith [Real.goldenRatio_sq, Real.goldenRatio_pos]
    have h4 : √(3 + φ) < 4 := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
    exact Five.Walls.finite_GG_of_centerBox (hr.trans h4).le
      (Five.Walls.centerBox_of_walls (Five.Walls.exists_walls h hr))
  · exact finite_GG_of_lt_one 5 (by linarith)

/-- The critical radius for fivefold disk rotations is the square root of three plus φ. -/
theorem criticalRadius_five_eq : criticalRadius 5 = √(3 + φ) :=
  criticalRadiusEqFive_of_finiteBelowClosedFormFive finiteBelowClosedFormFive

end TDCSG.CriticalRadius
