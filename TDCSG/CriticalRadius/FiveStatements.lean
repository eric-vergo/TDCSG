/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.Five

/-! # Endpoint infinitude and the fivefold critical-radius statement -/

@[expose] public section

open scoped Real goldenRatio

namespace TDCSG.CriticalRadius

/-- `GG₅(r)` is infinite for every `r ≥ √(3 + φ)` (`critical-radius-n5.md`, Theorem A). -/
theorem infinite_GG_five {r : ℝ} (hr : √(3 + φ) ≤ r) : Infinite (GG 5 5 r r) :=
  Five.infinite_GG hr

/-- For every `r ≥ √(3 + φ)` the orbit of `0` under `GG₅(r)` is infinite. -/
theorem infinite_orbit_zero_five {r : ℝ} (hr : √(3 + φ) ≤ r) : (orbit 5 5 r r 0).Infinite :=
  Five.infinite_orbit_zero hr

theorem criticalRadius_five_le : criticalRadius 5 ≤ √(3 + φ) :=
  Five.criticalRadius_le

theorem one_le_criticalRadius_five : 1 ≤ criticalRadius 5 :=
  TDCSG.one_le_criticalRadius ⟨_, Five.infinite_GG le_rfl⟩

/-- Subcritical finiteness for fivefold rotations, proved in `FiveSharp`. -/
def FiniteBelowClosedFormFive : Prop :=
  ∀ r : ℝ, r < √(3 + φ) → Finite (GG 5 5 r r)

/-- The fivefold critical-radius equality, proved as `criticalRadius_five_eq` in `FiveSharp`. -/
def CriticalRadiusEqFive : Prop := criticalRadius 5 = √(3 + φ)

/-- Finiteness below the closed form `√(3 + φ)`, with the infinitude at and above it
(`infinite_GG_five`), gives the exact value of the critical radius. -/
theorem criticalRadiusEqFive_of_finiteBelowClosedFormFive (h : FiniteBelowClosedFormFive) :
    CriticalRadiusEqFive := by
  refine le_antisymm criticalRadius_five_le (le_csInf ⟨_, Five.infinite_GG le_rfl⟩ fun r hr ↦ ?_)
  by_contra hlt
  exact not_finite_iff_infinite.2 hr (h r (not_le.1 hlt))

end TDCSG.CriticalRadius
