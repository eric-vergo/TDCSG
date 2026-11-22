/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.Five

/-! # The transverse lens estimate for a pair of fivefold centers -/

@[expose] public section

open Complex
open scoped goldenRatio

namespace TDCSG.Five.Walls

/-- Real part of a unit direction one fifth-turn away. -/
noncomputable abbrev nearCosine : ℝ := (φ - 1) / 2

/-- Real part of a unit direction two fifth-turns away. -/
noncomputable abbrev farCosine : ℝ := -φ / 2

/-- Distance between consecutive transverse phases. -/
noncomputable abbrev phaseSpacing : ℝ := nearCosine - farCosine

/-- Axial support at the critical lens. -/
noncomputable abbrev axialSupport : ℝ := (1 + phaseSpacing) / 2

/-- Near the outer axial support of the lens, every nonaxial neighbor misses the window. -/
theorem lens {r : ℝ} (hr : 0 ≤ r) (hc : r < √(3 + φ)) {v u : ℂ}
    (hu : ‖u‖ = 1) (hre : u.re = nearCosine ∨ u.re = farCosine)
    (hv : ‖v‖ ≤ r / 2)
    (hx : axialSupport - (3 + φ - r ^ 2) / 16 ≤ v.re) : r / 2 < ‖v - u‖ := by
  by_contra! hnear
  have hφ := Real.goldenRatio_sq
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hr2 := (Real.lt_sqrt hr).1 hc
  rcases hre with h | h
  · let t := 1 / 2 - nearCosine
    have ht : 0 ≤ t := by dsimp [t, nearCosine]; linarith
    have ht' : 0 ≤ 1 - t := by dsimp [t, nearCosine]; linarith
    have hnorm (w : ℂ) : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; ring
    have hlen := hnorm u
    rw [hu, h] at hlen
    have h₁ : v.re ^ 2 + v.im ^ 2 ≤ (r / 2) ^ 2 := by
      rw [hnorm]; exact pow_le_pow_left₀ (norm_nonneg _) hv _
    have h₂ : (v.re - u.re) ^ 2 + (v.im - u.im) ^ 2 ≤ (r / 2) ^ 2 := by
      change (v - u).re ^ 2 + (v - u).im ^ 2 ≤ _
      rw [hnorm]; exact pow_le_pow_left₀ (norm_nonneg _) hnear _
    have hcomb := add_nonneg (mul_nonneg ht' (sub_nonneg.mpr h₁))
      (mul_nonneg ht (sub_nonneg.mpr h₂))
    have hsq := add_nonneg (sq_nonneg (v.re - (1 + t * u.re))) (sq_nonneg (v.im - t * u.im))
    rw [h] at hcomb hsq
    have heq : (1 - t) * ((r / 2) ^ 2 - (v.re ^ 2 + v.im ^ 2)) +
        t * ((r / 2) ^ 2 - ((v.re - nearCosine) ^ 2 + (v.im - u.im) ^ 2)) +
        ((v.re - (1 + t * nearCosine)) ^ 2 + (v.im - t * u.im) ^ 2) =
        (r / 2) ^ 2 - 2 * v.re + 1 + 2 * t * nearCosine +
          (t ^ 2 - t) * (nearCosine ^ 2 + u.im ^ 2) := by ring
    rw [show nearCosine ^ 2 + u.im ^ 2 = 1 by linarith] at heq
    dsimp [t, axialSupport, phaseSpacing, nearCosine, farCosine] at heq hcomb hsq hx
    nlinarith only [heq, hcomb, hsq, hx, hφ, hr2]
  · have hreal := (Complex.re_le_norm (v - u)).trans hnear
    rw [sub_re, h] at hreal
    dsimp [axialSupport, phaseSpacing, nearCosine, farCosine] at hx hreal
    nlinarith [sq_nonneg r]

end TDCSG.Five.Walls
