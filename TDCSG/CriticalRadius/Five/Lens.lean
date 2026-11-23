/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.Complex.Basic

/-!
# The lens estimate

This is Lemma 2 of `notes/proofs/sharp-lower-bound-n5-pentagrid.md`. Write `R = r / 2`,
`c = cos (2π / 5) = (φ - 1) / 2`, `d = cos (4π / 5) = -φ / 2`, `L = c - d = φ - 1 / 2` and
`a = (1 + L) / 2 = (2φ + 1) / 4`. Below the critical radius `√(3 + φ)`, a point `v` of the disk of
radius `R` about `0` whose real part is close to `a` lies farther than `R` from each of the four
other fifth roots of unity `u = ζ^{±1}, ζ^{±2}`: the lens of points within `R` of both `0` and `u`
does not reach real part `a - η`, where `η = (3 + φ - r²) / 16`.

## Main statements

* `TDCSG.Five.lens`: the lens estimate.
-/

@[expose] public section

open Complex
open scoped goldenRatio

namespace TDCSG.Five

/-- **The lens estimate.** Let `0 ≤ r < √(3 + φ)` and let `u` be a unit vector with real part
`(φ - 1) / 2` or `-φ / 2`. If `|v| ≤ r / 2` and `Re v ≥ (2φ + 1) / 4 - (3 + φ - r²) / 16`, then
`|v - u| > r / 2`. -/
theorem lens {r : ℝ} (hr : 0 ≤ r) (hc : r < √(3 + φ)) {u v : ℂ} (hu : ‖u‖ = 1)
    (hre : u.re = (φ - 1) / 2 ∨ u.re = -φ / 2) (hv : ‖v‖ ≤ r / 2)
    (hx : (2 * φ + 1) / 4 - (3 + φ - r ^ 2) / 16 ≤ v.re) : r / 2 < ‖v - u‖ := by
  by_contra! hnear
  have hφ := Real.goldenRatio_sq
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hr2 := (Real.lt_sqrt hr).1 hc
  rcases hre with h | h
  · -- The lens is symmetric about the bisector of `0` and `u`; compare with its tip
    -- `1 + t u`, which has real part `(2φ + 1) / 4` and lies at distance `√(3 + φ) / 2`
    -- from both `0` and `u`.
    have hnorm (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, normSq_apply]
      ring
    have hlen := hnorm u
    rw [hu, h] at hlen
    have h₁ : v.re ^ 2 + v.im ^ 2 ≤ (r / 2) ^ 2 := by
      rw [← hnorm]
      exact pow_le_pow_left₀ (norm_nonneg _) hv _
    have h₂ : (v.re - u.re) ^ 2 + (v.im - u.im) ^ 2 ≤ (r / 2) ^ 2 := by
      rw [← sub_re, ← sub_im, ← hnorm]
      exact pow_le_pow_left₀ (norm_nonneg _) hnear _
    let t : ℝ := 1 / 2 - (φ - 1) / 2
    have ht : 0 ≤ t := by simp only [t]; linarith
    have ht' : 0 ≤ 1 - t := by simp only [t]; linarith
    have hcomb := add_nonneg (mul_nonneg ht' (sub_nonneg.mpr h₁))
      (mul_nonneg ht (sub_nonneg.mpr h₂))
    have hsq := add_nonneg (sq_nonneg (v.re - (1 + t * u.re))) (sq_nonneg (v.im - t * u.im))
    rw [h] at hcomb hsq
    have heq : (1 - t) * ((r / 2) ^ 2 - (v.re ^ 2 + v.im ^ 2)) +
        t * ((r / 2) ^ 2 - ((v.re - (φ - 1) / 2) ^ 2 + (v.im - u.im) ^ 2)) +
        ((v.re - (1 + t * ((φ - 1) / 2))) ^ 2 + (v.im - t * u.im) ^ 2) =
        (r / 2) ^ 2 - 2 * v.re + 1 + 2 * t * ((φ - 1) / 2) +
          (t ^ 2 - t) * (((φ - 1) / 2) ^ 2 + u.im ^ 2) := by
      ring
    rw [show ((φ - 1) / 2) ^ 2 + u.im ^ 2 = 1 by linarith] at heq
    simp only [t] at heq hcomb hsq
    nlinarith only [heq, hcomb, hsq, hx, hφ, hr2]
  · -- Points within `r / 2` of `u` have real part at most `r / 2 - φ / 2`.
    have hreal := (Complex.re_le_norm (v - u)).trans hnear
    rw [sub_re, h] at hreal
    nlinarith [sq_nonneg r]

end TDCSG.Five

end
