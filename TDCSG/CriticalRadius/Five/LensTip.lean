/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.Complex.Basic

/-!
# The lens stays left of `κ - 2η`

The proof of the lens estimate (`TDCSG.Five.div_two_lt_norm_sub_of_le_re`) gives more than the
estimate states: for every radius `r`, every point `v` within `r / 2` of both `0` and a unit vector
`u` of real part `(φ - 1) / 2` has real part at most `(2φ + 1) / 4 - (3 + φ - r²) / 8`, that is
`κ - 2η` with `κ = (2φ + 1) / 4` and `η = (3 + φ - r²) / 16`. Below the critical radius `η > 0`,
so the lens, its tip included, stays at least `η` left of the line `Re v = κ - η`; at the critical
radius the bound is `κ`.

## Main statements

* `TDCSG.Five.re_le_of_mem_lens`: the bound.
-/

@[expose] public section

open Complex
open scoped goldenRatio

namespace TDCSG.Five

/-- **The lens stays left of `κ - 2η`.** If `u` is a unit vector with real part `(φ - 1) / 2` and
`v` lies within `r / 2` of both `0` and `u`, then
`Re v ≤ (2φ + 1) / 4 - (3 + φ - r²) / 8`. -/
theorem re_le_of_mem_lens {r : ℝ} {u v : ℂ} (hu : ‖u‖ = 1) (hre : u.re = (φ - 1) / 2)
    (hv : ‖v‖ ≤ r / 2) (hvu : ‖v - u‖ ≤ r / 2) :
    v.re ≤ (2 * φ + 1) / 4 - (3 + φ - r ^ 2) / 8 := by
  have hφ := Real.goldenRatio_sq
  have hlen := sq_norm_sub_sq_re u
  rw [hu, hre] at hlen
  have h₁ : v.re ^ 2 + v.im ^ 2 ≤ (r / 2) ^ 2 := by
    linarith [sq_norm_sub_sq_re v, pow_le_pow_left₀ (norm_nonneg _) hv 2]
  have h₂ : (v.re - u.re) ^ 2 + (v.im - u.im) ^ 2 ≤ (r / 2) ^ 2 := by
    rw [← sub_re, ← sub_im]
    linarith [sq_norm_sub_sq_re (v - u), pow_le_pow_left₀ (norm_nonneg _) hvu 2]
  -- Compare with `v* = 1 + t u`: a convex combination of the two disk inequalities, plus
  -- `|v - v*|² ≥ 0`, leaves a bound on `Re v` alone.
  let t : ℝ := 1 / 2 - (φ - 1) / 2
  have ht : 0 ≤ t := by simp only [t]; linarith [Real.goldenRatio_lt_two]
  have ht' : 0 ≤ 1 - t := by simp only [t]; linarith [Real.one_lt_goldenRatio]
  have hcomb := add_nonneg (mul_nonneg ht' (sub_nonneg.mpr h₁))
    (mul_nonneg ht (sub_nonneg.mpr h₂))
  have hsq := add_nonneg (sq_nonneg (v.re - (1 + t * u.re))) (sq_nonneg (v.im - t * u.im))
  rw [hre] at hcomb hsq
  have heq : (1 - t) * ((r / 2) ^ 2 - (v.re ^ 2 + v.im ^ 2)) +
      t * ((r / 2) ^ 2 - ((v.re - (φ - 1) / 2) ^ 2 + (v.im - u.im) ^ 2)) +
      ((v.re - (1 + t * ((φ - 1) / 2))) ^ 2 + (v.im - t * u.im) ^ 2) =
      (r / 2) ^ 2 - 2 * v.re + 1 + 2 * t * ((φ - 1) / 2) +
        (t ^ 2 - t) * (((φ - 1) / 2) ^ 2 + u.im ^ 2) := by
    ring
  rw [show ((φ - 1) / 2) ^ 2 + u.im ^ 2 = 1 by linarith] at heq
  simp only [t] at heq hcomb hsq
  nlinarith only [heq, hcomb, hsq, hφ]

end TDCSG.Five

end
