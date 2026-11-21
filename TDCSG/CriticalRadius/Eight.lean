/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TDCSG.CriticalRadius.Basic

/-!
# The critical point of `GG₈`

Base facts of Part A of `notes/proofs/critical-radius-n8.md`. The critical point is
`p* = 1 - 2ζ + ζ² - ζ³ = (1 - √2/2) - (3√2/2 - 1) i`, with `ζ = exp (2πi / 8)`.

## Main statements

* `TDCSG.Eight.dist_pStar_leftCenter_sq`: `|p* + 1|² = 10 - 5√2`, so `p*` lies on the boundary
  circle of the left disk exactly at the conjectured critical radius `√(10 - 5√2)`.
* `TDCSG.Eight.dist_pStar_rightCenter_sq`: `|p* - 1|² = 6 - 3√2`, so `p*` lies inside the right
  disk at that radius.
* `TDCSG.Eight.applyWord_seed`: the seed word `b b a b` maps `p*` to `p* + (4√2 - 4) i`, for every
  `r ≥ √(10 - 5√2)`; so this point lies in the orbit of `p*`.

## Implementation notes

The full Theorem A of the written note (the orbit of `p*` contains `p* + 4 i (√2 - 1)^(k+1)` for
all `k`) rests on a family of 31 words with domains whose end points involve
`√(19/2 - 5√2)`, and on 172 exact composition steps; it is stated, not proved, as
`TDCSG.CriticalRadius.InfiniteOrbitEight` in `TDCSG.CriticalRadius.Statements`.

The four disk tests of the seed at `p*` have squared distances `6 - 3√2`, `6 - 3√2`,
`14 - 9√2` and `22 - 15√2`, none of them equal to `10 - 5√2`; so the seed is valid at `p*` for
every `r ≥ √(6 - 3√2)`, whether or not `p*` lies in the left disk.
-/

@[expose] public section

open Complex Metric
open scoped Real

namespace TDCSG.Eight

/-- `√2`, as a real number. -/
local notation "s" => Real.sqrt 2

theorem sqrt_two_sq : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt_two_bounds : 1.414 < s ∧ s < 1.415 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- The rotation factor `exp (-2πi / 8) = (1 - i) / √2`. -/
theorem exp_rotationAngle_eight : exp (-(2 * π * I / (8 : ℕ))) = ⟨s / 2, -(s / 2)⟩ := by
  rw [show -(2 * π * I / (8 : ℕ)) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  apply Complex.ext <;> simp

/-- The rotation factor `exp (2πi / 8) = (1 + i) / √2`. -/
theorem exp_two_pi_I_div_eight : exp (2 * π * I / (8 : ℕ)) = ⟨s / 2, s / 2⟩ := by
  rw [show 2 * π * I / (8 : ℕ) = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  apply Complex.ext <;> simp

/-- The critical point `p* = 1 - 2ζ + ζ² - ζ³ = -1 + (2 + i)(1 - ζ)`. -/
noncomputable def pStar : ℂ := ⟨1 - s / 2, 1 - 3 * s / 2⟩

/-- `|p* + 1|² = 10 - 5√2`. -/
theorem dist_pStar_leftCenter_sq : dist pStar leftCenter ^ 2 = 10 - 5 * s := by
  rw [dist_sq_eq_re_im]
  simp only [pStar, leftCenter, neg_re, neg_im, one_re, one_im]
  linear_combination (5 / 2 : ℝ) * sqrt_two_sq

/-- `|p* - 1|² = 6 - 3√2`. -/
theorem dist_pStar_rightCenter_sq : dist pStar rightCenter ^ 2 = 6 - 3 * s := by
  rw [dist_sq_eq_re_im]
  simp only [pStar, rightCenter, one_re, one_im]
  linear_combination (5 / 2 : ℝ) * sqrt_two_sq

/-- At the radius `√(10 - 5√2)` the point `p*` lies on the boundary circle of the left disk. -/
theorem pStar_mem_sphere : pStar ∈ sphere leftCenter √(10 - 5 * s) := by
  rw [mem_sphere, ← dist_pStar_leftCenter_sq, Real.sqrt_sq dist_nonneg]

/-- The seed word `b b a b`. -/
def seed : List Letter := [.b, .b, .a, .b]

/-- The seed word `b b a b` maps `p*` to `p* + (4√2 - 4) i` for every `r ≥ √(10 - 5√2)`. -/
theorem applyWord_seed {r : ℝ} (hr : √(10 - 5 * s) ≤ r) :
    applyWord 8 r seed pStar = pStar + ((4 * s - 4 : ℝ) : ℂ) * I := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  have h2s := sqrt_two_sq
  have hr0 : 0 ≤ r := (Real.sqrt_nonneg _).trans hr
  have hr2 : 10 - 5 * s ≤ r ^ 2 := sq_le_of_sqrt_le (by linarith) hr
  have hA := exp_rotationAngle_eight
  have step (l : Letter) (z z' : ℂ) (hz : (z.re - l.center.re) ^ 2 + (z.im - l.center.im) ^ 2 ≤
      10 - 5 * s) (hz' : l.glob 8 z = z') : l.perm 8 r z = z' := by
    rw [Letter.perm_apply_of_mem (mem_closedBall_of_sq_le hr0 (hz.trans hr2)), hz']
  have e1 : Letter.b.perm 8 r pStar = ⟨-1 + s / 2, -1 + s / 2⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [pStar, Letter.center, rightCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, rightCenter, hA, pStar]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h2s]
        try ring_nf
  have e2 : Letter.b.perm 8 r ⟨-1 + s / 2, -1 + s / 2⟩ = ⟨2 - 3 * s / 2, s / 2⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [Letter.center, rightCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, rightCenter, hA]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h2s]
        try ring_nf
  have e3 : Letter.a.perm 8 r ⟨2 - 3 * s / 2, s / 2⟩ = ⟨-2 + 3 * s / 2, 2 - 3 * s / 2⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [Letter.center, leftCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, leftCenter, hA]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h2s]
        try ring_nf
  have e4 : Letter.b.perm 8 r ⟨-2 + 3 * s / 2, 2 - 3 * s / 2⟩ = ⟨1 - s / 2, -3 + 5 * s / 2⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [Letter.center, rightCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, rightCenter, hA]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h2s]
        try ring_nf
  simp only [seed, applyWord, e1, e2, e3, e4]
  apply Complex.ext
  · simp [pStar]
  · simp [pStar]
    ring

/-- For every `r ≥ √(10 - 5√2)` the orbit of `p*` contains `p* + (4√2 - 4) i`. -/
theorem mem_orbit_pStar {r : ℝ} (hr : √(10 - 5 * s) ≤ r) :
    pStar + ((4 * s - 4 : ℝ) : ℂ) * I ∈ orbit 8 8 r r pStar := by
  rw [← applyWord_seed hr]
  exact applyWord_mem_orbit _ (mem_orbit_self _ _ _ _ _)

end TDCSG.Eight

end
