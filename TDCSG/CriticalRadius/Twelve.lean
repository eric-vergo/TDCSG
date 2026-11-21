/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TDCSG.CriticalRadius.Basic

/-!
# The critical point of `GG₁₂`

Base facts of Part A of `notes/proofs/critical-radius-n12.md`. The critical point is
`p* = (2 - √3)(1 - 2i) = -2ζ + 4ζ² - 3ζ³`, with `ζ = exp (2πi / 12)`, and the critical chord
is the line through `p*` in the direction `V = ζ⁵ + ζ⁶ = -(1 + √3/2) + i/2`.

## Main statements

* `TDCSG.Twelve.dist_pStar_leftCenter_sq`: `|p* + 1|² = 40 - 22√3`, so `p*` lies on the boundary
  circle of the left disk exactly at the conjectured critical radius `√(40 - 22√3)`.
* `TDCSG.Twelve.dist_pStar_rightCenter_sq`: `|p* - 1|² = 32 - 18√3`.
* `TDCSG.Twelve.applyWord_seed`: the seed word `b a b b a a` maps `p*` to `p* + (14 - 8√3) V`,
  for every `r ≥ √(40 - 22√3)`; so this point lies in the orbit of `p*`.

## Implementation notes

The full Theorem A of the written note (the orbit of `p*` contains `p* + 2 (2 - √3)^(k+2) V` for
all `k`) rests on a family of 30 words with domains given by quadratic surds and on an exact
closure computation; it is stated, not proved, as `TDCSG.CriticalRadius.InfiniteOrbitTwelve` in
`TDCSG.CriticalRadius.Statements`.

The six disk tests of the seed at `p*` have squared distances `32 - 18√3`, `22 - 12√3`,
`12 - 6√3`, `12 - 6√3`, `22 - 12√3` and `22 - 12√3`, all below `40 - 22√3`.
-/

@[expose] public section

open Complex Metric
open scoped Real

namespace TDCSG.Twelve

/-- `√3`, as a real number. -/
local notation "t" => Real.sqrt 3

theorem sqrt_three_sq : t ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt_three_bounds : 1.732 < t ∧ t < 1.7321 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- The rotation factor `exp (-2πi / 12) = √3/2 - i/2`. -/
theorem exp_rotationAngle_twelve : exp (-(2 * π * I / (12 : ℕ))) = ⟨t / 2, -(1 / 2)⟩ := by
  rw [show -(2 * π * I / (12 : ℕ)) = ((-(π / 6) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six,
    Real.sin_pi_div_six]
  apply Complex.ext <;> simp

/-- The critical point `p* = (2 - √3)(1 - 2i)`. -/
noncomputable def pStar : ℂ := ⟨2 - t, -4 + 2 * t⟩

/-- The direction `V = ζ⁵ + ζ⁶` of the critical chord. -/
noncomputable def chordDir : ℂ := ⟨-(t / 2) - 1, 1 / 2⟩

/-- `|p* + 1|² = 40 - 22√3`. -/
theorem dist_pStar_leftCenter_sq : dist pStar leftCenter ^ 2 = 40 - 22 * t := by
  rw [dist_sq_eq_re_im]
  simp only [pStar, leftCenter, neg_re, neg_im, one_re, one_im]
  linear_combination 5 * sqrt_three_sq

/-- `|p* - 1|² = 32 - 18√3`. -/
theorem dist_pStar_rightCenter_sq : dist pStar rightCenter ^ 2 = 32 - 18 * t := by
  rw [dist_sq_eq_re_im]
  simp only [pStar, rightCenter, one_re, one_im]
  linear_combination 5 * sqrt_three_sq

/-- At the radius `√(40 - 22√3)` the point `p*` lies on the boundary circle of the left disk. -/
theorem pStar_mem_sphere : pStar ∈ sphere leftCenter √(40 - 22 * t) := by
  rw [mem_sphere, ← dist_pStar_leftCenter_sq, Real.sqrt_sq dist_nonneg]

/-- The seed word `b a b b a a`. -/
def seed : List Letter := [.b, .a, .b, .b, .a, .a]

/-- The seed word `b a b b a a` maps `p*` to `p* + (14 - 8√3) V` for every `r ≥ √(40 - 22√3)`. -/
theorem applyWord_seed {r : ℝ} (hr : √(40 - 22 * t) ≤ r) :
    applyWord 12 r seed pStar = pStar + ((14 - 8 * t : ℝ) : ℂ) * chordDir := by
  obtain ⟨h1, h2⟩ := sqrt_three_bounds
  have h3s := sqrt_three_sq
  have hr0 : 0 ≤ r := (Real.sqrt_nonneg _).trans hr
  have hr2 : 40 - 22 * t ≤ r ^ 2 := sq_le_of_sqrt_le (by linarith) hr
  have hA := exp_rotationAngle_twelve
  have step (l : Letter) (z z' : ℂ) (hz : (z.re - l.center.re) ^ 2 + (z.im - l.center.im) ^ 2 ≤
      40 - 22 * t) (hz' : l.glob 12 z = z') : l.perm 12 r z = z' := by
    rw [Letter.perm_apply_of_mem (mem_closedBall_of_sq_le hr0 (hz.trans hr2)), hz']
  have e1 : Letter.b.perm 12 r pStar = ⟨-5 / 2 + 3 * t / 2, 5 / 2 - 3 * t / 2⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [pStar, Letter.center, rightCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, rightCenter, hA, pStar]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h3s]
        try ring_nf
  have e2 : Letter.a.perm 12 r ⟨-5 / 2 + 3 * t / 2, 5 / 2 - 3 * t / 2⟩ =
      ⟨5 / 2 - 3 * t / 2, -3 / 2 + t / 2⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [Letter.center, leftCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, leftCenter, hA]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h3s]
        try ring_nf
  have e3 : Letter.b.perm 12 r ⟨5 / 2 - 3 * t / 2, -3 / 2 + t / 2⟩ = ⟨-2 + t, 0⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [Letter.center, rightCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, rightCenter, hA]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h3s]
        try ring_nf
  have e4 : Letter.b.perm 12 r ⟨-2 + t, 0⟩ = ⟨5 / 2 - 3 * t / 2, 3 / 2 - t / 2⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [Letter.center, rightCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, rightCenter, hA]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h3s]
        try ring_nf
  have e5 : Letter.a.perm 12 r ⟨5 / 2 - 3 * t / 2, 3 / 2 - t / 2⟩ =
      ⟨-5 / 2 + 3 * t / 2, -5 / 2 + 3 * t / 2⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [Letter.center, leftCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, leftCenter, hA]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h3s]
        try ring_nf
  have e6 : Letter.a.perm 12 r ⟨-5 / 2 + 3 * t / 2, -5 / 2 + 3 * t / 2⟩ = ⟨0, 3 - 2 * t⟩ := by
    refine step _ _ _ ?_ ?_
    · simp [Letter.center, leftCenter]
      nlinarith
    · simp only [Letter.glob, Letter.factor, Letter.center, leftCenter, hA]
      apply Complex.ext
      all_goals
        simp
        ring_nf
        try simp only [h3s]
        try ring_nf
  simp only [seed, applyWord, e1, e2, e3, e4, e5, e6]
  apply Complex.ext
  · simp [pStar, chordDir]
    ring_nf
    simp only [h3s]
    ring
  · simp [pStar, chordDir]
    ring

/-- For every `r ≥ √(40 - 22√3)` the orbit of `p*` contains `p* + (14 - 8√3) V`. -/
theorem mem_orbit_pStar {r : ℝ} (hr : √(40 - 22 * t) ≤ r) :
    pStar + ((14 - 8 * t : ℝ) : ℂ) * chordDir ∈ orbit 12 12 r r pStar := by
  rw [← applyWord_seed hr]
  exact applyWord_mem_orbit _ (mem_orbit_self _ _ _ _ _)

end TDCSG.Twelve

end
