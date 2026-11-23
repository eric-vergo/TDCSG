/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TDCSG.CriticalRadius.CyclotomicModel

/-!
# `GG₈(r)` has an infinite orbit for every `r ≥ √(10 - 5√2)`

Part A of `notes/proofs/critical-radius-n8.md`. The critical point is
`p* = 1 - 2ζ + ζ² - ζ³ = (1 - √2/2) - (3√2/2 - 1) i`, with `ζ = exp (2πi / 8)`, and the critical
chord is the vertical line `t ↦ p* + i t`.

## Main definitions

* `TDCSG.Eight.family`: the 31 words of Appendix A of the note, each with the isometry
  `t ↦ ±t + c` it induces on the chord and its domain.
* `TDCSG.Eight.pieces`: the closure data: for each member, the pieces of its domain rescaled by
  `ε = √2 - 1`, each with its composition sequence.

## Main statements

* `TDCSG.Eight.dist_pStar_leftCenter_sq`: `|p* + 1|² = 10 - 5√2`, so `p*` lies on the boundary
  circle of the left disk exactly at the conjectured critical radius `√(10 - 5√2)`.
* `TDCSG.Eight.dist_pStar_rightCenter_sq`: `|p* - 1|² = 6 - 3√2`, so `p*` lies inside the right
  disk at that radius.
* `TDCSG.Eight.applyWord_seed`: the seed word `b b a b` maps `p*` to `p* + (4√2 - 4) i`, for every
  `r ≥ √(10 - 5√2)`; so this point lies in the orbit of `p*`.
* `TDCSG.Eight.realizeOK_family`, `TDCSG.Eight.closureOK_family`: the family is realized by its
  words and closed under rescaling by `ε` (Lemma 2.3 of the note).
* `TDCSG.Eight.mem_orbit_pStar_pow`: **Theorem A**, orbit form: for every `r ≥ √(10 - 5√2)` the
  orbit of `p*` contains `p* + 4 i (√2 - 1)^(k+1)` for every `k`.

## Implementation notes

The two checks run in the exact model `TDCSG.CycQ 2` of `ℤ[ζ]` and are decided by the kernel.
Parameters on the chord are stored doubled: the domain end points lie in `ℚ(√2)(Y)` with
`Y = √(19/2 - 5√2)`, and `2Y = √(38 - 20√2)`. The end points of the closure pieces are not listed
in the note; they were recomputed (each piece ends where its composition sequence stops being
defined) and are checked here like everything else.

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

/-- `(√2)² = 2`. -/
theorem sqrt_two_sq : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- Decimal bounds for `√2`. -/
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

/-! ### The renormalization family -/

open CycQ Renormalization

/-- The root of unity `ζ = exp (2πi / 8)`. -/
noncomputable def zeta : ℂ := exp (2 * π * I / (8 : ℕ))

/-- `ζ = (√2 + √2 i) / 2`. -/
theorem zeta_eq : zeta = ⟨s / 2, s / 2⟩ := exp_two_pi_I_div_eight

/-- `ζ² = i`. -/
theorem zeta_sq : zeta ^ 2 = I := by
  rw [zeta_eq, sq]
  apply Complex.ext
  · simp
  · simp only [mul_im, I_im]
    nlinarith [sqrt_two_sq]

/-- `ζ = exp (2πi / 8)` satisfies the relations of the model `CycQ 2`. -/
theorem isRoot_zeta : IsRoot 8 2 zeta where
  exp_eq := rfl
  pow_four := by
    rw [show zeta ^ 4 = (zeta ^ 2) ^ 2 by ring, zeta_sq]
    simp [CycQ.v]
  sqrt_eq := by
    rw [show zeta ^ 3 = zeta * zeta ^ 2 by ring, zeta_sq, zeta_eq]
    apply Complex.ext <;> simp [CycQ.v]

/-- The parameter `(a + b √2 + (c + d √2) √h₁ + (e + f √2) √h₂) / 2`, in the model. -/
def L (a b c d e f : ℤ) : Lin 2 := ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩

/-- The family of Appendix A, in the order of the table (row `k + 1` is entry `k`). -/
def family : List (Entry 2) := [
  -- 1: `bbab`
  ⟨[.b, .b, .a, .b],
    false, ⟨-8, 8⟩, L (-2) 3 (-1) 0 0 0, L (-6) 3 1 0 0 0⟩,
  -- 2: `bABABA`
  ⟨[.b, .aInv, .bInv, .aInv, .bInv, .aInv],
    false, ⟨-8, 8⟩, L (-2) 3 (-1) 0 0 0, L (-4) 4 0 0 0 0⟩,
  -- 3: `bbaababa`
  ⟨[.b, .b, .a, .a, .b, .a, .b, .a],
    true, ⟨8, -4⟩, L (-2) 3 (-1) 0 0 0, L (-8) 6 0 0 0 0⟩,
  -- 4: `bAbaba`
  ⟨[.b, .aInv, .b, .a, .b, .a],
    false, ⟨0, 0⟩, L (-2) 3 (-1) 0 0 0, L 0 0 0 0 0 0⟩,
  -- 5: `bbaBABababaB`
  ⟨[.b, .b, .a, .bInv, .aInv, .bInv, .a, .b, .a, .b, .a, .bInv],
    false, ⟨-16, 12⟩, L (-12) 8 0 0 0 0, L (-10) 5 1 0 0 0⟩,
  -- 6: `bbaababaBABB`
  ⟨[.b, .b, .a, .a, .b, .a, .b, .a, .bInv, .aInv, .bInv, .bInv],
    false, ⟨-16, 12⟩, L (-10) 9 (-1) 0 0 0, L (-8) 6 0 0 0 0⟩,
  -- 7: `bbaBABBABB`
  ⟨[.b, .b, .a, .bInv, .aInv, .bInv, .bInv, .aInv, .bInv, .bInv],
    false, ⟨-16, 12⟩, L (-10) 9 (-1) 0 0 0, L (-10) 5 1 0 0 0⟩,
  -- 8: `ABABBABABBAB`
  ⟨[.aInv, .bInv, .aInv, .bInv, .bInv, .aInv, .bInv, .aInv, .bInv, .bInv, .aInv, .bInv],
    false, ⟨8, -4⟩, L 0 0 0 0 0 0, L 4 (-2) 0 0 0 0⟩,
  -- 9: `bbaabbaBABaB`
  ⟨[.b, .b, .a, .a, .b, .b, .a, .bInv, .aInv, .bInv, .a, .bInv],
    false, ⟨0, 0⟩, L 0 0 0 0 0 0, L (-8) 6 0 0 0 0⟩,
  -- 10: `ABABBABA`
  ⟨[.aInv, .bInv, .aInv, .bInv, .bInv, .aInv, .bInv, .aInv],
    true, ⟨-8, 8⟩, L 0 0 0 0 0 0, L 4 (-2) 0 0 0 0⟩,
  -- 11: `babaBABABBAB`
  ⟨[.b, .a, .b, .a, .bInv, .aInv, .bInv, .aInv, .bInv, .bInv, .aInv, .bInv],
    false, ⟨8, -4⟩, L 2 1 (-1) 0 0 0, L 4 (-2) 0 0 0 0⟩,
  -- 12: `babb`
  ⟨[.b, .a, .b, .b],
    false, ⟨0, 4⟩, L 2 1 (-1) 0 0 0, L (-2) 1 1 0 0 0⟩,
  -- 13: `babaBABA`
  ⟨[.b, .a, .b, .a, .bInv, .aInv, .bInv, .aInv],
    true, ⟨-8, 8⟩, L 2 1 (-1) 0 0 0, L 4 (-2) 0 0 0 0⟩,
  -- 14: `bbabABABAABB`
  ⟨[.b, .b, .a, .b, .aInv, .bInv, .aInv, .bInv, .aInv, .aInv, .bInv, .bInv],
    false, ⟨-16, 12⟩, L (-8) 6 0 0 0 0, L (-6) 3 1 0 0 0⟩,
  -- 15: `babaBABabABA`
  ⟨[.b, .a, .b, .a, .bInv, .aInv, .bInv, .a, .b, .aInv, .bInv, .aInv],
    true, ⟨-16, 12⟩, L 12 (-8) 0 0 0 0, L 4 (-2) 0 0 0 0⟩,
  -- 16: `bbabbabABB`
  ⟨[.b, .b, .a, .b, .b, .a, .b, .aInv, .bInv, .bInv],
    false, ⟨-16, 12⟩, L (-6) 7 (-1) 0 0 0, L (-6) 3 1 0 0 0⟩,
  -- 17: `bABBAbABBAba`
  ⟨[.b, .aInv, .bInv, .bInv, .aInv, .b, .aInv, .bInv, .bInv, .aInv, .b, .a],
    false, ⟨8, -4⟩, L 4 (-2) 0 0 0 0, L (-4) 4 0 0 0 0⟩,
  -- 18: `babbabABBAba`
  ⟨[.b, .a, .b, .b, .a, .b, .aInv, .bInv, .bInv, .aInv, .b, .a],
    false, ⟨8, -4⟩, L 4 (-2) 0 0 0 0, L 8 (-4) 0 0 0 0⟩,
  -- 19: `bABBAA`
  ⟨[.b, .aInv, .bInv, .bInv, .aInv, .aInv],
    false, ⟨0, 4⟩, L 4 (-2) 0 0 0 0, L (-4) 4 0 0 0 0⟩,
  -- 20: `abaBAbABBAba`
  ⟨[.a, .b, .a, .bInv, .aInv, .b, .aInv, .bInv, .bInv, .aInv, .b, .a],
    true, ⟨16, -12⟩, L (-4) 4 0 0 0 0, L (-12) 10 0 0 0 0⟩,
  -- 21: `BABB`
  ⟨[.bInv, .aInv, .bInv, .bInv],
    false, ⟨-8, 8⟩, L (-2) 5 (-1) 0 0 0, L (-6) 5 1 0 0 0⟩,
  -- 22: `ABAbaBABBABA`
  ⟨[.aInv, .bInv, .aInv, .b, .a, .bInv, .aInv, .bInv, .bInv, .aInv, .bInv, .aInv],
    true, ⟨-16, 12⟩, L 8 (-4) 0 0 0 0, L 0 2 0 0 0 0⟩,
  -- 23: `ABAbaBABaB`
  ⟨[.aInv, .bInv, .aInv, .b, .a, .bInv, .aInv, .bInv, .a, .bInv],
    false, ⟨8, -4⟩, L 8 (-4) 0 0 0 0, L 0 2 0 0 0 0⟩,
  -- 24: `babABBABABaB`
  ⟨[.b, .a, .b, .aInv, .bInv, .bInv, .aInv, .bInv, .aInv, .bInv, .a, .bInv],
    false, ⟨8, -4⟩, L 8 (-4) 0 0 0 0, L (-2) 1 1 0 0 0⟩,
  -- 25: `BABBABABaB`
  ⟨[.bInv, .aInv, .bInv, .bInv, .aInv, .bInv, .aInv, .bInv, .a, .bInv],
    true, ⟨8, -8⟩, L (-10) 11 (-1) 0 0 0, L (-8) 8 0 0 0 0⟩,
  -- 26: `BBABBABB`
  ⟨[.bInv, .bInv, .aInv, .bInv, .bInv, .aInv, .bInv, .bInv],
    true, ⟨-8, 4⟩, L 2 3 (-1) 0 0 0, L 2 (-1) 1 0 0 0⟩,
  -- 27: `BBAB`
  ⟨[.bInv, .bInv, .aInv, .bInv],
    false, ⟨0, 4⟩, L 2 3 (-1) 0 0 0, L (-2) 3 1 0 0 0⟩,
  -- 28: `BABAbaba`
  ⟨[.bInv, .aInv, .bInv, .aInv, .b, .a, .b, .a],
    true, ⟨8, -8⟩, L (-8) 8 0 0 0 0, L (-6) 5 1 0 0 0⟩,
  -- 29: `ababAb`
  ⟨[.a, .b, .a, .b, .aInv, .b],
    false, ⟨-8, 12⟩, L (-6) 9 (-1) 0 0 0, L (-4) 6 0 0 0 0⟩,
  -- 30: `BBAABABA`
  ⟨[.bInv, .bInv, .aInv, .aInv, .bInv, .aInv, .bInv, .aInv],
    true, ⟨-8, 4⟩, L 4 0 0 0 0 0, L (-2) 3 1 0 0 0⟩,
  -- 31: `BBAbab`
  ⟨[.bInv, .bInv, .aInv, .b, .a, .b],
    true, ⟨-8, 4⟩, L 6 1 (-1) 0 0 0, L (-2) 3 1 0 0 0⟩]

/-- The closure data of Appendix A: for each member, the pieces of its domain rescaled by
`ε`, with their composition sequences (indices from `0`). -/
def pieces : List (List (Piece 2)) := [
  -- 1
  [
    ⟨[0, 27, 5, 10], L 8 (-5) 1 (-1) 0 0, L 0 0 0 0 0 0⟩,
    ⟨[2, 21, 25, 10], L 0 0 0 0 0 0, L 20 (-14) 0 0 0 0⟩,
    ⟨[0, 20, 7, 19], L 20 (-14) 0 0 0 0, L 12 (-9) (-1) 1 0 0⟩],
  -- 2
  [
    ⟨[0, 27, 5, 10], L 8 (-5) 1 (-1) 0 0, L 0 0 0 0 0 0⟩,
    ⟨[2, 21, 25, 10], L 0 0 0 0 0 0, L 20 (-14) 0 0 0 0⟩,
    ⟨[0, 24, 4, 16], L 20 (-14) 0 0 0 0, L 12 (-8) 0 0 0 0⟩],
  -- 3
  [
    ⟨[0, 27, 5], L 8 (-5) 1 (-1) 0 0, L 0 0 0 0 0 0⟩,
    ⟨[0, 20, 7, 20], L 0 0 0 0 0 0, L 20 (-14) 0 0 0 0⟩],
  -- 4
  [
    ⟨[0, 27], L 8 (-5) 1 (-1) 0 0, L 0 0 0 0 0 0⟩],
  -- 5
  [
    ⟨[3, 5, 14, 17], L 28 (-20) 0 0 0 0, L 0 0 0 0 0 0⟩,
    ⟨[7, 20, 14, 17], L 0 0 0 0 0 0, L 20 (-15) (-1) 1 0 0⟩],
  -- 6
  [
    ⟨[3, 5, 14, 17], L 28 (-19) 1 (-1) 0 0, L 0 0 0 0 0 0⟩,
    ⟨[7, 20, 14, 17], L 0 0 0 0 0 0, L 20 (-14) 0 0 0 0⟩],
  -- 7
  [
    ⟨[3, 5, 14, 17], L 28 (-19) 1 (-1) 0 0, L 0 0 0 0 0 0⟩,
    ⟨[7, 20, 14, 17], L 0 0 0 0 0 0, L 20 (-15) (-1) 1 0 0⟩],
  -- 8
  [
    ⟨[9, 26, 17, 5], L 0 0 0 0 0 0, L (-8) 6 0 0 0 0⟩],
  -- 9
  [
    ⟨[0, 20, 0, 24], L 0 0 0 0 0 0, L 20 (-14) 0 0 0 0⟩],
  -- 10
  [
    ⟨[0, 20, 5, 10], L 0 0 0 0 0 0, L (-8) 6 0 0 0 0⟩,
    ⟨[0, 21, 27, 10], L (-8) 6 0 0 0 0, L (-8) 6 0 0 0 0⟩],
  -- 11
  [
    ⟨[9, 26, 17, 5], L 0 1 1 (-1) 0 0, L (-8) 6 0 0 0 0⟩],
  -- 12
  [
    ⟨[0, 20, 7], L 0 1 1 (-1) 0 0, L 4 (-3) (-1) 1 0 0⟩],
  -- 13
  [
    ⟨[0, 20, 5, 10], L 0 1 1 (-1) 0 0, L (-8) 6 0 0 0 0⟩,
    ⟨[0, 21, 27, 10], L (-8) 6 0 0 0 0, L (-8) 6 0 0 0 0⟩],
  -- 14
  [
    ⟨[7, 19, 0, 17], L 20 (-14) 0 0 0 0, L 40 (-28) 0 0 0 0⟩,
    ⟨[10, 19, 0, 22], L 40 (-28) 0 0 0 0, L 12 (-9) (-1) 1 0 0⟩],
  -- 15
  [
    ⟨[5, 10, 19], L (-28) 20 0 0 0 0, L (-8) 6 0 0 0 0⟩,
    ⟨[0, 22, 2, 19], L (-8) 6 0 0 0 0, L (-8) 6 0 0 0 0⟩],
  -- 16
  [
    ⟨[10, 19, 0, 17], L 20 (-13) 1 (-1) 0 0, L 40 (-28) 0 0 0 0⟩,
    ⟨[10, 19, 0, 22], L 40 (-28) 0 0 0 0, L 12 (-9) (-1) 1 0 0⟩],
  -- 17
  [
    ⟨[0, 21, 27], L (-8) 6 0 0 0 0, L 12 (-8) 0 0 0 0⟩],
  -- 18
  [
    ⟨[0, 20, 13], L (-8) 6 0 0 0 0, L (-16) 12 0 0 0 0⟩],
  -- 19
  [
    ⟨[0, 20, 10], L (-8) 6 0 0 0 0, L 12 (-8) 0 0 0 0⟩],
  -- 20
  [
    ⟨[10, 1, 17, 13], L 12 (-8) 0 0 0 0, L 32 (-22) 0 0 0 0⟩],
  -- 21
  [
    ⟨[0, 20, 14, 17], L 12 (-7) 1 (-1) 0 0, L 4 (-2) 0 0 0 0⟩,
    ⟨[1, 19, 0, 17], L 4 (-2) 0 0 0 0, L 24 (-16) 0 0 0 0⟩,
    ⟨[11, 28, 30, 22], L 24 (-16) 0 0 0 0, L 16 (-11) (-1) 1 0 0⟩],
  -- 22
  [
    ⟨[0, 17, 5, 10], L (-16) 12 0 0 0 0, L 4 (-2) 0 0 0 0⟩],
  -- 23
  [
    ⟨[0, 20, 13], L (-16) 12 0 0 0 0, L 4 (-2) 0 0 0 0⟩],
  -- 24
  [
    ⟨[0, 20, 13], L (-16) 12 0 0 0 0, L 4 (-3) (-1) 1 0 0⟩],
  -- 25
  [
    ⟨[0, 20, 10, 13], L 32 (-21) 1 (-1) 0 0, L 4 (-2) 0 0 0 0⟩,
    ⟨[1, 19, 13], L 4 (-2) 0 0 0 0, L 24 (-16) 0 0 0 0⟩],
  -- 26
  [
    ⟨[1, 19, 14, 17], L 4 (-1) 1 (-1) 0 0, L (-4) 3 (-1) 1 0 0⟩],
  -- 27
  [
    ⟨[11, 26, 17], L 4 (-1) 1 (-1) 0 0, L 8 (-5) (-1) 1 0 0⟩],
  -- 28
  [
    ⟨[11, 26, 17, 13], L 24 (-16) 0 0 0 0, L 16 (-11) (-1) 1 0 0⟩],
  -- 29
  [
    ⟨[11, 27, 13, 7], L 24 (-15) 1 (-1) 0 0, L 16 (-10) 0 0 0 0⟩],
  -- 30
  [
    ⟨[11, 20, 4, 16], L (-4) 4 0 0 0 0, L (-12) 10 0 0 0 0⟩,
    ⟨[20, 0, 20, 10], L (-12) 10 0 0 0 0, L 8 (-5) (-1) 1 0 0⟩],
  -- 31
  [
    ⟨[11, 27, 7, 19], L (-4) 5 1 (-1) 0 0, L (-12) 10 0 0 0 0⟩,
    ⟨[20, 0, 20, 10], L (-12) 10 0 0 0 0, L 8 (-5) (-1) 1 0 0⟩]]

/-- `(2 Y)² = 38 - 20√2`, where `Y = √(19/2 - 5√2)` is the radical of the domain end points. -/
def radicand : Quad 2 := ⟨38, -20⟩

/-- The squared critical radius `10 - 5√2`. -/
def radiusSq : Quad 2 := ⟨10, -5⟩

/-- The unit `ε = √2 - 1`. -/
def unit : Quad 2 := ⟨-1, 1⟩

/-- The critical point `p* = 1 - 2ζ + ζ² - ζ³`, in the model. -/
def pModel : CycQ 2 := ⟨1, -2, 1, -1⟩

/-- The direction `i = ζ²` of the critical chord, in the model. -/
def dirModel : CycQ 2 := ⟨0, 0, 1, 0⟩

/-- Realization: every word of the family is valid at both end points of its domain, with the
listed action, at every radius `r ≥ √(10 - 5√2)`. -/
theorem realizeOK_family : realizeOK radiusSq radicand radicand pModel dirModel family = true := by
  decide +kernel

/-- Closure: the family is closed under rescaling by `ε = √2 - 1`. -/
theorem closureOK_family : closureOK radicand radicand unit family pieces = true := by
  decide +kernel

/-- The value of `radicand`. -/
theorem toReal_radicand : radicand.toReal = 38 - 20 * s := by
  simp [radicand, Quad.toReal]
  ring

/-- The value of `radiusSq`. -/
theorem toReal_radiusSq : radiusSq.toReal = 10 - 5 * s := by
  simp [radiusSq, Quad.toReal]
  ring

/-- The value of `unit`. -/
theorem toReal_unit : unit.toReal = s - 1 := by
  simp [unit, Quad.toReal]
  ring

/-- `pModel` represents the critical point `p*`. -/
theorem embed_pModel : embed zeta pModel = pStar := by
  have h3 : zeta ^ 3 = zeta * zeta ^ 2 := by ring
  simp only [embed, pModel, h3, zeta_sq]
  rw [zeta_eq]
  apply Complex.ext <;> simp [pStar] <;> ring

/-- `dirModel` represents the chord direction `i`. -/
theorem embed_dirModel : embed zeta dirModel = I := by
  simp [embed, dirModel, zeta_sq]

/-- Theorem A of the note `notes/proofs/critical-radius-n8.md`, orbit form: for every
`r ≥ √(10 - 5√2)` and every `k`, the orbit of `p*` contains `p* + 4 i (√2 - 1)^(k+1)`. -/
theorem mem_orbit_pStar_pow {r : ℝ} (hr : √(10 - 5 * s) ≤ r) (k : ℕ) :
    pStar + ((4 * (s - 1) ^ (k + 1) : ℝ) : ℂ) * I ∈ orbit 8 8 r r pStar := by
  have hs := sqrt_two_bounds
  have hh : 0 ≤ radicand.toReal := by rw [toReal_radicand]; linarith
  have h0 : (L 0 0 0 0 0 0).val radicand radicand = 0 := by simp [Lin.val, L, Quad.toReal]
  have hlo : (family.getD 0 default).lo.val radicand radicand ≤ 0 := by
    have := Lin.val_le_of_le hh hh (x := (family.getD 0 default).lo) (y := L 0 0 0 0 0 0)
      (by decide +kernel)
    rwa [h0] at this
  have hhi : 0 ≤ (family.getD 0 default).hi.val radicand radicand := by
    have := Lin.val_le_of_le hh hh (x := L 0 0 0 0 0 0) (y := (family.getD 0 default).hi)
      (by decide +kernel)
    rwa [h0] at this
  have hε : 0 < unit.toReal := by rw [toReal_unit]; linarith
  have hε' : 0 ≤ unit.toReal ^ k := pow_nonneg hε.le k
  have key := mem_orbit_of_checks isRoot_zeta hh hh hε realizeOK_family closureOK_family
    (r := r) (by rw [toReal_radiusSq]; exact hr) k (i := 0) (by decide) (t := 0)
    ⟨by nlinarith, by nlinarith⟩
  have hc : (family.getD 0 default).c.toReal = -8 + 8 * s := by
    simp [family, Quad.toReal]
  have e₁ : ract (family.getD 0 default).pos (unit.toReal ^ k *
      ((family.getD 0 default).c.toReal / 2)) 0 = 4 * (s - 1) ^ (k + 1) := by
    simp only [show (family.getD 0 default).pos = false from rfl, ract, Bool.false_eq_true,
      ite_false, hc, toReal_unit]
    ring
  rwa [embed_pModel, embed_dirModel, e₁, ofReal_zero, zero_mul, add_zero] at key

end TDCSG.Eight

end
