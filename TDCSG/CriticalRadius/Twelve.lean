/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TDCSG.CriticalRadius.CyclotomicModel

/-!
# `GG₁₂(r)` has an infinite orbit for every `r ≥ √(40 - 22√3)`

Part A of `notes/proofs/critical-radius-n12.md`. The critical point is
`p* = (2 - √3)(1 - 2i) = -2ζ + 4ζ² - 3ζ³`, with `ζ = exp (2πi / 12)`, and the critical chord
is the line `u ↦ p* + u V` in the direction `V = ζ⁵ + ζ⁶ = -(1 + √3/2) + i/2`.

## Main definitions

* `TDCSG.Twelve.family`: the 30 words of Appendix A of the note, each with the isometry
  `u ↦ ±u + c` it induces on the chord and its domain.
* `TDCSG.Twelve.pieces`: the closure data: for each member, the pieces of its domain rescaled by
  `ε = 2 - √3`, each with its composition sequence.

## Main statements

* `TDCSG.Twelve.dist_pStar_leftCenter_sq`: `|p* + 1|² = 40 - 22√3`, so `p*` lies on the boundary
  circle of the left disk exactly at the conjectured critical radius `√(40 - 22√3)`.
* `TDCSG.Twelve.dist_pStar_rightCenter_sq`: `|p* - 1|² = 32 - 18√3`.
* `TDCSG.Twelve.applyWord_seed`: the seed word `b a b b a a` maps `p*` to `p* + (14 - 8√3) V`,
  for every `r ≥ √(40 - 22√3)`; so this point lies in the orbit of `p*`.
* `TDCSG.Twelve.realizeOK_family`, `TDCSG.Twelve.closureOK_family`: the family is realized by
  its words and closed under rescaling by `ε` (Lemma 2.1 of the note).
* `TDCSG.Twelve.mem_orbit_pStar_pow`: **Theorem A**, orbit form: for every `r ≥ √(40 - 22√3)`
  the orbit of `p*` contains `p* + 2 (2 - √3)^(k+2) V` for every `k`.

## Implementation notes

The two checks run in the exact model `TDCSG.CycQ 3` of `ℤ[ζ]` and are decided by the kernel.
Parameters on the chord are stored doubled: the domain end points lie in `ℚ(√3)(Y₁, Y₂)` with
`Y₁ = √(143 - 165√3/2)` and `Y₂ = √(145 - 167√3/2)`, each end point involving at most one of
them; comparisons between end points with different radicals are decided by two squarings
(`TDCSG.Quad.nonneg₃`). The end points of the closure pieces are not listed in the note; they
were recomputed and are checked here like everything else.

The six disk tests of the seed at `p*` have squared distances `32 - 18√3`, `22 - 12√3`,
`12 - 6√3`, `12 - 6√3`, `22 - 12√3` and `22 - 12√3`, all below `40 - 22√3`.
-/

@[expose] public section

open Complex Metric
open scoped Real

namespace TDCSG.Twelve

/-- `√3`, as a real number. -/
local notation "t" => Real.sqrt 3

/-- `(√3)² = 3`. -/
theorem sqrt_three_sq : t ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- Decimal bounds for `√3`. -/
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

/-! ### The renormalization family -/

open CycQ Renormalization

/-- The root of unity `ζ = exp (2πi / 12)`. -/
noncomputable def zeta : ℂ := exp (2 * π * I / (12 : ℕ))

/-- `ζ = (√3 + i) / 2`. -/
theorem zeta_eq : zeta = ⟨t / 2, 1 / 2⟩ := by
  rw [zeta, show 2 * π * I / (12 : ℕ) = ((π / 6 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_six, Real.sin_pi_div_six]
  apply Complex.ext <;> simp

/-- `ζ² = (1 + √3 i) / 2`. -/
theorem zeta_sq : zeta ^ 2 = ⟨1 / 2, t / 2⟩ := by
  rw [zeta_eq, sq]
  apply Complex.ext
  · simp only [mul_re]
    nlinarith [sqrt_three_sq]
  · simp only [mul_im]
    ring

/-- `ζ³ = i`. -/
theorem zeta_cube : zeta ^ 3 = I := by
  rw [pow_succ, zeta_sq, zeta_eq]
  apply Complex.ext
  · simp only [mul_re, I_re]
    ring
  · simp only [mul_im, I_im]
    nlinarith [sqrt_three_sq]

/-- `ζ = exp (2πi / 12)` satisfies the relations of the model `CycQ 3`. -/
theorem isRoot_zeta : IsRoot 12 3 zeta where
  exp_eq := rfl
  pow_four := by
    rw [show zeta ^ 4 = (zeta ^ 2) ^ 2 by ring, zeta_sq, sq]
    apply Complex.ext
    · simp [CycQ.v]
      nlinarith [sqrt_three_sq]
    · simp [CycQ.v]
      ring
  sqrt_eq := by
    rw [zeta_cube, zeta_eq]
    apply Complex.ext <;> simp [CycQ.v] <;> ring

/-- The parameter `(a + b √3 + (c + d √3) √h₁ + (e + f √3) √h₂) / 2`, in the model. -/
def L (a b c d e f : ℤ) : Lin 3 := ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩

/-- The family of Appendix A, in the order of the table (row `k + 1` is entry `k`). -/
def family : List (Entry 3) := [
  -- 1: `bbabAbaBABabABAbaBabABABAbaB`
  ⟨[.b, .b, .a, .b, .aInv, .b, .a, .bInv, .aInv, .bInv, .a, .b, .aInv, .bInv, .aInv, .b, .a,
      .bInv, .a, .b, .aInv, .bInv, .aInv, .bInv, .aInv, .b, .a, .bInv],
    true, ⟨-76, 44⟩, L 89 (-51) 0 0 (-1) 0, L 48 (-28) 0 0 0 0⟩,
  -- 2: `bbABabaBAbabABabaBAbABaBAB`
  ⟨[.b, .b, .aInv, .bInv, .a, .b, .a, .bInv, .aInv, .b, .a, .b, .aInv, .bInv, .a, .b, .a, .bInv,
      .aInv, .b, .aInv, .bInv, .a, .bInv, .aInv, .bInv],
    true, ⟨-76, 44⟩, L 48 (-28) 0 0 0 0, L 77 (-45) 1 0 0 0⟩,
  -- 3: `bbABabaBAbabABababaB`
  ⟨[.b, .b, .aInv, .bInv, .a, .b, .a, .bInv, .aInv, .b, .a, .b, .aInv, .bInv, .a, .b, .a, .b, .a,
      .bInv],
    false, ⟨76, -44⟩, L 48 (-28) 0 0 0 0, L 38 (-22) 0 0 0 0⟩,
  -- 4: `bbABabaBAbababbababa`
  ⟨[.b, .b, .aInv, .bInv, .a, .b, .a, .bInv, .aInv, .b, .a, .b, .a, .b, .b, .a, .b, .a, .b, .a],
    true, ⟨-48, 28⟩, L 48 (-28) 0 0 0 0, L 38 (-22) 0 0 0 0⟩,
  -- 5: `bbabABAbaBabAbaBABabABABAbaB`
  ⟨[.b, .b, .a, .b, .aInv, .bInv, .aInv, .b, .a, .bInv, .a, .b, .aInv, .b, .a, .bInv, .aInv,
      .bInv, .a, .b, .aInv, .bInv, .aInv, .bInv, .aInv, .b, .a, .bInv],
    true, ⟨-76, 44⟩, L 47 (-27) (-1) 0 0 0, L 76 (-44) 0 0 0 0⟩,
  -- 6: `babbaa`
  ⟨[.b, .a, .b, .b, .a, .a],
    false, ⟨28, -16⟩, L 9 (-5) (-1) 0 0 0, L 28 (-16) 0 0 0 0⟩,
  -- 7: `bABababaBAbababABABAbaBABABa`
  ⟨[.b, .aInv, .bInv, .a, .b, .a, .b, .a, .bInv, .aInv, .b, .a, .b, .a, .b, .aInv, .bInv, .aInv,
      .bInv, .aInv, .b, .a, .bInv, .aInv, .bInv, .aInv, .bInv, .a],
    true, ⟨56, -32⟩, L (-28) 16 0 0 0 0, L 0 0 0 0 0 0⟩,
  -- 8: `bbABaBAABABabaBAbABabaBAbaba`
  ⟨[.b, .b, .aInv, .bInv, .a, .bInv, .aInv, .aInv, .bInv, .aInv, .bInv, .a, .b, .a, .bInv, .aInv,
      .b, .aInv, .bInv, .a, .b, .a, .bInv, .aInv, .b, .a, .b, .a],
    true, ⟨-76, 44⟩, L 76 (-44) 0 0 0 0, L 38 (-22) 0 0 0 0⟩,
  -- 9: `bABBABabABAbabABaBAbabABAB`
  ⟨[.b, .aInv, .bInv, .bInv, .aInv, .bInv, .a, .b, .aInv, .bInv, .aInv, .b, .a, .b, .aInv, .bInv,
      .a, .bInv, .aInv, .b, .a, .b, .aInv, .bInv, .aInv, .bInv],
    false, ⟨-48, 28⟩, L (-63) 37 0 0 (-1) 0, L 1 (-1) 1 0 0 0⟩,
  -- 10: `bbababABABAbaBABabAB`
  ⟨[.b, .b, .a, .b, .a, .b, .aInv, .bInv, .aInv, .bInv, .aInv, .b, .a, .bInv, .aInv, .bInv, .a,
      .b, .aInv, .bInv],
    true, ⟨-48, 28⟩, L 38 (-22) 0 0 0 0, L 63 (-37) 0 0 1 0⟩,
  -- 11: `bbababABABAbaBABabAbaBabABAB`
  ⟨[.b, .b, .a, .b, .a, .b, .aInv, .bInv, .aInv, .bInv, .aInv, .b, .a, .bInv, .aInv, .bInv, .a,
      .b, .aInv, .b, .a, .bInv, .a, .b, .aInv, .bInv, .aInv, .bInv],
    true, ⟨-76, 44⟩, L 38 (-22) 0 0 0 0, L 67 (-39) 1 0 0 0⟩,
  -- 12: `bbababABABAbaBABabAbaBBB`
  ⟨[.b, .b, .a, .b, .a, .b, .aInv, .bInv, .aInv, .bInv, .aInv, .b, .a, .bInv, .aInv, .bInv, .a,
      .b, .aInv, .b, .a, .bInv, .bInv, .bInv],
    true, ⟨-56, 32⟩, L 41 (-23) 0 0 (-1) 0, L 67 (-39) 1 0 0 0⟩,
  -- 13: `bbabABaBAbABabaBAbababbababa`
  ⟨[.b, .b, .a, .b, .aInv, .bInv, .a, .bInv, .aInv, .b, .aInv, .bInv, .a, .b, .a, .bInv, .aInv,
      .b, .a, .b, .a, .b, .b, .a, .b, .a, .b, .a],
    true, ⟨-76, 44⟩, L 37 (-21) (-1) 0 0 0, L 66 (-38) 0 0 0 0⟩,
  -- 14: `bbabABaBAbABabaBAbabABBAbaBB`
  ⟨[.b, .b, .a, .b, .aInv, .bInv, .a, .bInv, .aInv, .b, .aInv, .bInv, .a, .b, .a, .bInv, .aInv,
      .b, .a, .b, .aInv, .bInv, .bInv, .aInv, .b, .a, .bInv, .bInv],
    true, ⟨-56, 32⟩, L 37 (-21) (-1) 0 0 0, L 66 (-38) 0 0 0 0⟩,
  -- 15: `AABBAB`
  ⟨[.aInv, .aInv, .bInv, .bInv, .aInv, .bInv],
    false, ⟨28, -16⟩, L 0 0 0 0 0 0, L 19 (-11) 1 0 0 0⟩,
  -- 16: `ABABABBABABabAbaBABabABAbaBB`
  ⟨[.aInv, .bInv, .aInv, .bInv, .aInv, .bInv, .bInv, .aInv, .bInv, .aInv, .bInv, .a, .b, .aInv,
      .b, .a, .bInv, .aInv, .bInv, .a, .b, .aInv, .bInv, .aInv, .b, .a, .bInv, .bInv],
    true, ⟨76, -44⟩, L 0 0 0 0 0 0, L (-38) 22 0 0 0 0⟩,
  -- 17: `ABABABBABABabAbaBABABa`
  ⟨[.aInv, .bInv, .aInv, .bInv, .aInv, .bInv, .bInv, .aInv, .bInv, .aInv, .bInv, .a, .b, .aInv,
      .b, .a, .bInv, .aInv, .bInv, .aInv, .bInv, .a],
    true, ⟨56, -32⟩, L 0 0 0 0 0 0, L (-41) 23 0 0 1 0⟩,
  -- 18: `babaBAbABaBAbabABababaBABABB`
  ⟨[.b, .a, .b, .a, .bInv, .aInv, .b, .aInv, .bInv, .a, .bInv, .aInv, .b, .a, .b, .aInv, .bInv,
      .a, .b, .a, .b, .a, .bInv, .aInv, .bInv, .aInv, .bInv, .bInv],
    true, ⟨76, -44⟩, L (-38) 22 0 0 0 0, L (-9) 5 1 0 0 0⟩,
  -- 19: `babaBAbABaBAbabABabaBAbaba`
  ⟨[.b, .a, .b, .a, .bInv, .aInv, .b, .aInv, .bInv, .a, .bInv, .aInv, .b, .a, .b, .aInv, .bInv,
      .a, .b, .a, .bInv, .aInv, .b, .a, .b, .a],
    false, ⟨-48, 28⟩, L (-38) 22 0 0 0 0, L (-9) 5 1 0 0 0⟩,
  -- 20: `bbababABABAbaBabABAbaBABabAB`
  ⟨[.b, .b, .a, .b, .a, .b, .aInv, .bInv, .aInv, .bInv, .aInv, .b, .a, .bInv, .a, .b, .aInv,
      .bInv, .aInv, .b, .a, .bInv, .aInv, .bInv, .a, .b, .aInv, .bInv],
    true, ⟨-76, 44⟩, L 66 (-38) 0 0 0 0, L 25 (-15) 0 0 1 0⟩,
  -- 21: `bababaBABABabABAbaBabAbaBABB`
  ⟨[.b, .a, .b, .a, .b, .a, .bInv, .aInv, .bInv, .aInv, .bInv, .a, .b, .aInv, .bInv, .aInv, .b,
      .a, .bInv, .a, .b, .aInv, .b, .a, .bInv, .aInv, .bInv, .bInv],
    true, ⟨76, -44⟩, L (-39) 23 (-1) 0 0 0, L (-10) 6 0 0 0 0⟩,
  -- 22: `ABABabABAbaBABabAbaBabABAB`
  ⟨[.aInv, .bInv, .aInv, .bInv, .a, .b, .aInv, .bInv, .aInv, .b, .a, .bInv, .aInv, .bInv, .a, .b,
      .aInv, .b, .a, .bInv, .a, .b, .aInv, .bInv, .aInv, .bInv],
    false, ⟨-48, 28⟩, L (-39) 23 (-1) 0 0 0, L (-10) 6 0 0 0 0⟩,
  -- 23: `AbababABabaBAbABaBAbabABAB`
  ⟨[.aInv, .b, .a, .b, .a, .b, .aInv, .bInv, .a, .b, .a, .bInv, .aInv, .b, .aInv, .bInv, .a,
      .bInv, .aInv, .b, .a, .b, .aInv, .bInv, .aInv, .bInv],
    true, ⟨-76, 44⟩, L 28 (-16) 0 0 0 0, L 91 (-53) 0 0 1 0⟩,
  -- 24: `ABAABabaBAbababABABAbaBABABa`
  ⟨[.aInv, .bInv, .aInv, .aInv, .bInv, .a, .b, .a, .bInv, .aInv, .b, .a, .b, .a, .b, .aInv, .bInv,
      .aInv, .bInv, .aInv, .b, .a, .bInv, .aInv, .bInv, .aInv, .bInv, .a],
    false, ⟨84, -48⟩, L 28 (-16) 0 0 0 0, L 56 (-32) 0 0 0 0⟩,
  -- 25: `baBAbabABabaBAbABababaBABABB`
  ⟨[.b, .a, .bInv, .aInv, .b, .a, .b, .aInv, .bInv, .a, .b, .a, .bInv, .aInv, .b, .aInv, .bInv,
      .a, .b, .a, .b, .a, .bInv, .aInv, .bInv, .aInv, .bInv, .bInv],
    true, ⟨76, -44⟩, L (-10) 6 0 0 0 0, L (-51) 29 0 0 1 0⟩,
  -- 26: `baBAbabABabaBAbABabaBAbaba`
  ⟨[.b, .a, .bInv, .aInv, .b, .a, .b, .aInv, .bInv, .a, .b, .a, .bInv, .aInv, .b, .aInv, .bInv,
      .a, .b, .a, .bInv, .aInv, .b, .a, .b, .a],
    false, ⟨-48, 28⟩, L (-10) 6 0 0 0 0, L (-48) 28 0 0 0 0⟩,
  -- 27: `babaBABabAbaBabABAbaBABABa`
  ⟨[.b, .a, .b, .a, .bInv, .aInv, .bInv, .a, .b, .aInv, .b, .a, .bInv, .a, .b, .aInv, .bInv,
      .aInv, .b, .a, .bInv, .aInv, .bInv, .aInv, .bInv, .a],
    true, ⟨76, -44⟩, L (-48) 28 0 0 0 0, L 15 (-9) 0 0 1 0⟩,
  -- 28: `bbaBabAbaBABabABAbaBABabaBAB`
  ⟨[.b, .b, .a, .bInv, .a, .b, .aInv, .b, .a, .bInv, .aInv, .bInv, .a, .b, .aInv, .bInv, .aInv,
      .b, .a, .bInv, .aInv, .bInv, .a, .b, .a, .bInv, .aInv, .bInv],
    true, ⟨-84, 48⟩, L 93 (-53) (-1) 0 0 0, L 56 (-32) 0 0 0 0⟩,
  -- 29: `AbababABaBAbabABababaB`
  ⟨[.aInv, .b, .a, .b, .a, .b, .aInv, .bInv, .a, .bInv, .aInv, .b, .a, .b, .aInv, .bInv, .a, .b,
      .a, .b, .a, .bInv],
    false, ⟨84, -48⟩, L 56 (-32) 0 0 0 0, L 15 (-9) 0 0 1 0⟩,
  -- 30: `AbababABaBAbabABabaBAbABaBAB`
  ⟨[.aInv, .b, .a, .b, .a, .b, .aInv, .bInv, .a, .bInv, .aInv, .b, .a, .b, .aInv, .bInv, .a, .b,
      .a, .bInv, .aInv, .b, .aInv, .bInv, .a, .bInv, .aInv, .bInv],
    true, ⟨-84, 48⟩, L 56 (-32) 0 0 0 0, L 15 (-9) 0 0 1 0⟩]

/-- The closure data of Appendix A: for each member, the pieces of its domain rescaled by
`ε`, with their composition sequences (indices from `0`). -/
def pieces : List (List (Piece 3)) := [
  -- 1
  [
    ⟨[7, 9, 27, 4], L 331 (-191) 0 0 (-2) 1, L 180 (-104) 0 0 0 0⟩],
  -- 2
  [
    ⟨[7, 9, 29, 4], L 180 (-104) 0 0 0 0, L 38 (-22) 0 0 0 0⟩,
    ⟨[9, 22, 29, 4], L 38 (-22) 0 0 0 0, L 289 (-167) 2 (-1) 0 0⟩],
  -- 3
  [
    ⟨[7, 9, 28, 20], L 180 (-104) 0 0 0 0, L 38 (-22) 0 0 0 0⟩,
    ⟨[10, 13, 1, 2], L 38 (-22) 0 0 0 0, L 142 (-82) 0 0 0 0⟩,
    ⟨[9, 23, 20, 17], L 142 (-82) 0 0 0 0, L 142 (-82) 0 0 0 0⟩],
  -- 4
  [
    ⟨[7, 9, 28, 5], L 180 (-104) 0 0 0 0, L 38 (-22) 0 0 0 0⟩,
    ⟨[9, 23, 14, 7], L 38 (-22) 0 0 0 0, L 142 (-82) 0 0 0 0⟩],
  -- 5
  [
    ⟨[7, 9, 29, 4], L 175 (-101) (-2) 1 0 0, L 38 (-22) 0 0 0 0⟩,
    ⟨[10, 13, 1, 4], L 38 (-22) 0 0 0 0, L 284 (-164) 0 0 0 0⟩,
    ⟨[10, 12, 23, 25], L 284 (-164) 0 0 0 0, L 284 (-164) 0 0 0 0⟩],
  -- 6
  [
    ⟨[5, 14, 5, 20], L 33 (-19) (-2) 1 0 0, L 104 (-60) 0 0 0 0⟩],
  -- 7
  [
    ⟨[5, 22, 23, 20], L (-104) 60 0 0 0 0, L 0 0 0 0 0 0⟩],
  -- 8
  [
    ⟨[10, 12, 23, 25], L 284 (-164) 0 0 0 0, L 142 (-82) 0 0 0 0⟩,
    ⟨[10, 19, 23, 25], L 142 (-82) 0 0 0 0, L 142 (-82) 0 0 0 0⟩],
  -- 9
  [
    ⟨[5, 22, 23, 21], L (-237) 137 0 0 (-2) 1, L 5 (-3) 2 (-1) 0 0⟩],
  -- 10
  [
    ⟨[9, 14, 6, 21], L 142 (-82) 0 0 0 0, L 237 (-137) 0 0 2 (-1)⟩],
  -- 11
  [
    ⟨[10, 19, 23, 25], L 142 (-82) 0 0 0 0, L 251 (-145) 2 (-1) 0 0⟩],
  -- 12
  [
    ⟨[12, 19, 23, 14], L 151 (-87) 0 0 (-2) 1, L 251 (-145) 2 (-1) 0 0⟩],
  -- 13
  [
    ⟨[12, 19, 23, 25], L 137 (-79) (-2) 1 0 0, L 101 (-59) 0 0 1 0⟩,
    ⟨[11, 0, 4, 7], L 101 (-59) 0 0 1 0, L 246 (-142) 0 0 0 0⟩],
  -- 14
  [
    ⟨[12, 19, 23, 14], L 137 (-79) (-2) 1 0 0, L 101 (-59) 0 0 1 0⟩,
    ⟨[11, 0, 4], L 101 (-59) 0 0 1 0, L 246 (-142) 0 0 0 0⟩],
  -- 15
  [
    ⟨[5, 5, 5, 17], L 0 0 0 0 0 0, L 71 (-41) 2 (-1) 0 0⟩],
  -- 16
  [
    ⟨[15, 6, 20, 17], L 0 0 0 0 0 0, L (-142) 82 0 0 0 0⟩],
  -- 17
  [
    ⟨[15, 5, 23, 20], L 0 0 0 0 0 0, L (-151) 87 0 0 2 (-1)⟩],
  -- 18
  [
    ⟨[15, 6, 24, 17], L (-142) 82 0 0 0 0, L (-33) 19 2 (-1) 0 0⟩],
  -- 19
  [
    ⟨[15, 5, 23, 25], L (-142) 82 0 0 0 0, L (-33) 19 2 (-1) 0 0⟩],
  -- 20
  [
    ⟨[11, 0, 4, 10], L 246 (-142) 0 0 0 0, L 95 (-55) 0 0 2 (-1)⟩],
  -- 21
  [
    ⟨[15, 6, 24, 20], L (-147) 85 (-2) 1 0 0, L (-183) 105 0 0 1 0⟩,
    ⟨[15, 8, 28, 20], L (-183) 105 0 0 1 0, L (-38) 22 0 0 0 0⟩,
    ⟨[17, 8, 28, 20], L (-38) 22 0 0 0 0, L (-38) 22 0 0 0 0⟩],
  -- 22
  [
    ⟨[5, 19, 23, 25], L (-147) 85 (-2) 1 0 0, L (-38) 22 0 0 0 0⟩,
    ⟨[5, 12, 23, 25], L (-38) 22 0 0 0 0, L (-38) 22 0 0 0 0⟩],
  -- 23
  [
    ⟨[12, 22, 23, 21], L 104 (-60) 0 0 0 0, L 341 (-197) 0 0 2 (-1)⟩],
  -- 24
  [
    ⟨[12, 23, 26, 20], L 104 (-60) 0 0 0 0, L 208 (-120) 0 0 0 0⟩,
    ⟨[12, 22, 28, 20], L 208 (-120) 0 0 0 0, L 208 (-120) 0 0 0 0⟩],
  -- 25
  [
    ⟨[17, 8, 28, 20], L (-38) 22 0 0 0 0, L (-189) 109 0 0 2 (-1)⟩],
  -- 26
  [
    ⟨[5, 13, 1, 7], L (-38) 22 0 0 0 0, L (-180) 104 0 0 0 0⟩,
    ⟨[5, 13, 1, 4], L (-180) 104 0 0 0 0, L (-180) 104 0 0 0 0⟩],
  -- 27
  [
    ⟨[17, 6, 26, 20], L (-180) 104 0 0 0 0, L 57 (-33) 0 0 2 (-1)⟩],
  -- 28
  [
    ⟨[12, 22, 27, 4], L 345 (-199) (-2) 1 0 0, L 208 (-120) 0 0 0 0⟩,
    ⟨[12, 22, 29, 4], L 208 (-120) 0 0 0 0, L 208 (-120) 0 0 0 0⟩],
  -- 29
  [
    ⟨[12, 22, 28, 20], L 208 (-120) 0 0 0 0, L 57 (-33) 0 0 2 (-1)⟩],
  -- 30
  [
    ⟨[12, 22, 29, 4], L 208 (-120) 0 0 0 0, L 57 (-33) 0 0 2 (-1)⟩]]

/-- `(2 Y₁)² = 572 - 330√3`, where `Y₁ = √(143 - 165√3/2)` is the first radical of the domain
end points. -/
def radicand₁ : Quad 3 := ⟨572, -330⟩

/-- `(2 Y₂)² = 580 - 334√3`, where `Y₂ = √(145 - 167√3/2)` is the second radical of the domain
end points. -/
def radicand₂ : Quad 3 := ⟨580, -334⟩

/-- The squared critical radius `40 - 22√3`. -/
def radiusSq : Quad 3 := ⟨40, -22⟩

/-- The unit `ε = 2 - √3`. -/
def unit : Quad 3 := ⟨2, -1⟩

/-- The critical point `p* = -2ζ + 4ζ² - 3ζ³`, in the model. -/
def pModel : CycQ 3 := ⟨0, -2, 4, -3⟩

/-- The direction `V = ζ⁵ + ζ⁶ = -1 - ζ + ζ³` of the critical chord, in the model. -/
def dirModel : CycQ 3 := ⟨-1, -1, 0, 1⟩

/-- Realization: every word of the family is valid at both end points of its domain, with the
listed action, at every radius `r ≥ √(40 - 22√3)`. -/
theorem realizeOK_family :
    realizeOK radiusSq radicand₁ radicand₂ pModel dirModel family = true := by
  decide +kernel

/-- Closure: the family is closed under rescaling by `ε = 2 - √3`. -/
theorem closureOK_family : closureOK radicand₁ radicand₂ unit family pieces = true := by
  decide +kernel

/-- The value of `radicand₁`. -/
theorem toReal_radicand₁ : radicand₁.toReal = 572 - 330 * t := by
  simp [radicand₁, Quad.toReal]
  ring

/-- The value of `radicand₂`. -/
theorem toReal_radicand₂ : radicand₂.toReal = 580 - 334 * t := by
  simp [radicand₂, Quad.toReal]
  ring

/-- The value of `radiusSq`. -/
theorem toReal_radiusSq : radiusSq.toReal = 40 - 22 * t := by
  simp [radiusSq, Quad.toReal]
  ring

/-- The value of `unit`. -/
theorem toReal_unit : unit.toReal = 2 - t := by
  simp [unit, Quad.toReal]
  ring

/-- `pModel` represents the critical point `p*`. -/
theorem embed_pModel : embed zeta pModel = pStar := by
  simp only [embed, pModel]
  rw [zeta_cube, zeta_sq, zeta_eq]
  apply Complex.ext <;> simp [pStar] <;> ring

/-- `dirModel` represents the chord direction `V`. -/
theorem embed_dirModel : embed zeta dirModel = chordDir := by
  simp only [embed, dirModel]
  rw [zeta_cube, zeta_sq, zeta_eq]
  apply Complex.ext <;> simp [chordDir] <;> ring

/-- Theorem A of the note `notes/proofs/critical-radius-n12.md`, orbit form: for every
`r ≥ √(40 - 22√3)` and every `k`, the orbit of `p*` contains `p* + 2 (2 - √3)^(k+2) V`. -/
theorem mem_orbit_pStar_pow {r : ℝ} (hr : √(40 - 22 * t) ≤ r) (k : ℕ) :
    pStar + ((2 * (2 - t) ^ (k + 2) : ℝ) : ℂ) * chordDir ∈ orbit 12 12 r r pStar := by
  have hs := sqrt_three_bounds
  have hh₁ : 0 ≤ radicand₁.toReal := by rw [toReal_radicand₁]; linarith
  have hh₂ : 0 ≤ radicand₂.toReal := by rw [toReal_radicand₂]; linarith
  have h0 : (L 0 0 0 0 0 0).val radicand₁ radicand₂ = 0 := by simp [Lin.val, L, Quad.toReal]
  have hlo : (family.getD 5 default).lo.val radicand₁ radicand₂ ≤ 0 := by
    have := Lin.val_le_of_le hh₁ hh₂ (x := (family.getD 5 default).lo) (y := L 0 0 0 0 0 0)
      (by decide +kernel)
    rwa [h0] at this
  have hhi : 0 ≤ (family.getD 5 default).hi.val radicand₁ radicand₂ := by
    have := Lin.val_le_of_le hh₁ hh₂ (x := L 0 0 0 0 0 0) (y := (family.getD 5 default).hi)
      (by decide +kernel)
    rwa [h0] at this
  have hε : 0 < unit.toReal := by rw [toReal_unit]; linarith
  have hε' : 0 ≤ unit.toReal ^ k := pow_nonneg hε.le k
  have key : _ ∈ orbit 12 12 r r (embed zeta pModel + ((0 : ℝ) : ℂ) * embed zeta dirModel) :=
    mem_orbit_of_checks isRoot_zeta hh₁ hh₂ hε realizeOK_family closureOK_family
      (r := r) (by rw [toReal_radiusSq]; exact hr) k (i := 5) (by decide)
      ⟨by nlinarith, by nlinarith⟩
  have hc : (family.getD 5 default).c.toReal = 28 - 16 * t := by
    simp [family, Quad.toReal]
    ring
  have e₁ : ract (family.getD 5 default).pos (unit.toReal ^ k *
      ((family.getD 5 default).c.toReal / 2)) 0 = 2 * (2 - t) ^ (k + 2) := by
    simp only [show (family.getD 5 default).pos = false from rfl, ract, Bool.false_eq_true,
      ite_false, hc, toReal_unit]
    have := sqrt_three_sq
    rw [pow_add]
    linear_combination (-2 * (2 - t) ^ k) * this
  rwa [embed_pModel, embed_dirModel, e₁, ofReal_zero, zero_mul, add_zero] at key

end TDCSG.Twelve

end
