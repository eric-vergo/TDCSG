/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TDCSG.CriticalRadius.Basic

/-!
# `GG₅(r)` is infinite for every `r ≥ √(3 + φ)`

This is Part A (Theorem A) of `notes/proofs/critical-radius-n5.md`, which is Theorem 2 of
arXiv:2302.12950 extended to all larger radii. Let `ζ = exp (2πi / 5)` and `φ` the golden ratio.
On the chord from `E' = -E` to `E = ζ - ζ²`, parametrized as `t ↦ t E` for `t ∈ [-1, 1]`, three
explicit words in the generators act as translations, and together they realize the rotation
`t ↦ t + 2/φ` of the circle `ℝ / 2ℤ`. Since `φ` is irrational, the orbit of `0` contains
infinitely many distinct points `t_k E`.

## Main definitions

* `TDCSG.Five.zeta`: the root of unity `ζ = exp (2πi / 5)`.
* `TDCSG.Five.Cyc`: elements `x₀ + x₁ ζ + x₂ ζ² + x₃ ζ³` of `ℤ[ζ]` by their integer coordinates,
  with the exact arithmetic used to check the words.
* `TDCSG.Five.pointE`: the end point `E = ζ - ζ²` of the critical chord.
* `TDCSG.Five.word₁`, `TDCSG.Five.word₂`, `TDCSG.Five.word₃`: the three words of §3.2 of the
  written proof.

## Main statements

* `TDCSG.Five.normSq_pointE_add_one`: `|E + 1|² = 3 + φ`, so `E` lies on the boundary circle of
  the left disk at the critical radius.
* `TDCSG.Five.infinite_orbit_zero`: for `r ≥ √(3 + φ)` the orbit of `0` is infinite.
* `TDCSG.Five.infinite_GG`: for `r ≥ √(3 + φ)` the group `GG 5 5 r r` is infinite.
* `TDCSG.Five.criticalRadius_le`: `criticalRadius 5 ≤ √(3 + φ)`.

## Implementation notes

Every disk test and every endpoint image of the three words is computed in the integer model
`TDCSG.Five.Cyc` and checked by `decide`. The model is linked to `ℂ` by
`TDCSG.Five.Cyc.embed`, which turns the model rotations into the global rotations of the
generators (`TDCSG.Five.Cyc.embed_step`), and the model disk test into membership in the closed
disk of radius `r ≥ √(3 + φ)` (`TDCSG.Five.Cyc.mem_closedBall_of_memCheck`). Squared distances
are elements `α + β φ` of `ℤ[φ]`, whose signs are decided by integer arithmetic
(`TDCSG.Five.nonnegCheck`).
-/

@[expose] public section

open Complex Metric Equiv
open scoped Real goldenRatio

namespace TDCSG.Five

/-! ### The fifth root of unity -/

/-- The primitive fifth root of unity `ζ = exp (2πi / 5)`. -/
noncomputable def zeta : ℂ := exp (2 * π * I / 5)

@[inherit_doc] local notation "ζ" => zeta

theorem isPrimitiveRoot_zeta : IsPrimitiveRoot ζ 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  rwa [Nat.cast_ofNat] at this

theorem zeta_pow_five : ζ ^ 5 = 1 :=
  isPrimitiveRoot_zeta.pow_eq_one

theorem one_add_zeta_add : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  have := isPrimitiveRoot_zeta.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  linear_combination this

theorem zeta_inv : ζ⁻¹ = ζ ^ 4 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', zeta_pow_five])

/-- The rotation factor `exp (-2πi / 5)` of the generators is `ζ⁴ = ζ⁻¹`. -/
theorem exp_rotationAngle_five : exp (-(2 * π * I / 5)) = ζ ^ 4 := by
  rw [exp_neg, ← zeta_inv, zeta]

theorem exp_two_pi_I_div_five : exp (2 * π * I / 5) = ζ :=
  rfl

theorem conj_zeta : (starRingEnd ℂ) ζ = ζ ^ 4 := by
  rw [← exp_rotationAngle_five, zeta, ← exp_conj,
    show 2 * π * I / 5 = ((2 * π / 5 : ℝ) : ℂ) * I by push_cast; ring]
  congr 1
  simp [conj_ofReal, map_ofNat]

/-- `ζ + ζ⁻¹ = 2 cos (2π / 5) = φ - 1`. -/
theorem zeta_add_zeta_pow_four : ζ + ζ ^ 4 = (φ : ℂ) - 1 := by
  have hre : zeta.re = Real.cos (2 * π / 5) := by
    rw [zeta, show 2 * π * I / 5 = ((2 * π / 5 : ℝ) : ℂ) * I by push_cast; ring,
      exp_ofReal_mul_I_re]
  have hcos : Real.cos (2 * π / 5) = (φ - 1) / 2 := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five,
      Real.goldenRatio]
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    linear_combination h5 / 8
  rw [← conj_zeta, add_conj, hre, hcos]
  push_cast
  ring

/-- `ζ² + ζ³ = -φ`. -/
theorem zeta_sq_add_zeta_cube : ζ ^ 2 + ζ ^ 3 = -(φ : ℂ) := by
  linear_combination one_add_zeta_add - zeta_add_zeta_pow_four

/-! ### Signs in `ℤ[φ]` -/

/-- An exact test for `0 ≤ a + b φ`: writing `a + b φ = (u + v √5) / 2` with `u = 2a + b` and
`v = b`, compare signs and, if they differ, the squares `u²` and `5 v²`. -/
def nonnegCheck (a b : ℤ) : Bool :=
  decide ((0 ≤ 2 * a + b ∧ 0 ≤ b) ∨ (0 ≤ 2 * a + b ∧ b < 0 ∧ 5 * b ^ 2 ≤ (2 * a + b) ^ 2) ∨
    (2 * a + b < 0 ∧ 0 < b ∧ (2 * a + b) ^ 2 ≤ 5 * b ^ 2))

theorem nonneg_of_nonnegCheck {a b : ℤ} (h : nonnegCheck a b = true) :
    0 ≤ (a : ℝ) + b * φ := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have key : (a : ℝ) + b * φ = ((2 * a + b : ℤ) + (b : ℤ) * Real.sqrt 5) / 2 := by
    rw [Real.goldenRatio]
    push_cast
    ring
  rw [key]
  apply div_nonneg _ (by norm_num)
  set u : ℤ := 2 * a + b
  simp only [nonnegCheck, decide_eq_true_eq] at h
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv, hsq⟩ | ⟨hu, hv, hsq⟩
  · have hu' : (0 : ℝ) ≤ u := by exact_mod_cast hu
    have hv' : (0 : ℝ) ≤ b := by exact_mod_cast hv
    positivity
  · have hu' : (0 : ℝ) ≤ u := by exact_mod_cast hu
    have hv' : (b : ℝ) < 0 := by exact_mod_cast hv
    have hsq' : 5 * (b : ℝ) ^ 2 ≤ (u : ℝ) ^ 2 := by exact_mod_cast hsq
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -b) hs]
  · have hu' : (u : ℝ) < 0 := by exact_mod_cast hu
    have hv' : (0 : ℝ) < b := by exact_mod_cast hv
    have hsq' : (u : ℝ) ^ 2 ≤ 5 * (b : ℝ) ^ 2 := by exact_mod_cast hsq
    nlinarith [mul_nonneg hv'.le hs]

/-! ### The integer model of `ℤ[ζ]` -/

/-- The element `c0 + c1 ζ + c2 ζ² + c3 ζ³` of `ℤ[ζ]`, by its coordinates in the basis
`1, ζ, ζ², ζ³`. -/
@[ext]
structure Cyc where
  /-- The coordinate of `1`. -/
  c0 : ℤ
  /-- The coordinate of `ζ`. -/
  c1 : ℤ
  /-- The coordinate of `ζ²`. -/
  c2 : ℤ
  /-- The coordinate of `ζ³`. -/
  c3 : ℤ
  deriving DecidableEq, Repr

namespace Cyc

/-- The complex number represented by an element of the model. -/
noncomputable def embed (v : Cyc) : ℂ := v.c0 + v.c1 * ζ + v.c2 * ζ ^ 2 + v.c3 * ζ ^ 3

instance : Add Cyc := ⟨fun v w ↦ ⟨v.c0 + w.c0, v.c1 + w.c1, v.c2 + w.c2, v.c3 + w.c3⟩⟩
instance : Sub Cyc := ⟨fun v w ↦ ⟨v.c0 - w.c0, v.c1 - w.c1, v.c2 - w.c2, v.c3 - w.c3⟩⟩
instance : SMul ℤ Cyc := ⟨fun k v ↦ ⟨k * v.c0, k * v.c1, k * v.c2, k * v.c3⟩⟩

theorem add_def (v w : Cyc) : v + w = ⟨v.c0 + w.c0, v.c1 + w.c1, v.c2 + w.c2, v.c3 + w.c3⟩ :=
  rfl

theorem sub_def (v w : Cyc) : v - w = ⟨v.c0 - w.c0, v.c1 - w.c1, v.c2 - w.c2, v.c3 - w.c3⟩ :=
  rfl

theorem smul_def (k : ℤ) (v : Cyc) : k • v = ⟨k * v.c0, k * v.c1, k * v.c2, k * v.c3⟩ :=
  rfl

/-- Multiplication by `ζ`, using `ζ⁴ = -1 - ζ - ζ² - ζ³`. -/
def mulZeta (v : Cyc) : Cyc := ⟨-v.c3, v.c0 - v.c3, v.c1 - v.c3, v.c2 - v.c3⟩

/-- Multiplication by `ζ⁻¹ = ζ⁴`. -/
def mulZetaInv (v : Cyc) : Cyc := ⟨v.c1 - v.c0, v.c2 - v.c0, v.c3 - v.c0, -v.c0⟩

/-- Complex conjugation, which sends `ζ` to `ζ⁴`. -/
def conj (v : Cyc) : Cyc := ⟨v.c0 - v.c1, -v.c1, v.c3 - v.c1, v.c2 - v.c1⟩

/-- Multiplication in `ℤ[ζ]`. -/
def mul (v w : Cyc) : Cyc :=
  v.c0 • w + v.c1 • mulZeta w + v.c2 • mulZeta (mulZeta w) +
    v.c3 • mulZeta (mulZeta (mulZeta w))

/-- Multiplication by `φ = 1 + ζ + ζ⁴`. -/
def mulPhi (v : Cyc) : Cyc := v + mulZeta v + mulZetaInv v

@[simp] theorem embed_add (v w : Cyc) : embed (v + w) = embed v + embed w := by
  simp only [embed, add_def]
  push_cast
  ring

@[simp] theorem embed_sub (v w : Cyc) : embed (v - w) = embed v - embed w := by
  simp only [embed, sub_def]
  push_cast
  ring

@[simp] theorem embed_smul (k : ℤ) (v : Cyc) : embed (k • v) = k * embed v := by
  simp only [embed, smul_def]
  push_cast
  ring

@[simp] theorem embed_mulZeta (v : Cyc) : embed (mulZeta v) = ζ * embed v := by
  simp only [embed, mulZeta]
  push_cast
  linear_combination (-(v.c3 : ℂ)) * one_add_zeta_add

@[simp] theorem embed_mulZetaInv (v : Cyc) : embed (mulZetaInv v) = ζ ^ 4 * embed v := by
  simp only [embed, mulZetaInv]
  push_cast
  linear_combination (-(v.c0 : ℂ)) * one_add_zeta_add -
    ((v.c1 : ℂ) + v.c2 * ζ + v.c3 * ζ ^ 2) * zeta_pow_five

theorem embed_conj (v : Cyc) : embed (conj v) = (starRingEnd ℂ) (embed v) := by
  simp only [embed, conj, map_add, map_mul, map_intCast, map_pow, conj_zeta]
  push_cast
  linear_combination (-(v.c1 : ℂ)) * one_add_zeta_add -
    ((v.c2 : ℂ) * ζ ^ 3 + v.c3 * ζ ^ 2 * (ζ ^ 5 + 1)) * zeta_pow_five

theorem embed_mul (v w : Cyc) : embed (mul v w) = embed v * embed w := by
  simp only [mul, embed_add, embed_smul, embed_mulZeta]
  simp only [embed]
  ring

theorem embed_mulPhi (v : Cyc) : embed (mulPhi v) = φ * embed v := by
  simp only [mulPhi, embed_add, embed_mulZeta, embed_mulZetaInv]
  linear_combination (embed v) * zeta_add_zeta_pow_four

/-- If `v v̄ = y` has the shape `y₀ + y₂ (ζ² + ζ³)` of an element of `ℤ[φ]`, then
`|v|² = y₀ - y₂ φ`. -/
theorem norm_sq_embed {v : Cyc} (h1 : (mul v (conj v)).c1 = 0)
    (h3 : (mul v (conj v)).c3 = (mul v (conj v)).c2) :
    ‖embed v‖ ^ 2 = (mul v (conj v)).c0 - (mul v (conj v)).c2 * φ := by
  have h : ((‖embed v‖ ^ 2 : ℝ) : ℂ) = embed (mul v (conj v)) := by
    rw [embed_mul, embed_conj, mul_conj']
    push_cast
    rfl
  set y := mul v (conj v)
  rw [show embed y = y.c0 + y.c1 * ζ + y.c2 * ζ ^ 2 + y.c3 * ζ ^ 3 from rfl, h1, h3] at h
  have h' : ((‖embed v‖ ^ 2 : ℝ) : ℂ) = ((y.c0 - y.c2 * φ : ℝ) : ℂ) := by
    rw [h]
    simp only [ofReal_sub, ofReal_mul, ofReal_intCast, Int.cast_zero]
    linear_combination (y.c2 : ℂ) * zeta_sq_add_zeta_cube
  exact_mod_cast h'

/-- The exact test that `v` lies in the closed disk of radius `√(3 + φ)` about `c`. -/
def memCheck (c v : Cyc) : Bool :=
  let y := mul (v - c) (conj (v - c))
  decide (y.c1 = 0) && decide (y.c3 = y.c2) && nonnegCheck (3 - y.c0) (1 + y.c2)

theorem mem_closedBall_of_memCheck {c v : Cyc} (h : memCheck c v = true) {r : ℝ}
    (hr : √(3 + φ) ≤ r) : embed v ∈ closedBall (embed c) r := by
  simp only [memCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h3⟩, hn⟩ := h
  have hsq := norm_sq_embed h1 h3
  have hn' := nonneg_of_nonnegCheck hn
  push_cast at hn'
  rw [mem_closedBall, dist_eq_norm, ← embed_sub]
  refine le_trans ?_ hr
  rw [← abs_norm]
  exact Real.abs_le_sqrt (by rw [hsq]; linarith)

/-- The centre `-1` of the left disk. -/
def left : Cyc := ⟨-1, 0, 0, 0⟩

/-- The centre `1` of the right disk. -/
def right : Cyc := ⟨1, 0, 0, 0⟩

/-- The centre of the disk of a letter, in the model. -/
def center : Letter → Cyc
  | .a | .aInv => left
  | .b | .bInv => right

theorem embed_center (l : Letter) : embed (center l) = l.center := by
  cases l <;> simp [center, left, right, embed, Letter.center, leftCenter, rightCenter]

/-- The global rotation of a letter, in the model. -/
def step : Letter → Cyc → Cyc
  | .a, v => left + mulZetaInv (v - left)
  | .aInv, v => left + mulZeta (v - left)
  | .b, v => right + mulZetaInv (v - right)
  | .bInv, v => right + mulZeta (v - right)

theorem embed_step (l : Letter) (v : Cyc) : embed (step l v) = l.glob 5 (embed v) := by
  have hl := embed_center .a
  have hr := embed_center .b
  simp only [center] at hl hr
  cases l <;>
    simp [step, Letter.glob, Letter.factor, Letter.center, embed_add, embed_sub,
      embed_mulZeta, embed_mulZetaInv, hl, hr, exp_rotationAngle_five, exp_two_pi_I_div_five]

/-- The exact test that a word is valid on the segment from `P` to `Q` at every radius
`r ≥ √(3 + φ)`. -/
def valid : List Letter → Cyc → Cyc → Bool
  | [], _, _ => true
  | l :: w, P, Q => memCheck (center l) P && memCheck (center l) Q &&
      valid w (step l P) (step l Q)

/-- The composite global rotation of a word, in the model. -/
def run : List Letter → Cyc → Cyc
  | [], v => v
  | l :: w, v => run w (step l v)

theorem embed_run (w : List Letter) (v : Cyc) : embed (run w v) = globalWord 5 w (embed v) := by
  induction w generalizing v with
  | nil => rfl
  | cons l w ih => rw [run, ih, globalWord, embed_step]

theorem wordValid_of_valid {w : List Letter} {P Q : Cyc} (h : valid w P Q = true) {r : ℝ}
    (hr : √(3 + φ) ≤ r) : WordValid 5 r w (embed P) (embed Q) := by
  induction w generalizing P Q with
  | nil => trivial
  | cons l w ih =>
    simp only [valid, Bool.and_eq_true] at h
    obtain ⟨⟨hP, hQ⟩, hw⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · rw [← embed_center]
      exact mem_closedBall_of_memCheck hP hr
    · rw [← embed_center]
      exact mem_closedBall_of_memCheck hQ hr
    · rw [← embed_step, ← embed_step]
      exact ih hw

/-- The exact check that `w` is valid on the segment from `P` to `Q` and maps `P` to `P'` and
`Q` to `Q'`. -/
def wordCheck (w : List Letter) (P Q P' Q' : Cyc) : Bool :=
  valid w P Q && decide (run w P = P') && decide (run w Q = Q')

end Cyc

/-! ### The critical chord and the three words -/

open Cyc

/-- The end point `E = ζ - ζ²` of the critical chord. -/
def pointE : Cyc := ⟨0, 1, -1, 0⟩

/-- `|E + 1|² = 3 + φ`: at radius `√(3 + φ)` the point `E` lies on the boundary circle of the
left disk. -/
theorem normSq_pointE_add_one : ‖embed pointE + 1‖ ^ 2 = 3 + φ := by
  have h := norm_sq_embed (v := pointE - left) (by decide) (by decide)
  rw [embed_sub, show embed left = -1 by simp [embed, left]] at h
  rw [show embed pointE + 1 = embed pointE - -1 by ring, h]
  have : (mul (pointE - left) (conj (pointE - left))) = ⟨3, 0, -1, -1⟩ := by decide
  rw [this]
  push_cast
  ring

theorem embed_pointE_ne_zero : embed pointE ≠ 0 := by
  have h : embed pointE = ζ * (1 - ζ) := by
    simp [embed, pointE]
    ring
  rw [h]
  exact mul_ne_zero (isPrimitiveRoot_zeta.ne_zero (by norm_num))
    (sub_ne_zero.2 (isPrimitiveRoot_zeta.ne_one (by norm_num)).symm)

/-- The lattice point `(p + q φ) E` of the critical chord. -/
def chordPt (p q : ℤ) : Cyc := p • pointE + q • mulPhi pointE

theorem embed_chordPt (p q : ℤ) : embed (chordPt p q) = ((p + q * φ : ℝ) : ℂ) * embed pointE := by
  simp only [chordPt, embed_add, embed_smul, embed_mulPhi]
  push_cast
  ring

/-- A word checked on a segment of the chord translates every point of the segment along the
chord. -/
theorem applyWord_chord {r : ℝ} (hr : √(3 + φ) ≤ r) {w : List Letter}
    {p₀ q₀ p₁ q₁ dp dq : ℤ}
    (hcheck : wordCheck w (chordPt p₀ q₀) (chordPt p₁ q₁) (chordPt (p₀ + dp) (q₀ + dq))
      (chordPt (p₁ + dp) (q₁ + dq)) = true)
    (hlt : (p₀ + q₀ * φ : ℝ) < p₁ + q₁ * φ) {t : ℝ}
    (ht : t ∈ Set.Icc (p₀ + q₀ * φ : ℝ) (p₁ + q₁ * φ)) :
    applyWord 5 r w (t * embed pointE) = ((t + (dp + dq * φ) : ℝ) : ℂ) * embed pointE := by
  simp only [wordCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hv, h₀⟩, h₁⟩ := hcheck
  have hv' := wordValid_of_valid hv hr
  rw [embed_chordPt, embed_chordPt] at hv'
  refine applyWord_line hlt hv' ?_ ?_ ht
  · rw [← embed_chordPt, ← embed_run, h₀, embed_chordPt]
    push_cast
    ring_nf
  · rw [← embed_chordPt, ← embed_run, h₁, embed_chordPt]
    push_cast
    ring_nf

/-- The word `a⁻¹ a⁻¹ b⁻¹ a⁻¹ b⁻¹`, mapping `[E', F']` onto `[G, F]`. -/
def word₁ : List Letter := [.aInv, .aInv, .bInv, .aInv, .bInv]

/-- The word `a b a b b`, mapping `[F', G']` onto `[F, E]`. -/
def word₂ : List Letter := [.a, .b, .a, .b, .b]

/-- The word `a b a b⁻¹ a⁻¹ b⁻¹`, mapping `[G', E]` onto `[E', G]`. -/
def word₃ : List Letter := [.a, .b, .a, .bInv, .aInv, .bInv]

theorem one_lt_phi : 1 < φ := Real.one_lt_goldenRatio
theorem phi_lt_two : φ < 2 := Real.goldenRatio_lt_two

/-- On `[-1, 1 - φ]`, that is on `[E', F']`, the word `word₁` translates by `2φ - 2 = 2/φ`. -/
theorem applyWord_word₁ {r : ℝ} (hr : √(3 + φ) ≤ r) {t : ℝ} (ht : t ∈ Set.Icc (-1) (1 - φ)) :
    applyWord 5 r word₁ (t * embed pointE) = ((t + (2 * φ - 2) : ℝ) : ℂ) * embed pointE := by
  have := applyWord_chord (p₀ := -1) (q₀ := 0) (p₁ := 1) (q₁ := -1) (dp := -2) (dq := 2)
    (w := word₁) hr (by decide) (by push_cast; linarith [phi_lt_two]) (t := t)
    (by push_cast; constructor <;> linarith [ht.1, ht.2])
  rw [this]
  push_cast
  ring

/-- On `[1 - φ, 3 - 2φ]`, that is on `[F', G']`, the word `word₂` translates by `2φ - 2`. -/
theorem applyWord_word₂ {r : ℝ} (hr : √(3 + φ) ≤ r) {t : ℝ}
    (ht : t ∈ Set.Icc (1 - φ) (3 - 2 * φ)) :
    applyWord 5 r word₂ (t * embed pointE) = ((t + (2 * φ - 2) : ℝ) : ℂ) * embed pointE := by
  have := applyWord_chord (p₀ := 1) (q₀ := -1) (p₁ := 3) (q₁ := -2) (dp := -2) (dq := 2)
    (w := word₂) hr (by decide) (by push_cast; linarith [phi_lt_two]) (t := t)
    (by push_cast; constructor <;> linarith [ht.1, ht.2])
  rw [this]
  push_cast
  ring

/-- On `[3 - 2φ, 1]`, that is on `[G', E]`, the word `word₃` translates by `2φ - 4 = -2/φ²`. -/
theorem applyWord_word₃ {r : ℝ} (hr : √(3 + φ) ≤ r) {t : ℝ} (ht : t ∈ Set.Icc (3 - 2 * φ) 1) :
    applyWord 5 r word₃ (t * embed pointE) = ((t + (2 * φ - 4) : ℝ) : ℂ) * embed pointE := by
  have := applyWord_chord (p₀ := 3) (q₀ := -2) (p₁ := 1) (q₁ := 0) (dp := -4) (dq := 2)
    (w := word₃) hr (by decide) (by push_cast; linarith [one_lt_phi]) (t := t)
    (by push_cast; constructor <;> linarith [ht.1, ht.2])
  rw [this]
  push_cast
  ring

/-! ### The infinite orbit -/

/-- The orbit of `0` contains the points `t_k E`, with `t_k ∈ [-1, 1)` and
`t_k ≡ k (2φ - 2) mod 2`. -/
theorem exists_mem_orbit {r : ℝ} (hr : √(3 + φ) ≤ r) (k : ℕ) :
    ∃ t : ℝ, ∃ m : ℤ, t ∈ Set.Ico (-1) 1 ∧ t = k * (2 * φ - 2) + 2 * m ∧
      (t : ℂ) * embed pointE ∈ orbit 5 5 r r 0 := by
  induction k with
  | zero => exact ⟨0, 0, ⟨by norm_num, by norm_num⟩, by simp, by simp [mem_orbit_self]⟩
  | succ k ih =>
    obtain ⟨t, m, ⟨ht₀, ht₁⟩, htm, hmem⟩ := ih
    have h1 := one_lt_phi
    have h2 := phi_lt_two
    rcases le_or_gt t (1 - φ) with h | h
    · refine ⟨t + (2 * φ - 2), m, ⟨by linarith, by linarith⟩, by rw [htm]; push_cast; ring, ?_⟩
      rw [← applyWord_word₁ hr ⟨ht₀, h⟩]
      exact applyWord_mem_orbit _ hmem
    rcases lt_or_ge t (3 - 2 * φ) with h' | h'
    · refine ⟨t + (2 * φ - 2), m, ⟨by linarith, by linarith⟩, by rw [htm]; push_cast; ring, ?_⟩
      rw [← applyWord_word₂ hr ⟨h.le, h'.le⟩]
      exact applyWord_mem_orbit _ hmem
    · refine ⟨t + (2 * φ - 4), m - 1, ⟨by linarith, by linarith⟩, by rw [htm]; push_cast; ring,
        ?_⟩
      rw [← applyWord_word₃ hr ⟨h', ht₁.le⟩]
      exact applyWord_mem_orbit _ hmem

/-- **Theorem A**, orbit form: for every `r ≥ √(3 + φ)` the orbit of `0` under `GG 5 5 r r` is
infinite. -/
theorem infinite_orbit_zero {r : ℝ} (hr : √(3 + φ) ≤ r) : (orbit 5 5 r r 0).Infinite := by
  choose t m ht htm hmem using exists_mem_orbit hr
  refine Set.infinite_of_injective_forall_mem (f := fun k ↦ (t k : ℂ) * embed pointE)
    (fun k l hkl ↦ ?_) hmem
  have hkl' : t k = t l := by
    have := mul_right_cancel₀ embed_pointE_ne_zero hkl
    exact_mod_cast this
  rw [htm k, htm l] at hkl'
  by_contra hne
  have hd : ((k : ℤ) - l : ℝ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hne
  apply Real.goldenRatio_irrational.ne_rational (((k : ℤ) - l) + (m l - m k)) ((k : ℤ) - l)
  push_cast at hd ⊢
  rw [eq_div_iff hd]
  linear_combination hkl' / 2

/-- **Theorem A**: for every `r ≥ √(3 + φ)` the group `GG 5 5 r r` is infinite. -/
theorem infinite_GG {r : ℝ} (hr : √(3 + φ) ≤ r) : Infinite (GG 5 5 r r) :=
  infinite_GG_of_infinite_orbit (infinite_orbit_zero hr)

/-- The critical radius of `GG₅` is at most `√(3 + φ)`. -/
theorem criticalRadius_le : criticalRadius 5 ≤ √(3 + φ) :=
  TDCSG.criticalRadius_le (infinite_GG le_rfl)

end TDCSG.Five

end
