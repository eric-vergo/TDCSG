/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude, OpenAI GPT-6.2 Astra
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TDCSG.CriticalRadius.Basic

/-!
# The fifth root of unity and an exact model of `ℤ[ζ₅]`

Let `ζ = exp (2πi / 5)` and `φ` the golden ratio. This file proves the identities of `ζ` and `φ`
used by the fivefold argument, and sets up a computable model of `ℤ[ζ]` in which the disk tests
and the actions of words in the generators of `GG n n r r` are decided exactly. The model is
shared with the case `n = 10`, since `ℤ[exp (2πi / 10)] = ℤ[ζ]`.

## Main definitions

* `TDCSG.Five.zeta`: the root of unity `ζ = exp (2πi / 5)`.
* `TDCSG.Five.nonnegCheck`: an exact test for `0 ≤ a + b φ` with `a, b ∈ ℤ`.
* `TDCSG.Five.Cyc`: elements `x₀ + x₁ ζ + x₂ ζ² + x₃ ζ³` of `ℤ[ζ]` by their integer coordinates,
  with the exact arithmetic of `ℤ[ζ]`; `TDCSG.Five.Cyc.embed` is the embedding into `ℂ`.
* `TDCSG.Five.Cyc.memCheckAt`: an exact test for membership in a closed disk of radius
  `√(α + β φ)`.
* `TDCSG.Five.Cyc.Model`: an integer model of the generators of `GG n n r r` acting on `ℤ[ζ]`,
  with exact disk tests at a radius `√(α + β φ)`; `TDCSG.Five.Cyc.pentagon` is the model for
  `n = 5`.
* `TDCSG.Five.Cyc.linePt`: the lattice point `(p + q φ) V` of the line through `0` in the
  direction `V`.

## Main statements

* `TDCSG.Five.zeta_add_zeta_pow_four`, `TDCSG.Five.zeta_sq_add_zeta_cube`:
  `ζ + ζ⁴ = φ - 1` and `ζ² + ζ³ = -φ`.
* `TDCSG.Five.re_zeta`, `TDCSG.Five.re_zeta_sq`: `Re ζ = (φ - 1) / 2` and `Re ζ² = -φ / 2`.
* `TDCSG.Five.nonneg_of_nonnegCheck`: the sign test is sound.
* `TDCSG.Five.Cyc.mem_closedBall_of_memCheckAt`: the disk test is sound at every radius
  `r ≥ √(α + β φ)`.
* `TDCSG.Five.Cyc.Model.IsSound.applyWord_linePt`: a word whose exact check passes on a segment
  of a line through `0` translates every point of the segment along the line, at every radius
  `r ≥ √(α + β φ)`.

## Implementation notes

Squared distances in `ℤ[ζ]` that are real lie in `ℤ[φ]`; their signs are decided by integer
arithmetic (`TDCSG.Five.nonnegCheck`), so every check is a `Bool` that `decide` evaluates.
-/

@[expose] public section

open Complex Metric Equiv
open scoped Real goldenRatio

namespace TDCSG.Five

/-! ### The fifth root of unity -/

/-- The primitive fifth root of unity `ζ = exp (2πi / 5)`. -/
noncomputable def zeta : ℂ := exp (2 * π * I / 5)

@[inherit_doc] local notation "ζ" => zeta

/-- `ζ` is a primitive fifth root of unity. -/
theorem isPrimitiveRoot_zeta : IsPrimitiveRoot ζ 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  rwa [Nat.cast_ofNat] at this

/-- `ζ⁵ = 1`. -/
theorem zeta_pow_five : ζ ^ 5 = 1 :=
  isPrimitiveRoot_zeta.pow_eq_one

/-- `|ζ| = 1`. -/
theorem norm_zeta : ‖ζ‖ = 1 :=
  isPrimitiveRoot_zeta.norm'_eq_one (by norm_num)

/-- Powers of `ζ` only depend on the exponent modulo `5`. -/
theorem zeta_pow_mod (k : ℕ) : ζ ^ (k % 5) = ζ ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k 5, pow_add, pow_mul, zeta_pow_five, one_pow, mul_one]

/-- The powers of `ζ` sum to zero: `1 + ζ + ζ² + ζ³ + ζ⁴ = 0`. -/
theorem one_add_zeta_add : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  have := isPrimitiveRoot_zeta.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  linear_combination this

/-- `ζ⁻¹ = ζ⁴`. -/
theorem zeta_inv : ζ⁻¹ = ζ ^ 4 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', zeta_pow_five])

/-- The rotation factor `exp (-2πi / 5)` of the generators is `ζ⁴ = ζ⁻¹`. -/
theorem exp_rotationAngle_five : exp (-(2 * π * I / 5)) = ζ ^ 4 := by
  rw [exp_neg, ← zeta_inv, zeta]

/-- The rotation factor `exp (2πi / 5)` of `a⁻¹` and `b⁻¹` is `ζ`. -/
theorem exp_two_pi_I_div_five : exp (2 * π * I / 5) = ζ :=
  rfl

/-- Complex conjugation sends `ζ` to `ζ⁴`. -/
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

/-- `conj ζ² = ζ³`. -/
theorem conj_zeta_sq : (starRingEnd ℂ) (ζ ^ 2) = ζ ^ 3 := by
  rw [map_pow, conj_zeta, ← pow_mul, ← zeta_pow_mod 8]

/-- `Re ζ = cos (2π / 5) = (φ - 1) / 2`. -/
theorem re_zeta : (ζ).re = (φ - 1) / 2 := by
  have h := congrArg Complex.re zeta_add_zeta_pow_four
  rw [← conj_zeta] at h
  simp only [add_re, conj_re, sub_re, ofReal_re, one_re] at h
  linarith

/-- `Re ζ⁴ = Re ζ = (φ - 1) / 2`. -/
theorem re_zeta_pow_four : (ζ ^ 4).re = (φ - 1) / 2 := by
  rw [← conj_zeta, conj_re, re_zeta]

/-- `Re ζ² = cos (4π / 5) = -φ / 2`. -/
theorem re_zeta_sq : (ζ ^ 2).re = -φ / 2 := by
  have h := congrArg Complex.re zeta_sq_add_zeta_cube
  rw [← conj_zeta_sq] at h
  simp only [add_re, conj_re, neg_re, ofReal_re] at h
  linarith

/-- `Re ζ³ = Re ζ² = -φ / 2`. -/
theorem re_zeta_pow_three : (ζ ^ 3).re = -φ / 2 := by
  rw [← conj_zeta_sq, conj_re, re_zeta_sq]

/-! ### Signs in `ℤ[φ]` -/

/-- An exact test for `0 ≤ a + b φ`: writing `a + b φ = (u + v √5) / 2` with `u = 2a + b` and
`v = b`, compare signs and, if they differ, the squares `u²` and `5 v²`. -/
def nonnegCheck (a b : ℤ) : Bool :=
  decide ((0 ≤ 2 * a + b ∧ 0 ≤ b) ∨ (0 ≤ 2 * a + b ∧ b < 0 ∧ 5 * b ^ 2 ≤ (2 * a + b) ^ 2) ∨
    (2 * a + b < 0 ∧ 0 < b ∧ (2 * a + b) ^ 2 ≤ 5 * b ^ 2))

/-- The test `TDCSG.Five.nonnegCheck` is sound. -/
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

/-- `1` and `φ` are linearly independent over `ℤ`. -/
theorem eq_zero_of_add_mul_phi_eq_zero {a b : ℤ} (h : (a : ℝ) + b * φ = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    apply Real.goldenRatio_irrational.ne_rational (-a) b
    push_cast
    rw [eq_div_iff hb']
    linarith
  subst hb
  exact ⟨by simpa using h, rfl⟩

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

/-- Coordinatewise addition. -/
instance : Add Cyc := ⟨fun v w ↦ ⟨v.c0 + w.c0, v.c1 + w.c1, v.c2 + w.c2, v.c3 + w.c3⟩⟩
/-- Coordinatewise subtraction. -/
instance : Sub Cyc := ⟨fun v w ↦ ⟨v.c0 - w.c0, v.c1 - w.c1, v.c2 - w.c2, v.c3 - w.c3⟩⟩
/-- Coordinatewise multiplication by an integer. -/
instance : SMul ℤ Cyc := ⟨fun k v ↦ ⟨k * v.c0, k * v.c1, k * v.c2, k * v.c3⟩⟩

/-- Addition is coordinatewise. -/
theorem add_def (v w : Cyc) : v + w = ⟨v.c0 + w.c0, v.c1 + w.c1, v.c2 + w.c2, v.c3 + w.c3⟩ :=
  rfl

/-- Subtraction is coordinatewise. -/
theorem sub_def (v w : Cyc) : v - w = ⟨v.c0 - w.c0, v.c1 - w.c1, v.c2 - w.c2, v.c3 - w.c3⟩ :=
  rfl

/-- Multiplication by an integer is coordinatewise. -/
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

/-- The embedding is additive. -/
@[simp] theorem embed_add (v w : Cyc) : embed (v + w) = embed v + embed w := by
  simp only [embed, add_def]
  push_cast
  ring

/-- The embedding commutes with subtraction. -/
@[simp] theorem embed_sub (v w : Cyc) : embed (v - w) = embed v - embed w := by
  simp only [embed, sub_def]
  push_cast
  ring

/-- The embedding commutes with multiplication by an integer. -/
@[simp] theorem embed_smul (k : ℤ) (v : Cyc) : embed (k • v) = k * embed v := by
  simp only [embed, smul_def]
  push_cast
  ring

/-- `TDCSG.Five.Cyc.mulZeta` is multiplication by `ζ`. -/
@[simp] theorem embed_mulZeta (v : Cyc) : embed (mulZeta v) = ζ * embed v := by
  simp only [embed, mulZeta]
  push_cast
  linear_combination (-(v.c3 : ℂ)) * one_add_zeta_add

/-- `TDCSG.Five.Cyc.mulZetaInv` is multiplication by `ζ⁴`. -/
@[simp] theorem embed_mulZetaInv (v : Cyc) : embed (mulZetaInv v) = ζ ^ 4 * embed v := by
  simp only [embed, mulZetaInv]
  push_cast
  linear_combination (-(v.c0 : ℂ)) * one_add_zeta_add -
    ((v.c1 : ℂ) + v.c2 * ζ + v.c3 * ζ ^ 2) * zeta_pow_five

/-- `TDCSG.Five.Cyc.conj` is complex conjugation. -/
theorem embed_conj (v : Cyc) : embed (conj v) = (starRingEnd ℂ) (embed v) := by
  simp only [embed, conj, map_add, map_mul, map_intCast, map_pow, conj_zeta]
  push_cast
  linear_combination (-(v.c1 : ℂ)) * one_add_zeta_add -
    ((v.c2 : ℂ) * ζ ^ 3 + v.c3 * ζ ^ 2 * (ζ ^ 5 + 1)) * zeta_pow_five

/-- `TDCSG.Five.Cyc.mul` is multiplication in `ℂ`. -/
theorem embed_mul (v w : Cyc) : embed (mul v w) = embed v * embed w := by
  simp only [mul, embed_add, embed_smul, embed_mulZeta]
  simp only [embed]
  ring

/-- `TDCSG.Five.Cyc.mulPhi` is multiplication by `φ`. -/
theorem embed_mulPhi (v : Cyc) : embed (mulPhi v) = φ * embed v := by
  simp only [mulPhi, embed_add, embed_mulZeta, embed_mulZetaInv]
  linear_combination (embed v) * zeta_add_zeta_pow_four

/-- If `v v̄ = y` has the shape `y₀ + y₂ (ζ² + ζ³)` of an element of `ℤ[φ]`, then
`|v|² = y₀ - y₂ φ`. -/
theorem norm_embed_sq {v : Cyc} (h1 : (mul v (conj v)).c1 = 0)
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

/-- The exact test that `v` lies in the closed disk of radius `√(α + β φ)` about `c`. -/
def memCheckAt (α β : ℤ) (c v : Cyc) : Bool :=
  let y := mul (v - c) (conj (v - c))
  decide (y.c1 = 0) && decide (y.c3 = y.c2) && nonnegCheck (α - y.c0) (β + y.c2)

/-- The disk test `TDCSG.Five.Cyc.memCheckAt α β` is sound at every radius `r ≥ √(α + β φ)`. -/
theorem mem_closedBall_of_memCheckAt {α β : ℤ} {c v : Cyc} (h : memCheckAt α β c v = true)
    {r : ℝ} (hr : √(α + β * φ) ≤ r) : embed v ∈ closedBall (embed c) r := by
  simp only [memCheckAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h3⟩, hn⟩ := h
  have hsq := norm_embed_sq h1 h3
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

/-- The model centre of a letter is the centre of its disk. -/
theorem embed_center (l : Letter) : embed (center l) = l.center := by
  cases l <;> simp [center, left, right, embed, Letter.center, leftCenter, rightCenter]

/-! ### Models of the generators -/

/-- An integer model of the generators of `GG n n r r` acting on `ℤ[ζ]`: `rot` and `rotInv` are
the multiplications by the rotation factors `exp (∓2πi / n)` (`TDCSG.Five.Cyc.Model.IsSound`),
and the disk tests are made at the radius `√(α + β φ)`. -/
structure Model where
  /-- The rational part of the squared radius of the disk tests. -/
  α : ℤ
  /-- The coefficient of `φ` in the squared radius of the disk tests. -/
  β : ℤ
  /-- Multiplication by `exp (-2πi / n)`, the rotation factor of `a` and `b`. -/
  rot : Cyc → Cyc
  /-- Multiplication by `exp (2πi / n)`, the rotation factor of `a⁻¹` and `b⁻¹`. -/
  rotInv : Cyc → Cyc

namespace Model

/-- The rotations of a model are the multiplications by the rotation factors of order `n`. -/
structure IsSound (M : Model) (n : ℕ) : Prop where
  /-- `rot` is multiplication by `exp (-2πi / n)`. -/
  embed_rot (v : Cyc) : embed (M.rot v) = exp (-(2 * π * I / n)) * embed v
  /-- `rotInv` is multiplication by `exp (2πi / n)`. -/
  embed_rotInv (v : Cyc) : embed (M.rotInv v) = exp (2 * π * I / n) * embed v

variable (M : Model)

/-- The global rotation of a letter, in the model. -/
def step : Letter → Cyc → Cyc
  | .a, v => left + M.rot (v - left)
  | .aInv, v => left + M.rotInv (v - left)
  | .b, v => right + M.rot (v - right)
  | .bInv, v => right + M.rotInv (v - right)

/-- The exact test that a word is valid on the segment from `P` to `Q` at every radius
`r ≥ √(α + β φ)`. -/
def valid : List Letter → Cyc → Cyc → Bool
  | [], _, _ => true
  | l :: w, P, Q => memCheckAt M.α M.β (center l) P && memCheckAt M.α M.β (center l) Q &&
      valid w (M.step l P) (M.step l Q)

/-- The composite global rotation of a word, in the model. -/
def run : List Letter → Cyc → Cyc
  | [], v => v
  | l :: w, v => run w (M.step l v)

/-- The exact check that `w` is valid on the segment from `P` to `Q` and maps `P` to `P'` and
`Q` to `Q'`. -/
def wordCheck (w : List Letter) (P Q P' Q' : Cyc) : Bool :=
  M.valid w P Q && decide (M.run w P = P') && decide (M.run w Q = Q')

namespace IsSound

variable {M} {n : ℕ} (hM : M.IsSound n)
include hM

/-- The model step of a letter is its global rotation. -/
theorem embed_step (l : Letter) (v : Cyc) : embed (M.step l v) = l.glob n (embed v) := by
  have hl := embed_center .a
  have hr := embed_center .b
  simp only [center] at hl hr
  cases l <;>
    simp [step, Letter.glob, Letter.factor, Letter.center, embed_add, embed_sub, hM.embed_rot,
      hM.embed_rotInv, hl, hr]

/-- The model run of a word is the composite of the global rotations of its letters. -/
theorem embed_run (w : List Letter) (v : Cyc) : embed (M.run w v) = globalWord n w (embed v) := by
  induction w generalizing v with
  | nil => rfl
  | cons l w ih => rw [run, ih, globalWord, hM.embed_step]

/-- The validity test `TDCSG.Five.Cyc.Model.valid` is sound at every radius `r ≥ √(α + β φ)`. -/
theorem wordValid_of_valid {w : List Letter} {P Q : Cyc} (h : M.valid w P Q = true) {r : ℝ}
    (hr : √(M.α + M.β * φ) ≤ r) : WordValid n r w (embed P) (embed Q) := by
  induction w generalizing P Q with
  | nil => trivial
  | cons l w ih =>
    simp only [valid, Bool.and_eq_true] at h
    obtain ⟨⟨hP, hQ⟩, hw⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · rw [← embed_center]
      exact mem_closedBall_of_memCheckAt hP hr
    · rw [← embed_center]
      exact mem_closedBall_of_memCheckAt hQ hr
    · rw [← hM.embed_step, ← hM.embed_step]
      exact ih hw

end IsSound

end Model

/-- The model of the generators of `GG 5 5 r r`, with disk tests at radius `√(3 + φ)`. -/
def pentagon : Model := ⟨3, 1, mulZetaInv, mulZeta⟩

/-- The rotations of `TDCSG.Five.Cyc.pentagon` are those of the generators of `GG 5 5 r r`. -/
theorem pentagon_isSound : pentagon.IsSound 5 where
  embed_rot v := by
    rw [show pentagon.rot v = mulZetaInv v from rfl, embed_mulZetaInv, Nat.cast_ofNat,
      exp_rotationAngle_five]
  embed_rotInv v := by
    rw [show pentagon.rotInv v = mulZeta v from rfl, embed_mulZeta, Nat.cast_ofNat,
      exp_two_pi_I_div_five]

/-! ### Words acting along a line -/

/-- The lattice point `(p + q φ) V` of the line through `0` in the direction `V`. -/
def linePt (V : Cyc) (p q : ℤ) : Cyc := p • V + q • mulPhi V

/-- The lattice point `TDCSG.Five.Cyc.linePt V p q` is `(p + q φ) V`. -/
theorem embed_linePt (V : Cyc) (p q : ℤ) :
    embed (linePt V p q) = ((p + q * φ : ℝ) : ℂ) * embed V := by
  simp only [linePt, embed_add, embed_smul, embed_mulPhi]
  push_cast
  ring

/-- A word checked on a segment of a line through `0` translates every point of the segment
along the line. -/
theorem Model.IsSound.applyWord_linePt {M : Model} {n : ℕ} (hM : M.IsSound n) {r : ℝ}
    (hr : √(M.α + M.β * φ) ≤ r) {w : List Letter} {V : Cyc} {p₀ q₀ p₁ q₁ dp dq : ℤ}
    (hcheck : M.wordCheck w (linePt V p₀ q₀) (linePt V p₁ q₁) (linePt V (p₀ + dp) (q₀ + dq))
      (linePt V (p₁ + dp) (q₁ + dq)) = true)
    (hlt : (p₀ + q₀ * φ : ℝ) < p₁ + q₁ * φ) {t : ℝ}
    (ht : t ∈ Set.Icc (p₀ + q₀ * φ : ℝ) (p₁ + q₁ * φ)) :
    applyWord n r w (t * embed V) = ((t + (dp + dq * φ) : ℝ) : ℂ) * embed V := by
  simp only [Model.wordCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hv, h₀⟩, h₁⟩ := hcheck
  have hv' := hM.wordValid_of_valid hv hr
  rw [embed_linePt, embed_linePt] at hv'
  refine applyWord_line hlt hv' ?_ ?_ ht
  · rw [← embed_linePt, ← hM.embed_run, h₀, embed_linePt]
    push_cast
    ring_nf
  · rw [← embed_linePt, ← hM.embed_run, h₁, embed_linePt]
    push_cast
    ring_nf

end Cyc

end TDCSG.Five

end
