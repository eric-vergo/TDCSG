/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import TDCSG.CriticalRadius.Five

/-!
# `GG₁₀(r)` is infinite for every `r ≥ √(4 - φ)`

This is Part A (Theorem A) of `notes/proofs/critical-radius-n10.md`. Let `ζ = exp (2πi / 5)`, so
that `exp (2πi / 10) = -ζ³` and `ℤ[exp (2πi / 10)] = ℤ[ζ]`, and let `u = ζ² = exp (4πi / 5)`. On
the chord `J = {s u : |s| ≤ √5}` three explicit words in the generators act as translations:
`b b a⁻¹ b⁻¹` on `s ∈ [-√5, -φ⁻¹]` and `a b a⁻¹ a⁻¹` on `s ∈ [-φ⁻¹, 1]` by `2φ⁻¹ = 2φ - 2`, and
`a a a b⁻¹ b⁻¹ b⁻¹` on `s ∈ [1, √5]` by `-2φ`. Together they realize the rotation
`s ↦ s + 2φ⁻¹` of the circle `ℝ / 2√5 ℤ`, whose rotation number `1 / (φ + 2)` is irrational, so
the orbit of `0` contains infinitely many distinct points `s_k u`.

## Main definitions

* `TDCSG.Ten.model`: the integer model of the generators of `GG 10 10 r r` on `ℤ[ζ]`, with disk
  tests at radius `√(4 - φ)`.
* `TDCSG.Ten.dirU`: the direction `u = ζ²` of the critical chord.
* `TDCSG.Ten.pointW`: the end point `W = √5 u` of the critical chord.
* `TDCSG.Ten.word₁`, `TDCSG.Ten.word₂`, `TDCSG.Ten.word₃`: the three words of §3.2 of the
  written proof.

## Main statements

* `TDCSG.Ten.normSq_pointW_add_one`: `|W + 1|² = 4 - φ`, so `W` lies on the boundary circle of
  the left disk at the critical radius.
* `TDCSG.Ten.infinite_orbit_zero`: for `r ≥ √(4 - φ)` the orbit of `0` is infinite.
* `TDCSG.Ten.infinite_GG`: for `r ≥ √(4 - φ)` the group `GG 10 10 r r` is infinite.
* `TDCSG.Ten.criticalRadius_le`, `TDCSG.Ten.one_le_criticalRadius`:
  `1 ≤ criticalRadius 10 ≤ √(4 - φ)`.

## Implementation notes

The integer model `TDCSG.Five.Cyc` of `ℤ[ζ]` and its exact disk tests are shared with the case
`n = 5`; only the rotations change: the generators rotate by `exp (-2πi / 10) = -ζ²`. Every disk
test and every endpoint image of the three words is checked by `decide`.
-/

@[expose] public section

open Complex Metric
open scoped Real goldenRatio

namespace TDCSG.Ten

open Five Five.Cyc

local notation "ζ" => Five.zeta

/-! ### The tenth root of unity in `ℤ[ζ]` -/

/-- The rotation factor `exp (-2πi / 10)` of the generators is `-ζ²`. -/
theorem exp_rotationAngle_ten : exp (-(2 * π * I / 10)) = -ζ ^ 2 := by
  rw [show -(2 * π * I / 10) = ((2 : ℕ) : ℂ) * (2 * π * I / 5) - π * I by push_cast; ring,
    exp_sub, exp_nat_mul, exp_pi_mul_I, exp_two_pi_I_div_five, div_neg, div_one]

/-- `exp (2πi / 10) = -ζ³`. -/
theorem exp_two_pi_I_div_ten : exp (2 * π * I / 10) = -ζ ^ 3 := by
  rw [show 2 * π * I / 10 = ((3 : ℕ) : ℂ) * (2 * π * I / 5) - π * I by push_cast; ring,
    exp_sub, exp_nat_mul, exp_pi_mul_I, exp_two_pi_I_div_five, div_neg, div_one]

/-- Multiplication by `exp (-2πi / 10) = -ζ²`. -/
def rot (v : Cyc) : Cyc := (-1 : ℤ) • mulZeta (mulZeta v)

/-- Multiplication by `exp (2πi / 10) = -ζ³ = -ζ⁸`. -/
def rotInv (v : Cyc) : Cyc := (-1 : ℤ) • mulZetaInv (mulZetaInv v)

/-- The model of the generators of `GG 10 10 r r`, with disk tests at radius `√(4 - φ)`. -/
def model : Model := ⟨4, -1, rot, rotInv⟩

theorem model_isSound : model.IsSound 10 where
  embed_rot v := by
    rw [show model.rot v = rot v from rfl, rot, embed_smul, embed_mulZeta, embed_mulZeta,
      Nat.cast_ofNat, exp_rotationAngle_ten]
    push_cast
    ring
  embed_rotInv v := by
    rw [show model.rotInv v = rotInv v from rfl, rotInv, embed_smul, embed_mulZetaInv,
      embed_mulZetaInv, Nat.cast_ofNat, exp_two_pi_I_div_ten]
    push_cast
    linear_combination (-ζ ^ 3 * embed v) * zeta_pow_five

theorem sqrt_model_le {r : ℝ} (hr : √(4 - φ) ≤ r) : √(model.α + model.β * φ) ≤ r := by
  convert hr using 2
  simp only [model, Int.cast_ofNat, Int.reduceNeg, Int.cast_neg, Int.cast_one]
  ring

/-! ### The critical chord -/

/-- The direction `u = ζ² = exp (4πi / 5)` of the critical chord. -/
def dirU : Cyc := ⟨0, 0, 1, 0⟩

theorem embed_dirU : embed dirU = ζ ^ 2 := by
  simp [embed, dirU]

theorem embed_dirU_ne_zero : embed dirU ≠ 0 := by
  rw [embed_dirU]
  exact pow_ne_zero 2 (isPrimitiveRoot_zeta.ne_zero (by norm_num))

/-- The end point `W = √5 u` of the critical chord. -/
def pointW : Cyc := ⟨0, 2, 1, 2⟩

theorem embed_pointW : embed pointW = ((√5 : ℝ) : ℂ) * embed dirU := by
  rw [show pointW = linePt dirU (-1) 2 by decide, embed_linePt]
  congr 2
  rw [Real.goldenRatio]
  push_cast
  ring

/-- `|W + 1|² = 4 - φ`: at radius `√(4 - φ)` the point `W` lies on the boundary circle of the
left disk. -/
theorem normSq_pointW_add_one : ‖embed pointW + 1‖ ^ 2 = 4 - φ := by
  have h := norm_sq_embed (v := pointW - left) (by decide) (by decide)
  rw [embed_sub, show embed left = -1 by simp [embed, left]] at h
  rw [show embed pointW + 1 = embed pointW - -1 by ring, h]
  have : (mul (pointW - left) (conj (pointW - left))) = ⟨4, 0, 1, 1⟩ := by decide
  rw [this]
  push_cast
  ring

/-! ### The three words -/

/-- The word `b b a⁻¹ b⁻¹`, mapping `[-√5, -φ⁻¹] u` onto `[-1, φ⁻¹] u`. -/
def word₁ : List Letter := [.b, .b, .aInv, .bInv]

/-- The word `a b a⁻¹ a⁻¹`, mapping `[-φ⁻¹, 1] u` onto `[φ⁻¹, √5] u`. -/
def word₂ : List Letter := [.a, .b, .aInv, .aInv]

/-- The word `a a a b⁻¹ b⁻¹ b⁻¹`, mapping `[1, √5] u` onto `[-√5, -1] u`. -/
def word₃ : List Letter := [.a, .a, .a, .bInv, .bInv, .bInv]

/-- On `[1 - 2φ, 1 - φ] = [-√5, -φ⁻¹]` the word `word₁` translates by `2φ - 2 = 2φ⁻¹`. -/
theorem applyWord_word₁ {r : ℝ} (hr : √(4 - φ) ≤ r) {s : ℝ}
    (hs : s ∈ Set.Icc (1 - 2 * φ) (1 - φ)) :
    applyWord 10 r word₁ (s * embed dirU) = ((s + (2 * φ - 2) : ℝ) : ℂ) * embed dirU := by
  have := model_isSound.applyWord_linePt (p₀ := 1) (q₀ := -2) (p₁ := 1) (q₁ := -1) (dp := -2)
    (dq := 2) (V := dirU) (w := word₁) (sqrt_model_le hr) (by decide)
    (by push_cast; linarith [one_lt_phi]) (t := s)
    (by push_cast; constructor <;> linarith [hs.1, hs.2])
  rw [this]
  push_cast
  ring

/-- On `[1 - φ, 1] = [-φ⁻¹, 1]` the word `word₂` translates by `2φ - 2 = 2φ⁻¹`. -/
theorem applyWord_word₂ {r : ℝ} (hr : √(4 - φ) ≤ r) {s : ℝ} (hs : s ∈ Set.Icc (1 - φ) 1) :
    applyWord 10 r word₂ (s * embed dirU) = ((s + (2 * φ - 2) : ℝ) : ℂ) * embed dirU := by
  have := model_isSound.applyWord_linePt (p₀ := 1) (q₀ := -1) (p₁ := 1) (q₁ := 0) (dp := -2)
    (dq := 2) (V := dirU) (w := word₂) (sqrt_model_le hr) (by decide)
    (by push_cast; linarith [one_lt_phi]) (t := s)
    (by push_cast; constructor <;> linarith [hs.1, hs.2])
  rw [this]
  push_cast
  ring

/-- On `[1, 2φ - 1] = [1, √5]` the word `word₃` translates by `-2φ`. -/
theorem applyWord_word₃ {r : ℝ} (hr : √(4 - φ) ≤ r) {s : ℝ} (hs : s ∈ Set.Icc 1 (2 * φ - 1)) :
    applyWord 10 r word₃ (s * embed dirU) = ((s + -2 * φ : ℝ) : ℂ) * embed dirU := by
  have := model_isSound.applyWord_linePt (p₀ := 1) (q₀ := 0) (p₁ := -1) (q₁ := 2) (dp := 0)
    (dq := -2) (V := dirU) (w := word₃) (sqrt_model_le hr) (by decide)
    (by push_cast; linarith [one_lt_phi]) (t := s)
    (by push_cast; constructor <;> linarith [hs.1, hs.2])
  rw [this]
  push_cast
  ring

/-! ### The infinite orbit -/

/-- The orbit of `0` contains the points `s_k u`, with `s_k ∈ [1 - 2φ, 2φ - 1) = [-√5, √5)` and
`s_k ≡ k (2φ - 2) mod 2√5`, where `2√5 = 4φ - 2`. -/
theorem exists_mem_orbit {r : ℝ} (hr : √(4 - φ) ≤ r) (k : ℕ) :
    ∃ s : ℝ, ∃ m : ℤ, s ∈ Set.Ico (1 - 2 * φ) (2 * φ - 1) ∧
      s = k * (2 * φ - 2) + m * (4 * φ - 2) ∧ (s : ℂ) * embed dirU ∈ orbit 10 10 r r 0 := by
  induction k with
  | zero =>
    refine ⟨0, 0, ⟨by linarith [one_lt_phi], by linarith [one_lt_phi]⟩, by simp, ?_⟩
    simp [mem_orbit_self]
  | succ k ih =>
    obtain ⟨s, m, ⟨hs₀, hs₁⟩, hsm, hmem⟩ := ih
    have h1 := one_lt_phi
    rcases le_or_gt s (1 - φ) with h | h
    · refine ⟨s + (2 * φ - 2), m, ⟨by linarith, by linarith⟩, by rw [hsm]; push_cast; ring, ?_⟩
      rw [← applyWord_word₁ hr ⟨hs₀, h⟩]
      exact applyWord_mem_orbit _ hmem
    rcases lt_or_ge s 1 with h' | h'
    · refine ⟨s + (2 * φ - 2), m, ⟨by linarith, by linarith⟩, by rw [hsm]; push_cast; ring, ?_⟩
      rw [← applyWord_word₂ hr ⟨h.le, h'.le⟩]
      exact applyWord_mem_orbit _ hmem
    · refine ⟨s + -2 * φ, m - 1, ⟨by linarith, by linarith⟩, by rw [hsm]; push_cast; ring, ?_⟩
      rw [← applyWord_word₃ hr ⟨h', hs₁.le⟩]
      exact applyWord_mem_orbit _ hmem

/-- **Theorem A**, orbit form: for every `r ≥ √(4 - φ)` the orbit of `0` under `GG 10 10 r r`
is infinite. -/
theorem infinite_orbit_zero {r : ℝ} (hr : √(4 - φ) ≤ r) : (orbit 10 10 r r 0).Infinite := by
  choose s m hs hsm hmem using exists_mem_orbit hr
  refine Set.infinite_of_injective_forall_mem (f := fun k ↦ (s k : ℂ) * embed dirU)
    (fun k l hkl ↦ ?_) hmem
  have hkl' : s k = s l := by
    have := mul_right_cancel₀ embed_dirU_ne_zero hkl
    exact_mod_cast this
  rw [hsm k, hsm l] at hkl'
  obtain ⟨ha, hb⟩ := eq_zero_of_add_mul_phi_eq_zero
    (a := -2 * ((k : ℤ) - l) - 2 * (m k - m l)) (b := 2 * ((k : ℤ) - l) + 4 * (m k - m l))
    (by push_cast; linear_combination hkl')
  have : (k : ℤ) = l := by omega
  exact_mod_cast this

/-- **Theorem A**: for every `r ≥ √(4 - φ)` the group `GG 10 10 r r` is infinite. -/
theorem infinite_GG {r : ℝ} (hr : √(4 - φ) ≤ r) : Infinite (GG 10 10 r r) :=
  infinite_GG_of_infinite_orbit (infinite_orbit_zero hr)

/-- The critical radius of `GG₁₀` is at most `√(4 - φ)`. -/
theorem criticalRadius_le : criticalRadius 10 ≤ √(4 - φ) :=
  TDCSG.criticalRadius_le (infinite_GG le_rfl)

/-- The critical radius of `GG₁₀` is at least `1`. -/
theorem one_le_criticalRadius : 1 ≤ criticalRadius 10 :=
  TDCSG.one_le_criticalRadius ⟨_, infinite_GG le_rfl⟩

end TDCSG.Ten

end
