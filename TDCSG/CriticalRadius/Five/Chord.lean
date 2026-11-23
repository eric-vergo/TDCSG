/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.Five.Cyclotomic

/-!
# The critical chord: `GG₅(r)` is infinite for every `r ≥ √(3 + φ)`

This is Theorem 2 of arXiv:2302.12950, extended to all larger radii, and Part A of
`notes/proofs/critical-radius-n5.md`. Let `ζ = exp (2πi / 5)` and `φ` the golden ratio. On the
chord from `E' = -E` to `E = ζ - ζ²`, parametrized as `t ↦ t E` for `t ∈ [-1, 1]`, three explicit
words in the generators act as translations, and together they realize the rotation
`t ↦ t + 2/φ` of the circle `ℝ / 2ℤ`. Since `φ` is irrational, the orbit of `0` contains
infinitely many distinct points `t_k E`.

## Main definitions

* `TDCSG.Five.pointE`: the end point `E = ζ - ζ²` of the critical chord.
* `TDCSG.Five.chordPt`: the lattice point `(p + q φ) E` of the chord.
* `TDCSG.Five.word₁`, `TDCSG.Five.word₂`, `TDCSG.Five.word₃`: the three words of §3.2 of the
  written proof.

## Main statements

* `TDCSG.Five.norm_embed_pointE_add_one_sq`: `|E + 1|² = 3 + φ`, so `E` lies on the boundary
  circle of the left disk at the critical radius.
* `TDCSG.Five.applyWord_word₁`, `TDCSG.Five.applyWord_word₂`, `TDCSG.Five.applyWord_word₃`: the
  three words translate their segments of the chord.
* `TDCSG.Five.infinite_orbit_zero`: for `r ≥ √(3 + φ)` the orbit of `0` is infinite.
* `TDCSG.Five.infinite_GG`: for `r ≥ √(3 + φ)` the group `GG 5 5 r r` is infinite.

## Implementation notes

Every disk test and every endpoint image of the three words is computed in the integer model
`TDCSG.Five.Cyc` and checked by `decide`.
-/

@[expose] public section

open Complex Metric Equiv
open scoped Real goldenRatio

namespace TDCSG.Five

@[inherit_doc] local notation "ζ" => zeta

/-! ### The critical chord and the three words -/

open Cyc

/-- The end point `E = ζ - ζ²` of the critical chord. -/
def pointE : Cyc := ⟨0, 1, -1, 0⟩

/-- `|E + 1|² = 3 + φ`: at radius `√(3 + φ)` the point `E` lies on the boundary circle of the
left disk. -/
theorem norm_embed_pointE_add_one_sq : ‖embed pointE + 1‖ ^ 2 = 3 + φ := by
  have h := norm_embed_sq (v := pointE - left) (by decide) (by decide)
  rw [embed_sub, show embed left = -1 by simp [embed, left]] at h
  rw [show embed pointE + 1 = embed pointE - -1 by ring, h]
  have : (mul (pointE - left) (conj (pointE - left))) = ⟨3, 0, -1, -1⟩ := by decide
  rw [this]
  push_cast
  ring

/-- The end point `E` of the critical chord is not `0`. -/
theorem embed_pointE_ne_zero : embed pointE ≠ 0 := by
  have h : embed pointE = ζ * (1 - ζ) := by
    simp [embed, pointE]
    ring
  rw [h]
  exact mul_ne_zero (isPrimitiveRoot_zeta.ne_zero (by norm_num))
    (sub_ne_zero.2 (isPrimitiveRoot_zeta.ne_one (by norm_num)).symm)

/-- The lattice point `(p + q φ) E` of the critical chord. -/
def chordPt (p q : ℤ) : Cyc := linePt pointE p q

/-- The lattice point `TDCSG.Five.chordPt p q` is `(p + q φ) E`. -/
theorem embed_chordPt (p q : ℤ) : embed (chordPt p q) = ((p + q * φ : ℝ) : ℂ) * embed pointE :=
  embed_linePt pointE p q

/-- A word checked on a segment of the chord translates every point of the segment along the
chord. -/
theorem applyWord_chord {r : ℝ} (hr : √(3 + φ) ≤ r) {w : List Letter}
    {p₀ q₀ p₁ q₁ dp dq : ℤ}
    (hcheck : pentagon.wordCheck w (chordPt p₀ q₀) (chordPt p₁ q₁) (chordPt (p₀ + dp) (q₀ + dq))
      (chordPt (p₁ + dp) (q₁ + dq)) = true)
    (hlt : (p₀ + q₀ * φ : ℝ) < p₁ + q₁ * φ) {t : ℝ}
    (ht : t ∈ Set.Icc (p₀ + q₀ * φ : ℝ) (p₁ + q₁ * φ)) :
    applyWord 5 r w (t * embed pointE) = ((t + (dp + dq * φ) : ℝ) : ℂ) * embed pointE :=
  pentagon_isSound.applyWord_linePt (by simpa [pentagon] using hr) hcheck hlt ht

/-- The word `a⁻¹ a⁻¹ b⁻¹ a⁻¹ b⁻¹`, mapping `[E', F']` onto `[G, F]`. -/
def word₁ : List Letter := [.aInv, .aInv, .bInv, .aInv, .bInv]

/-- The word `a b a b b`, mapping `[F', G']` onto `[F, E]`. -/
def word₂ : List Letter := [.a, .b, .a, .b, .b]

/-- The word `a b a b⁻¹ a⁻¹ b⁻¹`, mapping `[G', E]` onto `[E', G]`. -/
def word₃ : List Letter := [.a, .b, .a, .bInv, .aInv, .bInv]

/-- On `[-1, 1 - φ]`, that is on `[E', F']`, the word `word₁` translates by `2φ - 2 = 2/φ`. -/
theorem applyWord_word₁ {r : ℝ} (hr : √(3 + φ) ≤ r) {t : ℝ} (ht : t ∈ Set.Icc (-1) (1 - φ)) :
    applyWord 5 r word₁ (t * embed pointE) = ((t + (2 * φ - 2) : ℝ) : ℂ) * embed pointE := by
  have := applyWord_chord (p₀ := -1) (q₀ := 0) (p₁ := 1) (q₁ := -1) (dp := -2) (dq := 2)
    (w := word₁) hr (by decide) (by push_cast; linarith [Real.goldenRatio_lt_two]) (t := t)
    (by push_cast; constructor <;> linarith [ht.1, ht.2])
  rw [this]
  push_cast
  ring

/-- On `[1 - φ, 3 - 2φ]`, that is on `[F', G']`, the word `word₂` translates by `2φ - 2`. -/
theorem applyWord_word₂ {r : ℝ} (hr : √(3 + φ) ≤ r) {t : ℝ}
    (ht : t ∈ Set.Icc (1 - φ) (3 - 2 * φ)) :
    applyWord 5 r word₂ (t * embed pointE) = ((t + (2 * φ - 2) : ℝ) : ℂ) * embed pointE := by
  have := applyWord_chord (p₀ := 1) (q₀ := -1) (p₁ := 3) (q₁ := -2) (dp := -2) (dq := 2)
    (w := word₂) hr (by decide) (by push_cast; linarith [Real.goldenRatio_lt_two]) (t := t)
    (by push_cast; constructor <;> linarith [ht.1, ht.2])
  rw [this]
  push_cast
  ring

/-- On `[3 - 2φ, 1]`, that is on `[G', E]`, the word `word₃` translates by `2φ - 4 = -2/φ²`. -/
theorem applyWord_word₃ {r : ℝ} (hr : √(3 + φ) ≤ r) {t : ℝ} (ht : t ∈ Set.Icc (3 - 2 * φ) 1) :
    applyWord 5 r word₃ (t * embed pointE) = ((t + (2 * φ - 4) : ℝ) : ℂ) * embed pointE := by
  have := applyWord_chord (p₀ := 3) (q₀ := -2) (p₁ := 1) (q₁ := 0) (dp := -4) (dq := 2)
    (w := word₃) hr (by decide) (by push_cast; linarith [Real.one_lt_goldenRatio]) (t := t)
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
    have h1 := Real.one_lt_goldenRatio
    have h2 := Real.goldenRatio_lt_two
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

end TDCSG.Five

end
