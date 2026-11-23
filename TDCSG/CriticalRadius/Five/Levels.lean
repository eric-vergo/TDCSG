/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
module

public import TDCSG.CriticalRadius.Five.Labels
public import TDCSG.CriticalRadius.Five.Lens
public import TDCSG.ForMathlib.Recurrence

/-!
# Good levels: crossing edges end in leaves, and good levels recur

This is §3 of `notes/proofs/sharp-lower-bound-n5-pentagrid.md`. Fix a coordinate `j` and a
window centre `x`, and write `L = φ - 1 / 2` and `η = (3 + φ - r²) / 16`. After turning by
`ζ⁻ʲ`, the midpoint of an edge from a sum-zero label `n` with `n_j = m` to `n + e_j` has real part
`(1 + φ / 2) m + 1 / 2 - Re (x ζ⁻ʲ)` relative to `x`, up to a multiple of `L`. A level `m` is good
if this quantity stays farther than `L / 2 - η` from `L ℤ`. By the lens estimate, every edge of
the centre graph that crosses a good level has an endpoint of degree one. The levels form an
irrational rotation by `(1 + φ / 2) / L = φ`, so good levels recur with bounded gaps, uniformly
in `x` and `j`.

## Main definitions

* `TDCSG.Five.IsGoodLevel r x j m`: `m` is a good level for coordinate `j` at window centre `x`.

## Main statements

* `TDCSG.Five.re_proj_mul_conj_dir`: the real part of `P(n) ζ⁻ʲ` for a sum-zero label `n`.
* `TDCSG.Five.IsGoodLevel.leaf`: at a good level, one end of every crossing edge in the window
  has no other neighbour in the window (Lemma 3 of the written proof).
* `TDCSG.Five.exists_isGoodLevel`: good levels recur with gaps bounded uniformly in `x` and `j`
  (Lemma 4 of the written proof, without the rate).
-/

@[expose] public section

open Complex
open scoped goldenRatio

namespace TDCSG.Five

open Label

/-! ### Real parts of projections -/

/-- The four directions other than `1` have real part `(φ - 1) / 2` or `-φ / 2`. -/
theorem re_dir_of_ne_zero {k : Fin 5} (hk : k ≠ 0) :
    (dir k).re = (φ - 1) / 2 ∨ (dir k).re = -φ / 2 := by
  fin_cases k
  · exact (hk rfl).elim
  · exact .inl (by simpa [dir] using re_zeta)
  · exact .inr re_zeta_sq
  · exact .inr re_zeta_pow_three
  · exact .inl re_zeta_pow_four

/-- Turning a projection by `ζ⁻ʲ` shifts the coordinates of the label by `j`. -/
theorem proj_mul_conj_dir (n : Label) (j : Fin 5) :
    proj n * (starRingEnd ℂ) (dir j) = proj (fun k ↦ n (k + j)) := by
  simp only [proj_apply, Finset.sum_mul, mul_assoc, dir_mul_conj_dir]
  exact Fintype.sum_equiv (Equiv.subRight j) _ _ fun k ↦ by simp

/-- Shifting the coordinates of a label does not change its coordinate sum. -/
theorem weight_shift (n : Label) (j : Fin 5) : weight (fun k ↦ n (k + j)) = weight n :=
  Equiv.sum_comp (Equiv.addRight j) n

/-- For a sum-zero label `m`, `Re P(m) = (1 + φ / 2) m₀ + (φ - 1 / 2) (m₁ + m₄)`. -/
theorem re_proj (m : Label) (hm : weight m = 0) :
    (proj m).re = (1 + φ / 2) * m 0 + (φ - 1 / 2) * (m 1 + m 4) := by
  have hm' : (m 0 : ℝ) + m 1 + m 2 + m 3 + m 4 = 0 := by
    rw [weight_apply, Fin.sum_univ_five] at hm
    exact_mod_cast hm
  have h1 : (dir 1).re = (φ - 1) / 2 := by simpa [dir] using re_zeta
  rw [proj_apply, re_sum, Fin.sum_univ_five]
  simp only [mul_re, intCast_re, intCast_im, zero_mul, sub_zero, dir_zero, one_re, h1]
  rw [show (dir 2).re = -φ / 2 from re_zeta_sq, show (dir 3).re = -φ / 2 from re_zeta_pow_three,
    show (dir 4).re = (φ - 1) / 2 from re_zeta_pow_four]
  linear_combination (-φ / 2) * hm'

/-- For a sum-zero label `n`, the real part of `P(n) ζ⁻ʲ` is
`(1 + φ / 2) n_j + (φ - 1 / 2) (n_{j+1} + n_{j-1})`. -/
theorem re_proj_mul_conj_dir (n : Label) (hn : weight n = 0) (j : Fin 5) :
    (proj n * (starRingEnd ℂ) (dir j)).re =
      (1 + φ / 2) * n j + (φ - 1 / 2) * (n (j + 1) + n (j - 1)) := by
  rw [proj_mul_conj_dir, re_proj _ ((weight_shift n j).trans hn), zero_add, add_comm 1 j,
    show (4 : Fin 5) + j = j - 1 by rw [show (4 : Fin 5) = -1 from rfl, neg_add_eq_sub]]

/-! ### Good levels -/

/-- The level `m` of coordinate `j` is good at radius `r` and window centre `x` if
`(1 + φ / 2) m + 1 / 2 - Re (x ζ⁻ʲ)` is farther than `L / 2 - η` from every point of `L ℤ`, where
`L = φ - 1 / 2` and `η = (3 + φ - r²) / 16`. -/
def IsGoodLevel (r : ℝ) (x : ℂ) (j : Fin 5) (m : ℤ) : Prop :=
  ∀ p : ℤ, (φ - 1 / 2) / 2 - (3 + φ - r ^ 2) / 16 <
    |(1 + φ / 2) * m + (1 / 2 - (x * (starRingEnd ℂ) (dir j)).re) + (φ - 1 / 2) * p|

variable {r : ℝ} {x : ℂ}

/-- **Crossings end in leaves.** Let `n` be a sum-zero label at a good level `m = n_j`, with
`n` and `n + e_j` in the window. Then either `n + e_j` is the only neighbour of `n` in the
window, or `n` is the only neighbour of `n + e_j`. -/
theorem IsGoodLevel.leaf (hr : 0 ≤ r) (hc : r < √(3 + φ)) {j : Fin 5} {m : ℤ}
    (hm : IsGoodLevel r x j m) {n : Label} (hw : weight n = 0) (hnj : n j = m)
    (hlo : InWindow r x n) (hhi : InWindow r x (n + basis j)) :
    (∀ k ≠ j, ¬InWindow r x (n + basis k)) ∨
      (∀ k ≠ j, ¬InWindow r x (n + basis j - basis k)) := by
  have hnorm (w : ℂ) : ‖w * (starRingEnd ℂ) (dir j)‖ = ‖w‖ := by simp
  set q := (proj n - x) * (starRingEnd ℂ) (dir j) with hq_def
  have hmid := hm (n (j + 1) + n (j - 1))
  have hform : (1 + φ / 2) * (m : ℝ) + (1 / 2 - (x * (starRingEnd ℂ) (dir j)).re) +
      (φ - 1 / 2) * (((n (j + 1) + n (j - 1) : ℤ) : ℝ)) = q.re + 1 / 2 := by
    rw [hq_def, sub_mul (proj n), sub_re, re_proj_mul_conj_dir n hw, hnj]
    push_cast
    ring
  rw [hform, lt_abs] at hmid
  have hrot : (proj (n + basis j) - x) * (starRingEnd ℂ) (dir j) = q + 1 := by
    rw [map_add, proj_basis, add_sub_right_comm, add_mul, dir_mul_conj_dir, sub_self, dir_zero]
  have hq : ‖q‖ ≤ r / 2 := by rw [hq_def, hnorm]; exact hlo
  have hk {k : Fin 5} (hk : k ≠ j) := re_dir_of_ne_zero (sub_ne_zero.2 hk)
  rcases hmid with h | h
  · right
    have hqr : ‖q + 1‖ ≤ r / 2 := by rw [← hrot, hnorm]; exact hhi
    intro k hkj hwin
    refine (div_two_lt_norm_sub_of_le_re hr hc (norm_dir (k - j)) (hk hkj) hqr ?_).not_ge ?_
    · rw [add_re, one_re]
      linarith
    · rw [InWindow, ← hnorm, map_sub, proj_basis, sub_right_comm, sub_mul, hrot,
        dir_mul_conj_dir] at hwin
      exact hwin
  · left
    intro k hkj hwin
    have hneg : ‖-q‖ ≤ r / 2 := by rwa [norm_neg]
    refine (div_two_lt_norm_sub_of_le_re hr hc (norm_dir (k - j)) (hk hkj) hneg ?_).not_ge ?_
    · rw [neg_re]
      linarith
    · rw [InWindow, ← hnorm, map_add, proj_basis, add_sub_right_comm, add_mul,
        dir_mul_conj_dir, ← hq_def] at hwin
      rwa [← neg_add', norm_neg]

/-- For an irrational rotation number `α / L` and every `η > 0` there is a bound `K` such that,
for every offset `b` and every integer `z`, some `z + i` with `|i| ≤ K` puts the phase
`α (z + i) + b` farther than `L / 2 - η` from every point of `L ℤ`. -/
theorem exists_abs_le_forall_lt_abs_add_mul {L η α : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hirr : Irrational (α / L)) :
    ∃ K : ℕ, ∀ (b : ℝ) (z : ℤ), ∃ i : ℤ, |i| ≤ K ∧
      ∀ p : ℤ, L / 2 - η < |α * (z + i) + b + L * p| := by
  obtain ⟨K, hK⟩ := hirr.exists_abs_le_lt_norm_zsmul_add hL hη
  refine ⟨K, fun b z ↦ ?_⟩
  obtain ⟨i, hiK, hi⟩ := hK ((z * α + b : ℝ) : AddCircle L)
  refine ⟨i, hiK, fun p ↦ hi.trans_le ?_⟩
  have hw : (((α * (z + i) + b + L * p : ℝ)) : AddCircle L) =
      i • (α : AddCircle L) + ((z * α + b : ℝ) : AddCircle L) := by
    rw [mul_comm L, ← zsmul_eq_mul, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, add_zero, ← AddCircle.coe_zsmul, ← AddCircle.coe_add, zsmul_eq_mul]
    congr 1
    ring
  rw [← hw]
  exact QuotientAddGroup.norm_mk_le_norm

/-- **Good levels recur.** Below the critical radius there is a bound `K` such that, for every
window centre `x`, every coordinate `j` and every integer `z`, one of the levels `z + i` with
`|i| ≤ K` is good. -/
theorem exists_isGoodLevel (hr : 0 ≤ r) (hc : r < √(3 + φ)) :
    ∃ K : ℕ, ∀ (x : ℂ) (j : Fin 5) (z : ℤ), ∃ i : ℤ, |i| ≤ K ∧ IsGoodLevel r x j (z + i) := by
  have hφ := Real.one_lt_goldenRatio
  have hL : 0 < φ - 1 / 2 := by linarith
  have hη : 0 < (3 + φ - r ^ 2) / 16 :=
    div_pos (sub_pos.2 ((Real.lt_sqrt hr).1 hc)) (by norm_num)
  have hrot : (1 + φ / 2) / (φ - 1 / 2) = φ := by
    rw [div_eq_iff hL.ne']
    linear_combination (-1 : ℝ) * Real.goldenRatio_sq
  obtain ⟨K, hK⟩ := exists_abs_le_forall_lt_abs_add_mul hL hη
    (hrot ▸ Real.goldenRatio_irrational)
  refine ⟨K, fun x j z ↦ ?_⟩
  obtain ⟨i, hi, h⟩ := hK (1 / 2 - (x * (starRingEnd ℂ) (dir j)).re) z
  exact ⟨i, hi, fun p ↦ by simpa using h p⟩

end TDCSG.Five

end
