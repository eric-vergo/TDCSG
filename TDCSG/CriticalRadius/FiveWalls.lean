/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.FiveCenterModel
public import TDCSG.CriticalRadius.FiveWallLevels

/-! # Barriers for paths of fivefold disk centers -/

@[expose] public section

open Complex
open scoped goldenRatio

namespace TDCSG.Five.Walls

private noncomputable abbrev c : ℝ := (φ - 1) / 2
private noncomputable abbrev d : ℝ := -φ / 2
private noncomputable abbrev spacing : ℝ := c - d
private noncomputable abbrev axial : ℝ := (1 + spacing) / 2

private theorem dir_re_one : zeta.re = c := by
  have h := congrArg Complex.re zeta_add_zeta_pow_four
  rw [← conj_zeta] at h
  simp only [add_re, conj_re, sub_re, ofReal_re, one_re] at h
  unfold c
  linarith

private theorem dir_re_two : (zeta ^ 2).re = d := by
  have hconj : (starRingEnd ℂ) (zeta ^ 2) = zeta ^ 3 := by
    rw [map_pow, conj_zeta, ← pow_mul, ← zeta_pow_mod 8]
  have h := congrArg Complex.re zeta_sq_add_zeta_cube
  rw [← hconj] at h
  simp only [add_re, conj_re, neg_re, ofReal_re] at h
  unfold d
  linarith

private theorem dir_re (k : Fin 5) :
    (dir k).re = if k = 0 then 1 else if k = 1 ∨ k = 4 then c else d := by
  have h4 : (zeta ^ 4).re = c := by rw [← conj_zeta]; simpa using dir_re_one
  have h3 : (zeta ^ 3).re = d := by
    have h : (starRingEnd ℂ) (zeta ^ 2) = zeta ^ 3 := by
      rw [map_pow, conj_zeta, ← pow_mul, ← zeta_pow_mod 8]
    rw [← h, conj_re]; exact dir_re_two
  fin_cases k <;> norm_num [dir, dir_re_one, dir_re_two, h3, h4]

private theorem relative_dir (j k : Fin 5) :
    dir k * (starRingEnd ℂ) (dir j) = dir (k - j) := by
  rw [dir, dir, map_pow, conj_zeta, ← pow_mul, ← pow_add, ← zeta_pow_mod]
  congr 1
  fin_cases j <;> fin_cases k <;> rfl

private theorem norm_dir (j : Fin 5) : ‖dir j‖ = 1 := by
  simp [dir, norm_zeta]

private theorem lens {r : ℝ} (hr : 0 ≤ r) (hc : r < √(3 + φ)) {v u : ℂ}
    (hu : ‖u‖ = 1) (hre : u.re = c ∨ u.re = d)
    (hv : ‖v‖ ≤ r / 2)
    (hx : axial - (3 + φ - r ^ 2) / 16 ≤ v.re) : r / 2 < ‖v - u‖ := by
  by_contra! hnear
  have hφ := Real.goldenRatio_sq
  have hp := Real.goldenRatio_pos
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 : φ < 2 := by nlinarith
  have hr2 : r ^ 2 < 3 + φ := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 3 + φ by positivity),
      mul_pos (sub_pos.mpr hc) (show 0 < √(3 + φ) + r by positivity)]
  rcases hre with h | h
  · let t := 1 / 2 - c
    have ht : 0 ≤ t := by dsimp [t, c]; linarith
    have ht' : 0 ≤ 1 - t := by dsimp [t, c]; linarith
    have hnorm (w : ℂ) : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; ring
    have hlen := hnorm u
    rw [hu, h] at hlen
    have h₁ : v.re ^ 2 + v.im ^ 2 ≤ (r / 2) ^ 2 := by
      rw [hnorm]; exact pow_le_pow_left₀ (norm_nonneg _) hv _
    have h₂ : (v.re - u.re) ^ 2 + (v.im - u.im) ^ 2 ≤ (r / 2) ^ 2 := by
      change (v - u).re ^ 2 + (v - u).im ^ 2 ≤ _
      rw [hnorm]; exact pow_le_pow_left₀ (norm_nonneg _) hnear _
    have hcomb := add_nonneg (mul_nonneg ht' (sub_nonneg.mpr h₁))
      (mul_nonneg ht (sub_nonneg.mpr h₂))
    have hsq := add_nonneg (sq_nonneg (v.re - (1 + t * u.re))) (sq_nonneg (v.im - t * u.im))
    rw [h] at hcomb hsq
    have heq : (1 - t) * ((r / 2) ^ 2 - (v.re ^ 2 + v.im ^ 2)) +
        t * ((r / 2) ^ 2 - ((v.re - c) ^ 2 + (v.im - u.im) ^ 2)) +
        ((v.re - (1 + t * c)) ^ 2 + (v.im - t * u.im) ^ 2) =
        (r / 2) ^ 2 - 2 * v.re + 1 + 2 * t * c + (t ^ 2 - t) * (c ^ 2 + u.im ^ 2) := by ring
    rw [show c ^ 2 + u.im ^ 2 = 1 by linarith] at heq
    dsimp [t, axial, spacing, c, d] at heq hcomb hsq hx
    nlinarith only [heq, hcomb, hsq, hx, hφ, hr2]
  · have hreal := (Complex.re_le_norm (v - u)).trans hnear
    rw [sub_re, h] at hreal
    dsimp [axial, spacing, c, d] at hx hreal
    nlinarith [sq_nonneg r]

private theorem proj_step (n : Label) (j : Fin 5) :
    proj (n + basis j) = proj n + dir j := by
  classical
  simp only [proj, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [basis]
  · intro k _ hk
    simp [basis, Pi.single_eq_of_ne hk]
  · simp

private theorem proj_back (n : Label) (j : Fin 5) :
    proj (n - basis j) = proj n - dir j := by
  have h := proj_step (n - basis j) j
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

private theorem rotated_re (n : Label) (j : Fin 5) :
    (proj n * (starRingEnd ℂ) (dir j)).re = ∑ k, (n k : ℝ) * (dir (k - j)).re := by
  simp only [proj, Finset.sum_mul, mul_assoc, relative_dir, re_sum, mul_re, intCast_re,
    intCast_im, zero_mul, sub_zero]

private theorem axial_proj (n : Label) (hw : weight n = 0) (j : Fin 5) :
    (proj n * (starRingEnd ℂ) (dir j)).re =
      (1 - d) * (n j : ℝ) + spacing * ((n (j + 1) : ℝ) + n (j - 1)) := by
  have hw' : (∑ k, (n k : ℝ)) = 0 := by exact_mod_cast hw
  rw [rotated_re]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hw' ⊢
  change (n 0 : ℝ) + (n 1 + (n 2 + (n 3 + n 4))) = 0 at hw'
  simp only [dir_re]
  fin_cases j
  · change (n 0 : ℝ) * 1 + ((n 1 : ℝ) * c + ((n 2 : ℝ) * d + ((n 3 : ℝ) * d + ((n 4 : ℝ) * c)))) =
      (1 - d) * (n 0 : ℝ) + (c - d) * ((n 1 : ℝ) + n 4)
    linear_combination d * hw'
  · change (n 0 : ℝ) * c + ((n 1 : ℝ) * 1 + ((n 2 : ℝ) * c + ((n 3 : ℝ) * d + ((n 4 : ℝ) * d)))) =
      (1 - d) * (n 1 : ℝ) + (c - d) * ((n 2 : ℝ) + n 0)
    linear_combination d * hw'
  · change (n 0 : ℝ) * d + ((n 1 : ℝ) * c + ((n 2 : ℝ) * 1 + ((n 3 : ℝ) * c + ((n 4 : ℝ) * d)))) =
      (1 - d) * (n 2 : ℝ) + (c - d) * ((n 3 : ℝ) + n 1)
    linear_combination d * hw'
  · change (n 0 : ℝ) * d + ((n 1 : ℝ) * d + ((n 2 : ℝ) * c + ((n 3 : ℝ) * 1 + ((n 4 : ℝ) * c)))) =
      (1 - d) * (n 3 : ℝ) + (c - d) * ((n 4 : ℝ) + n 2)
    linear_combination d * hw'
  · change (n 0 : ℝ) * c + ((n 1 : ℝ) * d + ((n 2 : ℝ) * d + ((n 3 : ℝ) * c + ((n 4 : ℝ) * 1)))) =
      (1 - d) * (n 4 : ℝ) + (c - d) * ((n 0 : ℝ) + n 3)
    linear_combination d * hw'

private theorem rotated_norm (j : Fin 5) (w : ℂ) :
    ‖w * (starRingEnd ℂ) (dir j)‖ = ‖w‖ := by simp [norm_dir]

private theorem dir_re_of_ne {j k : Fin 5} (h : k ≠ j) :
    (dir (k - j)).re = c ∨ (dir (k - j)).re = d := by
  simp only [dir_re, sub_ne_zero.mpr h, ↓reduceIte]
  split <;> simp

private theorem leaf_of_level {r : ℝ} (hr : 0 ≤ r) (hcrit : r < √(3 + φ))
    (x : ℂ) (j : Fin 5) (m : ℤ)
    (hm : ∀ p : ℤ, spacing / 2 - (3 + φ - r ^ 2) / 16 <
      |(1 - d) * (m : ℝ) + (1 / 2 - (x * (starRingEnd ℂ) (dir j)).re) + spacing * p|)
    (n : Label) (hw : weight n = 0) (hnj : n j = m)
    (hlo : ‖proj n - x‖ ≤ r / 2) (hhi : ‖proj (n + basis j) - x‖ ≤ r / 2) :
    (∀ k ≠ j, r / 2 < ‖proj (n + basis k) - x‖) ∨
    (∀ k ≠ j, r / 2 < ‖proj (n + basis j - basis k) - x‖) := by
  let q := (proj n - x) * (starRingEnd ℂ) (dir j)
  have hmid := hm (n (j + 1) + n (j - 1))
  have hform : (1 - d) * (m : ℝ) + (1 / 2 - (x * (starRingEnd ℂ) (dir j)).re) +
      spacing * (((n (j + 1) + n (j - 1) : ℤ) : ℝ)) = q.re + 1 / 2 := by
    simp only [q, sub_mul, sub_re, axial_proj n hw, hnj, Int.cast_add]
    ring
  rw [hform, lt_abs] at hmid
  have hrot : (proj (n + basis j) - x) * (starRingEnd ℂ) (dir j) = q + 1 := by
    rw [proj_step, add_sub_right_comm, add_mul, relative_dir, sub_self]
    simp [q, dir]
  have hq : ‖q‖ ≤ r / 2 := by simpa only [q, rotated_norm] using hlo
  rcases hmid with h | h
  · right
    have hqr : ‖q + 1‖ ≤ r / 2 := by rwa [← hrot, rotated_norm]
    intro k hk
    have hu := lens hr hcrit (norm_dir (k - j)) (dir_re_of_ne hk) hqr
      (by simp only [add_re, one_re]; dsimp [axial]; linarith)
    rw [← rotated_norm j, proj_back, sub_right_comm, sub_mul, relative_dir, hrot]
    exact hu
  · left
    intro k hk
    have hneg : ‖ - q‖ ≤ r / 2 := by simpa only [norm_neg] using hq
    have hu := lens hr hcrit (norm_dir (k - j)) (dir_re_of_ne hk) hneg
      (by simp only [neg_re]; dsimp [axial]; linarith)
    rw [← rotated_norm j, proj_step, add_sub_right_comm, add_mul, relative_dir]
    convert hu using 1
    rw [← norm_neg (-q - dir (k - j))]
    simp [q, add_comm]

/-- Each coordinate has two uniformly bounded cuts outside the initial labels. At either
cut every active crossing edge has a leaf endpoint. -/
theorem exists_walls {r : ℝ} (hr : 0 ≤ r) (hcrit : r < √(3 + φ)) :
    ∃ N : ℕ, ∀ x : ℂ, ‖x‖ ≤ 4 → ∀ j : Fin 5, ∃ lo hi : ℤ,
      -(N : ℤ) ≤ lo ∧ lo < -2 ∧ 2 < hi ∧ hi ≤ N ∧
      ∀ m : ℤ, (m = lo ∨ m = hi) → ∀ n : Label, weight n = 0 → n j = m →
        ‖proj n - x‖ ≤ r / 2 → ‖proj (n + basis j) - x‖ ≤ r / 2 →
          ((∀ k ≠ j, r / 2 < ‖proj (n + basis k) - x‖) ∨
           (∀ k ≠ j, r / 2 < ‖proj (n + basis j - basis k) - x‖)) := by
  have hp := Real.one_lt_goldenRatio
  have hL : 0 < spacing := by dsimp [spacing, c, d]; linarith
  have hη : 0 < (3 + φ - r ^ 2) / 16 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 3 + φ by linarith),
      mul_pos (sub_pos.mpr hcrit) (show 0 < √(3 + φ) + r by positivity)]
  have hφ : (1 - d) / spacing = φ := by
    rw [div_eq_iff hL.ne']
    dsimp [spacing, c, d]
    nlinarith [Real.goldenRatio_sq]
  obtain ⟨N, hN⟩ := exists_levels hL hη (hφ ▸ Real.goldenRatio_irrational :
    Irrational ((1 - d) / spacing))
  refine ⟨N, fun x _ j ↦ ?_⟩
  obtain ⟨lo, hi, hlo, hl, hh, hhi, hm⟩ :=
    hN (1 / 2 - (x * (starRingEnd ℂ) (dir j)).re)
  exact ⟨lo, hi, hlo, hl, hh, hhi, fun m h ↦ leaf_of_level hr hcrit x j m (hm m h)⟩

end TDCSG.Five.Walls
