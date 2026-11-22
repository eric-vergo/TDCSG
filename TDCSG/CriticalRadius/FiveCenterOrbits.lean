/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.FiveCenterPaths
import TDCSG.DiskUnion

/-! # Uniformly bounded active centers give finite fivefold disk-rotation groups -/

@[expose] public section

open Complex Metric Equiv

namespace TDCSG.Five.Walls

private theorem reach_next {r : ℝ} {x : ℂ} {v w : Label} (h : CenterReach r x v)
    (he : CenterEdge r x v w ∨ CenterEdge r x w v) : CenterReach r x w := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨s, hs, hp.tail he⟩

private def InWindow (r : ℝ) (x : ℂ) (n : Label) : Prop := ‖proj n - x‖ ≤ r / 2

/-- The current oriented pair of centers and the initial coordinates of the current point. -/
private def Framed (r : ℝ) (x y : ℂ) : Prop :=
  ∃ (n : Label) (j : Fin 5), weight n = 0 ∧
    2 * (x - proj n) = dir j * (y + 1) ∧
    (InWindow r x n → CenterReach r x n) ∧
    (InWindow r x (n + basis j) → CenterReach r x (n + basis j))

private theorem frame_right {x y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) :
    2 * (x - proj (n + basis j)) = dir j * (y - 1) := by
  rw [proj_add, proj_basis]
  linear_combination h

private theorem window_of_frame {x y p : ℂ} {n : Label} {j : Fin 5} {r : ℝ}
    (h : 2 * (x - proj n) = dir j * (y - p)) (hy : y ∈ closedBall p r) :
    InWindow r x n := by
  have e := congrArg norm h
  rw [norm_mul, norm_mul, norm_dir, one_mul, norm_sub_rev x, Complex.norm_ofNat] at e
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
    rw [mul_comm, e]; simpa [dist_eq_norm] using mem_closedBall.1 hy)

private theorem next_dir (j : Fin 5) :
    ∃ k : Fin 5, dir k * zeta ^ 4 = dir j := by
  refine ⟨⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩, ?_⟩
  simp only [dir, zeta_pow_mod, ← pow_add]
  rw [show j.val + 1 + 4 = j.val + 5 by omega, pow_add, zeta_pow_five, mul_one]

private theorem frame_left_step {x y : ℂ} {r : ℝ} (hf : Framed r x y) :
    Framed r x (genA 5 r y) := by
  obtain ⟨n, j, hn, h, hL, hR⟩ := hf
  by_cases hy : y ∈ closedBall leftCenter r
  · have hw := window_of_frame (p := leftCenter) (by simpa [leftCenter] using h) hy
    obtain ⟨k, hk⟩ := next_dir j
    refine ⟨n, k, hn, ?_, hL, fun hright ↦ reach_next (hL hw) (.inl ?_)⟩
    · rw [genA, diskRotation_of_mem hy, rotation, leftCenter, Nat.cast_ofNat,
        exp_rotationAngle_five]
      linear_combination h - (y + 1) * hk
    · exact ⟨hn, ⟨k, rfl⟩, hw, hright⟩
  · rw [genA, diskRotation_of_notMem hy]
    exact ⟨n, j, hn, h, hL, hR⟩

private theorem frame_right_step {x y : ℂ} {r : ℝ} (hf : Framed r x y) :
    Framed r x (genB 5 r y) := by
  obtain ⟨n, j, hn, h, hL, hR⟩ := hf
  by_cases hy : y ∈ closedBall rightCenter r
  · have h' := frame_right h
    have hw := window_of_frame (p := rightCenter) h' hy
    obtain ⟨k, hk⟩ := next_dir j
    let m := n + basis j - basis k
    have hm : m + basis k = n + basis j := sub_add_cancel _ _
    have hmw : weight m = 0 := by
      simp only [m, weight, Pi.sub_apply, Pi.add_apply, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      change weight n + weight (basis j) - weight (basis k) = 0
      rw [hn, weight_basis, weight_basis]; norm_num
    refine ⟨m, k, hmw, ?_, fun hleft ↦ reach_next (hR hw) (.inr ?_), ?_⟩
    · have ep : proj m + dir k = proj (n + basis j) := by
        rw [← proj_basis, ← proj_add, hm]
      rw [genB, diskRotation_of_mem hy, rotation, rightCenter, Nat.cast_ofNat,
        exp_rotationAngle_five]
      linear_combination h' - (y - 1) * hk - 2 * ep
    · exact ⟨hmw, ⟨k, hm.symm⟩, hleft, hw⟩
    · simpa [hm] using hR
  · rw [genB, diskRotation_of_notMem hy]
    exact ⟨n, j, hn, h, hL, hR⟩

private theorem framed_initial (r : ℝ) (z : ℂ) : Framed r ((z + 1) / 2) z := by
  refine ⟨0, 0, by simp [weight], ?_, fun _ ↦ ⟨0, .inl rfl, .refl⟩, ?_⟩
  · simp [proj, dir]; ring
  · intro _
    rw [zero_add]
    exact ⟨_, .inr rfl, .refl⟩

private theorem preserving_of_fifth {f : Perm ℂ} {S : Set ℂ}
    (hp : (⇑f)^[5] = id) (h : Set.MapsTo f S S) : f ∈ preserving S := by
  intro y hy
  refine ⟨h hy, ?_⟩
  have hid : f ((⇑f)^[4] y) = y := by
    simpa only [Function.iterate_succ_apply', id_eq] using congrFun hp y
  have hinv : f⁻¹ y = (⇑f)^[4] y := by
    apply f.injective
    simpa using hid.symm
  rw [hinv]
  exact h.iterate 4 hy

private theorem framed_orbit (r : ℝ) (z : ℂ) :
    orbit 5 5 r r z ⊆ {y | Framed r ((z + 1) / 2) y} := by
  apply orbit_subset (framed_initial r z)
  · exact preserving_of_fifth (iterate_genA_self (by decide) r) (fun _ h ↦ frame_left_step h)
  · exact preserving_of_fifth (iterate_genB_self (by decide) r) (fun _ h ↦ frame_right_step h)

/-- Uniform confinement of the integer labels of active centers bounds every point orbit. -/
theorem finite_GG_of_centerBox {r : ℝ} (hr : r ≤ 4) (hbox : CenterBox r) :
    Finite (GG 5 5 r r) := by
  classical
  obtain ⟨N, hN⟩ := hbox
  let labels := Set.pi Set.univ (fun _ : Fin 5 ↦ Set.Icc (-(N : ℤ)) N)
  have hl : labels.Finite := Set.Finite.pi (fun _ ↦ Set.finite_Icc _ _)
  let T := (Set.univ : Set (Bool × Fin 5)) ×ˢ labels
  have hT : T.Finite := Set.finite_univ.prod hl
  refine finite_of_encard_orbit_le (T.ncard + 1) fun z ↦ ?_
  let x := (z + 1) / 2
  let f := fun q : (Bool × Fin 5) × Label ↦
    (if q.1.1 then (1 : ℂ) else -1) + 2 * (x - proj q.2) / dir q.1.2
  have hsub : orbit 5 5 r r z ⊆ insert z (f '' T) := by
    rintro y ⟨g, hg, rfl⟩
    by_cases hz : z ∈ diskUnion r r
    · right
      have hx : ‖x‖ ≤ 4 := by
        have hz' := norm_le_of_mem_diskUnion hz
        rw [max_self] at hz'
        dsimp [x]
        rw [norm_div, Complex.norm_ofNat]
        have htri := norm_add_le z (1 : ℂ)
        rw [norm_one] at htri
        linarith
      obtain ⟨n, j, _, he, hL, hR⟩ := framed_orbit r z ⟨g, hg, rfl⟩
      have hd : dir j ≠ 0 := by
        intro h; have hj := norm_dir j; rw [h, norm_zero] at hj; linarith
      have hmem {m : Label} (hm : CenterReach r x m) : m ∈ labels :=
        fun k _ ↦ hN x hx m hm k
      rcases apply_mem_diskUnion hg hz with hy | hy
      · have hw := window_of_frame (p := leftCenter) (by simpa [leftCenter] using he) hy
        refine ⟨((false, j), n), ⟨Set.mem_univ _, hmem (hL hw)⟩, ?_⟩
        change -1 + 2 * (x - proj n) / dir j = g z
        change 2 * (x - proj n) = _ at he
        rw [he]; field_simp; ring
      · have he' := frame_right he
        have hw := window_of_frame (p := rightCenter) he' hy
        refine ⟨((true, j), n + basis j), ⟨Set.mem_univ _, hmem (hR hw)⟩, ?_⟩
        change 1 + 2 * (x - proj (n + basis j)) / dir j = g z
        change 2 * (x - proj (n + basis j)) = _ at he'
        rw [he']; field_simp; ring
    · left
      exact apply_eq_of_notMem_diskUnion hg hz
  calc
    _ ≤ (insert z (f '' T)).encard := Set.encard_le_encard hsub
    _ ≤ (f '' T).encard + 1 := Set.encard_insert_le _ _
    _ ≤ T.encard + 1 := by gcongr; exact Set.encard_image_le _ _
    _ = ((T.ncard + 1 : ℕ) : ℕ∞) := by rw [← hT.cast_ncard_eq]; push_cast; rfl

end TDCSG.Five.Walls
