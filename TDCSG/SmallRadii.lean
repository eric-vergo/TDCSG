/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import TDCSG.Group

/-!
# Disjoint and tangent disks: all orbits are finite

If both radii are at most `1`, the two closed disks meet at most in the point `0`, and every
orbit is finite (`TDCSG.finite_orbit_of_le_one`). This is the orbit part of Proposition 7.1 of
`notes/proofs/theorem1-converse.md`, for all rotation orders.

## Main definitions

* `TDCSG.rotOrbit n c z`: the orbit of `z` under the full-plane rotation by `-2π / n` about `c`.

## Main statements

* `TDCSG.finite_rotOrbit`: such an orbit is finite.
* `TDCSG.diskPerm_mem_preserving_of_finite`: a disk rotation preserves a finite set as soon as
  the rotation maps the points of the set lying in the disk into the set.
* `TDCSG.finite_orbit_of_le_one`: for radii at most `1` every orbit is finite.

## Implementation notes

The written proof bounds the order of the group in the tangent case. Only finiteness of orbits
is needed here: the orbit of `p` lies in the finite set formed by `p`, the orbits of `p` under
the rotation of each disk containing `p`, and the orbits of the contact point `0` under both
rotations, and this set is preserved by both generators.
-/

@[expose] public section

open Complex Metric Equiv

namespace TDCSG

/-- The orbit of `z` under the full-plane rotation by `-2π / n` about `c`. -/
def rotOrbit (n : ℕ) (c z : ℂ) : Set ℂ := Set.range fun j : ℕ ↦ (rotation n c)^[j] z

/-- A point lies in its own rotation orbit. -/
theorem mem_rotOrbit_self (n : ℕ) (c z : ℂ) : z ∈ rotOrbit n c z := ⟨0, rfl⟩

/-- The rotation maps a rotation orbit into itself. -/
theorem rotation_mem_rotOrbit {n : ℕ} {c z y : ℂ} (hy : y ∈ rotOrbit n c z) :
    rotation n c y ∈ rotOrbit n c z := by
  obtain ⟨j, rfl⟩ := hy
  exact ⟨j + 1, Function.iterate_succ_apply' _ _ _⟩

/-- Points of a rotation orbit have the same distance to the centre. -/
theorem dist_of_mem_rotOrbit {n : ℕ} {c z y : ℂ} (hy : y ∈ rotOrbit n c z) :
    dist y c = dist z c := by
  obtain ⟨j, rfl⟩ := hy
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only at ih ⊢
    rw [Function.iterate_succ_apply', dist_rotation, ih]

/-- An orbit of the rotation by `-2π / n` is finite. -/
theorem finite_rotOrbit (n : ℕ) (c z : ℂ) : (rotOrbit n c z).Finite := by
  rcases eq_or_ne n 0 with rfl | hn
  · refine (Set.finite_singleton z).subset ?_
    rintro _ ⟨j, rfl⟩
    have : rotation 0 c = id := funext (rotation_zero c)
    simp [this]
  · refine ((Set.finite_lt_nat n).image fun j ↦ (rotation n c)^[j] z).subset ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨j % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn), ?_⟩
    change (rotation n c)^[j % n] z = (rotation n c)^[j] z
    conv_rhs => rw [← Nat.mod_add_div j n]
    rw [Function.iterate_add_apply, Function.iterate_mul, iterate_rotation_self hn,
      Function.iterate_id]
    rfl

/-- A disk rotation preserves a finite set `S` if the rotation maps every point of `S` lying in
the disk into `S`. -/
theorem diskPerm_mem_preserving_of_finite {n : ℕ} {c : ℂ} {r : ℝ} {S : Set ℂ} (hS : S.Finite)
    (h : ∀ y ∈ S, y ∈ closedBall c r → rotation n c y ∈ S) : diskPerm n c r ∈ preserving S := by
  have hm : Set.MapsTo (diskPerm n c r) S S := fun y hy ↦ by
    by_cases hyc : y ∈ closedBall c r
    · rw [diskPerm_apply, diskRotation_of_mem hyc]
      exact h y hy hyc
    · rw [diskPerm_apply, diskRotation_of_notMem hyc]
      exact hy
  have hbij := (hS.injOn_iff_bijOn_of_mapsTo hm).1 (diskPerm n c r).injective.injOn
  intro y hy
  obtain ⟨w, hw, rfl⟩ := hbij.surjOn hy
  exact ⟨hm (hm hw), by rw [Perm.inv_eq_iff_eq.mpr rfl]; exact hw⟩

/-- The two closed unit disks about `-1` and `1` meet only in `0`. -/
theorem eq_zero_of_dist_le_one {z : ℂ} (h₁ : dist z leftCenter ≤ 1)
    (h₂ : dist z rightCenter ≤ 1) : z = 0 := by
  rw [dist_eq_norm, leftCenter, sub_neg_eq_add] at h₁
  rw [dist_eq_norm, rightCenter] at h₂
  have e₁ := (sq_le_one_iff₀ (norm_nonneg _)).2 h₁
  have e₂ := (sq_le_one_iff₀ (norm_nonneg _)).2 h₂
  rw [← normSq_eq_norm_sq, normSq_apply] at e₁ e₂
  simp only [add_re, one_re, add_im, one_im, add_zero, sub_re, sub_im, sub_zero] at e₁ e₂
  apply Complex.ext <;> simp <;> nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- For radii at most `1` (disjoint or tangent closed disks) every orbit is finite. -/
theorem finite_orbit_of_le_one (n₁ n₂ : ℕ) {r₁ r₂ : ℝ} (h₁ : r₁ ≤ 1) (h₂ : r₂ ≤ 1) (p : ℂ) :
    (orbit n₁ n₂ r₁ r₂ p).Finite := by
  set R₁ := rotOrbit n₁ leftCenter
  set R₂ := rotOrbit n₂ rightCenter
  set S := {p} ∪ R₁ 0 ∪ R₂ 0 ∪ {y | p ∈ leftDisk r₁ ∧ y ∈ R₁ p} ∪
    {y | p ∈ rightDisk r₂ ∧ y ∈ R₂ p}
  have hS : S.Finite :=
    (((Set.finite_singleton p).union (finite_rotOrbit _ _ _)).union
      (finite_rotOrbit _ _ _)).union ((finite_rotOrbit n₁ leftCenter p).subset fun _ h ↦ h.2)
      |>.union ((finite_rotOrbit n₂ rightCenter p).subset fun _ h ↦ h.2)
  have hd₁ : dist (0 : ℂ) leftCenter = 1 := by simp [leftCenter]
  have hd₂ : dist (0 : ℂ) rightCenter = 1 := by simp [rightCenter]
  have hA0 : rotation n₁ leftCenter 0 ∈ S :=
    .inl (.inl (.inl (.inr (rotation_mem_rotOrbit (mem_rotOrbit_self _ _ _)))))
  have hB0 : rotation n₂ rightCenter 0 ∈ S :=
    .inl (.inl (.inr (rotation_mem_rotOrbit (mem_rotOrbit_self _ _ _))))
  refine (hS.subset (orbit_subset (.inl (.inl (.inl (.inl rfl)))) ?_ ?_))
  · refine diskPerm_mem_preserving_of_finite hS fun y hy hyc ↦ ?_
    have hy₁ : dist y leftCenter ≤ 1 := (mem_closedBall.1 hyc).trans h₁
    rcases hy with (((rfl | hy) | hy) | ⟨hp, hy⟩) | ⟨hp, hy⟩
    · exact .inl (.inr ⟨hyc, rotation_mem_rotOrbit (mem_rotOrbit_self _ _ _)⟩)
    · exact .inl (.inl (.inl (.inr (rotation_mem_rotOrbit hy))))
    · rw [eq_zero_of_dist_le_one hy₁ ((dist_of_mem_rotOrbit hy).trans hd₂).le]
      exact hA0
    · exact .inl (.inr ⟨hp, rotation_mem_rotOrbit hy⟩)
    · rw [eq_zero_of_dist_le_one hy₁
        (((dist_of_mem_rotOrbit hy).trans_le (mem_closedBall.1 hp)).trans h₂)]
      exact hA0
  · refine diskPerm_mem_preserving_of_finite hS fun y hy hyc ↦ ?_
    have hy₂ : dist y rightCenter ≤ 1 := (mem_closedBall.1 hyc).trans h₂
    rcases hy with (((rfl | hy) | hy) | ⟨hp, hy⟩) | ⟨hp, hy⟩
    · exact .inr ⟨hyc, rotation_mem_rotOrbit (mem_rotOrbit_self _ _ _)⟩
    · rw [eq_zero_of_dist_le_one ((dist_of_mem_rotOrbit hy).trans hd₁).le hy₂]
      exact hB0
    · exact .inl (.inl (.inr (rotation_mem_rotOrbit hy)))
    · rw [eq_zero_of_dist_le_one
        (((dist_of_mem_rotOrbit hy).trans_le (mem_closedBall.1 hp)).trans h₁) hy₂]
      exact hB0
    · exact .inr ⟨hp, rotation_mem_rotOrbit hy⟩

end TDCSG

end
