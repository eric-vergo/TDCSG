/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TDCSG.Group

/-!
# Disjoint disks

For disjoint closed disks of positive radii the two generators commute, have orders exactly `n₁`
and `n₂`, and generate a group of order `n₁ * n₂` isomorphic to `C_{n₁} × C_{n₂}`. This is
Proposition 7.1(1) of `notes/proofs/theorem1-converse.md`. It serves as a check that the
definitions of `TDCSG.Group` are not degenerate. The product decomposition is the two-disk case
of `TDCSG.mulEquivPi`, the decomposition of the compound symmetry group of pairwise disjoint balls.

## Main statements

* `TDCSG.orderOf_diskPerm`: a disk rotation by `-2π / n` of a disk of positive radius has order
  exactly `n`.
* `TDCSG.commute_permA_permB`: for disjoint disks the generators commute.
* `TDCSG.nonempty_mulEquiv_of_add_lt_two`: for disjoint disks the group is isomorphic to
  `C_{n₁} × C_{n₂}`.
* `TDCSG.card_GG_of_add_lt_two`: for disjoint disks the group has order `n₁ * n₂`.
-/

@[expose] public section

open Complex Function Metric Equiv
open scoped Real

namespace TDCSG

/-- A disk rotation by `-2π / n`, `n ≠ 0`, of a disk of positive radius has order exactly `n`. -/
theorem orderOf_diskPerm {n : ℕ} (hn : n ≠ 0) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    orderOf (diskPerm n c r) = n := by
  have hpow (m : ℕ) (z : ℂ) : (diskPerm n c r ^ m) z = (diskRotation n c r)^[m] z := by
    rw [Perm.coe_pow]
    rfl
  rw [orderOf_eq_iff (Nat.pos_of_ne_zero hn)]
  refine ⟨Perm.ext fun z ↦ by rw [hpow, iterate_diskRotation_self hn]; rfl, fun m hmn hm h ↦ ?_⟩
  have hz : c + r ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_of_nonneg hr.le]
  have := congrArg (· (c + r)) h
  simp only [hpow, Perm.coe_one, id_eq, iterate_diskRotation_of_mem hz, iterate_rotation,
    add_sub_cancel_left] at this
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have h1 : exp (-(2 * π * I / n)) ^ m = 1 := by
    have : exp (-(2 * π * I / n)) ^ m * r = 1 * r := by linear_combination this
    exact mul_right_cancel₀ hr' this
  rw [← exp_nat_mul, exp_eq_one_iff] at h1
  obtain ⟨k, hk⟩ := h1
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  field_simp at hk
  have : -(m : ℤ) = n * k := by exact_mod_cast hk
  have hk0 : k < 0 := by nlinarith
  nlinarith

/-- The two closed disks are disjoint when `r₁ + r₂ < 2`. -/
theorem leftDisk_disjoint_rightDisk {r₁ r₂ : ℝ} (h : r₁ + r₂ < 2) :
    Disjoint (leftDisk r₁) (rightDisk r₂) := by
  rw [Set.disjoint_left]
  intro z h₁ h₂
  have := dist_triangle_left leftCenter rightCenter z
  rw [leftDisk, mem_closedBall] at h₁
  rw [rightDisk, mem_closedBall] at h₂
  have h2 : dist leftCenter rightCenter = 2 := by
    rw [leftCenter, rightCenter, dist_eq_norm]
    norm_num
  linarith

/-- A permutation fixing every point outside `S` maps `S` into itself. -/
theorem apply_mem_of_forall_notMem {σ : Perm ℂ} {S : Set ℂ} (hσ : ∀ z ∉ S, σ z = z) {z : ℂ}
    (hz : z ∈ S) : σ z ∈ S := by
  by_contra h
  have := hσ _ h
  rw [σ.injective this] at h
  exact h hz

/-- Permutations supported in disjoint sets commute. -/
theorem commute_of_disjoint {σ τ : Perm ℂ} {S T : Set ℂ} (hST : Disjoint S T)
    (hσ : ∀ z ∉ S, σ z = z) (hτ : ∀ z ∉ T, τ z = z) : Commute σ τ := by
  refine Perm.ext fun z ↦ ?_
  simp only [Perm.mul_apply]
  by_cases hzS : z ∈ S
  · have hσz := apply_mem_of_forall_notMem hσ hzS
    rw [hτ z (Set.disjoint_left.1 hST hzS), hτ _ (Set.disjoint_left.1 hST hσz)]
  · rw [hσ z hzS]
    by_cases hzT : z ∈ T
    · exact hσ _ (Set.disjoint_right.1 hST (apply_mem_of_forall_notMem hτ hzT))
    · rw [hτ z hzT, hσ z hzS]

/-- The left generator fixes every point outside the left disk. -/
theorem permA_apply_of_notMem {n : ℕ} {r : ℝ} {z : ℂ} (hz : z ∉ leftDisk r) :
    permA n r z = z :=
  diskRotation_of_notMem hz

/-- The right generator fixes every point outside the right disk. -/
theorem permB_apply_of_notMem {n : ℕ} {r : ℝ} {z : ℂ} (hz : z ∉ rightDisk r) :
    permB n r z = z :=
  diskRotation_of_notMem hz

/-- For disjoint disks the two generators commute. -/
theorem commute_permA_permB (n₁ n₂ : ℕ) {r₁ r₂ : ℝ} (h : r₁ + r₂ < 2) :
    Commute (permA n₁ r₁) (permB n₂ r₂) := by
  rw [permA, permB, ← ballPerm_ballRotation, ← ballPerm_ballRotation]
  exact commute_ballPerm (leftDisk_disjoint_rightDisk h) _ _

/-- The powers of a permutation fixing every point outside `S` fix every point outside `S`. -/
theorem zpowers_le_fixingSubgroup {σ : Perm ℂ} {S : Set ℂ} (hσ : ∀ z ∉ S, σ z = z) :
    Subgroup.zpowers σ ≤ fixingSubgroup (Perm ℂ) Sᶜ :=
  (Subgroup.zpowers_le).2 ((mem_fixingSubgroup_iff _).2 hσ)

/-- For disjoint disks the two disks of `TDCSG.GG` are pairwise disjoint. -/
theorem pairwise_disjoint_closedBall_of_add_lt_two {r₁ r₂ : ℝ} (h : r₁ + r₂ < 2) :
    Pairwise (Disjoint on fun i : Fin 2 ↦
      closedBall (![leftCenter, rightCenter] i) (![r₁, r₂] i)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact leftDisk_disjoint_rightDisk h
  · exact (leftDisk_disjoint_rightDisk h).symm
  · exact absurd rfl hij

/-- The cyclic group generated by a disk rotation is isomorphic to its image in the
permutations of `ℂ`. -/
noncomputable def zpowersBallRotationEquiv (n : ℕ) (c : ℂ) (r : ℝ) :
    Subgroup.zpowers (ballRotation n c r) ≃* Subgroup.zpowers (diskPerm n c r) :=
  ((Subgroup.zpowers _).equivMapOfInjective _ (ballPerm_injective c r)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.map_zpowers, ballPerm_ballRotation]))

/-- For disjoint closed disks the group is the internal direct product of the cyclic groups
generated by the two generators. -/
theorem nonempty_mulEquiv_zpowers_prod {n₁ n₂ : ℕ} {r₁ r₂ : ℝ} (h : r₁ + r₂ < 2) :
    Nonempty (GG n₁ n₂ r₁ r₂ ≃*
      Subgroup.zpowers (permA n₁ r₁) × Subgroup.zpowers (permB n₂ r₂)) :=
  ⟨(mulEquivPi (pairwise_disjoint_closedBall_of_add_lt_two h)).trans <|
    ({ piFinTwoEquiv _ with map_mul' := fun _ _ ↦ rfl } :
      (∀ i : Fin 2, Subgroup.zpowers (ballRotation (![n₁, n₂] i) (![leftCenter, rightCenter] i)
        (![r₁, r₂] i))) ≃* _).trans <|
    MulEquiv.prodCongr (zpowersBallRotationEquiv n₁ leftCenter r₁)
      (zpowersBallRotationEquiv n₂ rightCenter r₂)⟩

/-- For disjoint closed disks of positive radii the group is isomorphic to
`C_{n₁} × C_{n₂}`. -/
theorem nonempty_mulEquiv_of_add_lt_two {n₁ n₂ : ℕ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ + r₂ < 2) :
    Nonempty (GG n₁ n₂ r₁ r₂ ≃* Multiplicative (ZMod n₁) × Multiplicative (ZMod n₂)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_zpowers_prod (n₁ := n₁) (n₂ := n₂) h
  have hcyc (n : ℕ) (hn : n ≠ 0) (σ : Perm ℂ) (hσ : orderOf σ = n) :
      Nonempty (Subgroup.zpowers σ ≃* Multiplicative (ZMod n)) := by
    have : NeZero n := ⟨hn⟩
    refine ⟨mulEquivOfCyclicCardEq ?_⟩
    rw [Nat.card_zpowers, hσ, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  obtain ⟨e₁⟩ := hcyc n₁ hn₁ _ (orderOf_diskPerm hn₁ _ hr₁)
  obtain ⟨e₂⟩ := hcyc n₂ hn₂ _ (orderOf_diskPerm hn₂ _ hr₂)
  exact ⟨e.trans (MulEquiv.prodCongr e₁ e₂)⟩

/-- For disjoint closed disks of positive radii the group has order `n₁ * n₂`. -/
theorem card_GG_of_add_lt_two {n₁ n₂ : ℕ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ + r₂ < 2) : Nat.card (GG n₁ n₂ r₁ r₂) = n₁ * n₂ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_zpowers_prod (n₁ := n₁) (n₂ := n₂) h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers]
  exact congrArg₂ (· * ·) (orderOf_diskPerm hn₁ _ hr₁) (orderOf_diskPerm hn₂ _ hr₂)

end TDCSG

end
