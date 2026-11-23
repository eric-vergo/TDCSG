/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import TDCSG.Group

/-!
# Monotonicity in the radii

Enlarging the radii can only enlarge orbits (`TDCSG.orbit_mono`), and finiteness of the group
passes to smaller radii (`TDCSG.finite_GG_of_le`). This is Theorem 3.1 and Theorem 3.4 of
`notes/proofs/boundary-contact.md`.

## Main statements

* `TDCSG.orbit_mono`: `orbit n₁ n₂ r₁ r₂ p ⊆ orbit n₁ n₂ r₁' r₂' p` when `r₁ ≤ r₁'`, `r₂ ≤ r₂'`.
* `TDCSG.finite_of_encard_orbit_le`, `TDCSG.finite_of_orbit_subset_insert_image`: the group is
  finite as soon as its orbits are uniformly bounded.
* `TDCSG.finite_GG_of_le`: if the group is finite at larger radii, it is finite at smaller ones.

## Implementation notes

Both statements are instances of monotonicity in the balls for compound symmetry groups,
`TDCSG.orbit_subset_orbit_of_eqOn` and `TDCSG.finite_of_forall_orbit_subset`. The written proof
deletes trivial steps from a chain of moves; here the same idea is that on the smaller disk the
rotation of the smaller disk agrees with the rotation of the larger one
(`TDCSG.eqOn_ballPerm_ballRotation`), while off it the rotation is the identity, so it preserves
every orbit at the larger radii.
-/

@[expose] public section

open Metric Equiv

namespace TDCSG

/-- The group is finitely generated, by `permA` and `permB`. -/
instance (n₁ n₂ : ℕ) (r₁ r₂ : ℝ) : Group.FG (GG n₁ n₂ r₁ r₂) := by
  rw [GG_eq_closure]
  exact Group.closure_finite_fg _

/-- `TDCSG.orbit` is the orbit of the action of the subgroup `TDCSG.GG` on `ℂ`. -/
theorem mulAction_orbit_eq (n₁ n₂ : ℕ) (r₁ r₂ : ℝ) (p : ℂ) :
    MulAction.orbit (GG n₁ n₂ r₁ r₂) p = orbit n₁ n₂ r₁ r₂ p := by
  ext y
  simp [MulAction.mem_orbit_iff, orbit, Subgroup.smul_def, Perm.smul_def]

/-- The two-disk group is finite as soon as its orbits are uniformly bounded. -/
theorem finite_of_encard_orbit_le {n₁ n₂ : ℕ} {r₁ r₂ : ℝ} (N : ℕ)
    (h : ∀ p, (orbit n₁ n₂ r₁ r₂ p).encard ≤ N) : Finite (GG n₁ n₂ r₁ r₂) :=
  MulAction.finite_of_encard_orbit_le (X := ℂ) N fun p ↦ by
    rw [mulAction_orbit_eq]
    exact h p

/-- The two-disk group is finite if every orbit consists of its base point and images of one
fixed finite set `T`, under a map that may depend on the base point. -/
theorem finite_of_orbit_subset_insert_image {n₁ n₂ : ℕ} {r₁ r₂ : ℝ} {ι : Type*} {T : Set ι}
    (hT : T.Finite) (f : ℂ → ι → ℂ) (h : ∀ p, orbit n₁ n₂ r₁ r₂ p ⊆ insert p (f p '' T)) :
    Finite (GG n₁ n₂ r₁ r₂) :=
  finite_of_encard_orbit_le (T.ncard + 1) fun p ↦ calc
    _ ≤ (insert p (f p '' T)).encard := Set.encard_le_encard (h p)
    _ ≤ (f p '' T).encard + 1 := Set.encard_insert_le _ _
    _ ≤ T.encard + 1 := by gcongr; exact Set.encard_image_le _ _
    _ = ((T.ncard + 1 : ℕ) : ℕ∞) := by rw [← hT.cast_ncard_eq]; push_cast; rfl

/-- A finite group has orbits of size at most its order. -/
theorem encard_orbit_le_card (n₁ n₂ : ℕ) (r₁ r₂ : ℝ) [Finite (GG n₁ n₂ r₁ r₂)] (p : ℂ) :
    (orbit n₁ n₂ r₁ r₂ p).encard ≤ Nat.card (GG n₁ n₂ r₁ r₂) := by
  rw [← mulAction_orbit_eq]
  exact encard_orbit_le_natCard _ p

/-- At each point, a disk rotation either fixes the point or agrees with the rotation of any
larger concentric disk. -/
theorem diskRotation_eq_or_of_le {n : ℕ} {c : ℂ} {r r' : ℝ} (h : r ≤ r') (z : ℂ) :
    diskRotation n c r z = z ∨ diskRotation n c r z = diskRotation n c r' z := by
  by_cases hz : z ∈ closedBall c r
  · right
    rw [diskRotation_of_mem hz, diskRotation_of_mem (closedBall_subset_closedBall h hz)]
  · exact .inl (diskRotation_of_notMem hz)

/-- On the smaller of two concentric disks, the rotation of the smaller disk agrees with the
rotation of the larger disk. -/
theorem eqOn_ballPerm_ballRotation {n : ℕ} {c : ℂ} {r r' : ℝ} (h : r ≤ r') :
    Set.EqOn (ballPerm c r (ballRotation n c r)) (diskPerm n c r') (closedBall c r) := by
  intro z hz
  rw [ballPerm_ballRotation, diskPerm_apply, diskPerm_apply, diskRotation_of_mem hz,
    diskRotation_of_mem (closedBall_subset_closedBall h hz)]

/-- Orbit monotonicity: enlarging the radii can only enlarge the orbit of a point. -/
theorem orbit_mono (n₁ n₂ : ℕ) {r₁ r₂ r₁' r₂' : ℝ} (h₁ : r₁ ≤ r₁') (h₂ : r₂ ≤ r₂') (p : ℂ) :
    orbit n₁ n₂ r₁ r₂ p ⊆ orbit n₁ n₂ r₁' r₂' p := by
  rw [← mulAction_orbit_eq, ← mulAction_orbit_eq]
  refine orbit_subset_orbit_of_eqOn (S := fun i ↦ {ballRotation _ _ _})
    (fun _ ↦ Subgroup.zpowers_eq_closure _) (fun i s hs ↦ ?_) p
  rw [Set.mem_singleton_iff] at hs
  subst hs
  fin_cases i
  · exact ⟨_, permA_mem_GG n₁ n₂ r₁' r₂', eqOn_ballPerm_ballRotation h₁⟩
  · exact ⟨_, permB_mem_GG n₁ n₂ r₁' r₂', eqOn_ballPerm_ballRotation h₂⟩

/-- Group monotonicity: if the group is finite for some radii, it is finite for all smaller
radii. -/
theorem finite_GG_of_le (n₁ n₂ : ℕ) {r₁ r₂ r₁' r₂' : ℝ} (h₁ : r₁ ≤ r₁') (h₂ : r₂ ≤ r₂')
    (h : Finite (GG n₁ n₂ r₁' r₂')) : Finite (GG n₁ n₂ r₁ r₂) :=
  finite_of_forall_orbit_subset (G := GG n₁ n₂ r₁ r₂) (G' := GG n₁ n₂ r₁' r₂') fun p ↦ by
    rw [mulAction_orbit_eq, mulAction_orbit_eq]
    exact orbit_mono n₁ n₂ h₁ h₂ p

end TDCSG

end
