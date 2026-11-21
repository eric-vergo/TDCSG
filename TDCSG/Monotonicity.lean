/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import TDCSG.BoundedOrbits
public import TDCSG.Group

/-!
# Monotonicity in the radii

Enlarging the radii can only enlarge orbits (`TDCSG.orbit_mono`), and finiteness of the group
passes to smaller radii (`TDCSG.finite_GG_of_le`). This is Theorem 3.1 and Theorem 3.4 of
`notes/proofs/boundary-contact.md`.

## Main statements

* `TDCSG.orbit_mono`: `orbit n₁ n₂ r₁ r₂ p ⊆ orbit n₁ n₂ r₁' r₂' p` when `r₁ ≤ r₁'`, `r₂ ≤ r₂'`.
* `TDCSG.finite_of_encard_orbit_le`: the group is finite as soon as its orbits are uniformly
  bounded.
* `TDCSG.finite_GG_of_le`: if the group is finite at larger radii, it is finite at smaller ones.

## Implementation notes

The written proof deletes trivial steps from a chain of moves. Here the same idea takes the form
of `TDCSG.mem_preserving_of_forall_eq_or`: at every point, a generator at the smaller radius
either fixes the point or acts as the generator at the larger radius, so it preserves every orbit
at the larger radius.
-/

@[expose] public section

open Metric Equiv

namespace TDCSG

instance (n₁ n₂ : ℕ) (r₁ r₂ : ℝ) : Group.FG (GG n₁ n₂ r₁ r₂) :=
  Group.closure_finite_fg _

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

theorem encard_orbit_le_card (n₁ n₂ : ℕ) (r₁ r₂ : ℝ) [Finite (GG n₁ n₂ r₁ r₂)] (p : ℂ) :
    (orbit n₁ n₂ r₁ r₂ p).encard ≤ Nat.card (GG n₁ n₂ r₁ r₂) := by
  have : orbit n₁ n₂ r₁ r₂ p = (fun g : GG n₁ n₂ r₁ r₂ ↦ (g : Perm ℂ) p) '' Set.univ := by
    ext y
    simp [orbit]
  rw [this, ← ENat.card_eq_coe_natCard, ← Set.encard_univ]
  exact Set.encard_image_le _ _

theorem diskRotation_eq_or_of_le {n : ℕ} {c : ℂ} {r r' : ℝ} (h : r ≤ r') (z : ℂ) :
    diskRotation n c r z = z ∨ diskRotation n c r z = diskRotation n c r' z := by
  by_cases hz : z ∈ closedBall c r
  · right
    rw [diskRotation_of_mem hz, diskRotation_of_mem (closedBall_subset_closedBall h hz)]
  · exact .inl (diskRotation_of_notMem hz)

/-- Orbit monotonicity: enlarging the radii can only enlarge the orbit of a point. -/
theorem orbit_mono (n₁ n₂ : ℕ) {r₁ r₂ r₁' r₂' : ℝ} (h₁ : r₁ ≤ r₁') (h₂ : r₂ ≤ r₂') (p : ℂ) :
    orbit n₁ n₂ r₁ r₂ p ⊆ orbit n₁ n₂ r₁' r₂' p :=
  orbit_subset (mem_orbit_self _ _ _ _ p)
    (mem_preserving_of_forall_eq_or
      (GG_le_preserving_orbit _ _ _ _ p (permA_mem_GG _ _ _ _)) (diskRotation_eq_or_of_le h₁))
    (mem_preserving_of_forall_eq_or
      (GG_le_preserving_orbit _ _ _ _ p (permB_mem_GG _ _ _ _)) (diskRotation_eq_or_of_le h₂))

/-- Group monotonicity: if the group is finite for some radii, it is finite for all smaller
radii. -/
theorem finite_GG_of_le (n₁ n₂ : ℕ) {r₁ r₂ r₁' r₂' : ℝ} (h₁ : r₁ ≤ r₁') (h₂ : r₂ ≤ r₂')
    (h : Finite (GG n₁ n₂ r₁' r₂')) : Finite (GG n₁ n₂ r₁ r₂) :=
  finite_of_encard_orbit_le (Nat.card (GG n₁ n₂ r₁' r₂')) fun p ↦
    (Set.encard_le_encard (orbit_mono n₁ n₂ h₁ h₂ p)).trans (encard_orbit_le_card _ _ _ _ p)

end TDCSG

end
