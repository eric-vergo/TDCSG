/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.GroupTheory.Finiteness
public import TDCSG.Group

/-!
# Main statements

This file states the main results about two-disk compound symmetry groups in compact form, using
only the definitions of `TDCSG.Basic` and `TDCSG.Group`, so that each statement can be checked
independently of its proof.

The written proofs are `notes/proofs/theorem1-converse.md` (cited as [T1]) and
`notes/proofs/boundary-contact.md` (cited as [BC]).

## Main statements

* `TDCSG.Statements.finite_of_encard_orbit_le`: a finitely generated group acting faithfully with
  all orbits of size at most `N` is finite ([T1] Proposition 4.2, [BC] Proposition 3.3).
* `TDCSG.Statements.orbit_mono`: orbits grow with the radii ([BC] Theorem 3.1).
* `TDCSG.Statements.finite_GG_of_le`: finiteness of the group passes to smaller radii
  ([BC] Theorem 3.4).
* `TDCSG.Statements.lcm_mem_iff`: `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}` holds exactly when `n₁` and `n₂`
  both divide `4` or both divide `6` ([T1] Corollary 5.2).
* `TDCSG.Statements.exists_encard_orbit_le`: if `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}`, the orbits are
  uniformly bounded, for all radii ([T1] Theorem 5.1(1)).
* `TDCSG.Statements.finite_GG`: if `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}`, the group is finite for all
  radii ([T1] Theorem 5.1(2)); this is the direction of Theorem 1 of arXiv:2302.12950 that the
  paper omits.
* `TDCSG.Statements.exists_orbit_eq_of_finite`: a finite orbit is unchanged for slightly larger
  radii ([BC] Theorem 4.1).
* `TDCSG.Statements.infinite_orbit_radii`: the radii at which a point has an infinite orbit form
  either the empty set or a closed half-line `[r₀, ∞)` with `r₀ > 0` ([BC] Corollary 4.2).
* `TDCSG.Statements.boundary_depth`, `TDCSG.Statements.touchesBoundary_or_accumulatesInside`,
  `TDCSG.Statements.of_not_touchesBoundary`: the boundary-contact dichotomy at the critical
  radius of a point ([BC] Theorem 5.1, parts 1–3).
* `TDCSG.Statements.card_GG_of_add_lt_two`: a sanity check of the definitions; for disjoint disks
  the group has order `n₁ * n₂` ([T1] Proposition 7.1(1)).
-/

@[expose] public section

open Metric

namespace TDCSG.Statements

/-- A finitely generated group acting faithfully on a set, with all orbits of size at most `N`,
is finite. -/
theorem finite_of_encard_orbit_le {G X : Type*} [Group G] [Group.FG G] [MulAction G X]
    [FaithfulSMul G X] (N : ℕ) (h : ∀ x : X, (MulAction.orbit G x).encard ≤ N) : Finite G :=
  sorry

/-- Orbit monotonicity: enlarging the radii can only enlarge the orbit of a point. -/
theorem orbit_mono (n₁ n₂ : ℕ) {r₁ r₂ r₁' r₂' : ℝ} (h₁ : r₁ ≤ r₁') (h₂ : r₂ ≤ r₂') (p : ℂ) :
    orbit n₁ n₂ r₁ r₂ p ⊆ orbit n₁ n₂ r₁' r₂' p :=
  sorry

/-- Group monotonicity: if the group is finite for some radii, it is finite for all smaller
radii. -/
theorem finite_GG_of_le (n₁ n₂ : ℕ) {r₁ r₂ r₁' r₂' : ℝ} (h₁ : r₁ ≤ r₁') (h₂ : r₂ ≤ r₂')
    (h : Finite (GG n₁ n₂ r₁' r₂')) : Finite (GG n₁ n₂ r₁ r₂) :=
  sorry

/-- The arithmetic hypothesis of the finiteness theorem, restated without `lcm`. -/
theorem lcm_mem_iff (n₁ n₂ : ℕ) :
    Nat.lcm n₁ n₂ ∈ ({1, 2, 3, 4, 6} : Finset ℕ) ↔ n₁ ∣ 4 ∧ n₂ ∣ 4 ∨ n₁ ∣ 6 ∧ n₂ ∣ 6 :=
  sorry

/-- If `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}`, then for all radii the orbits are uniformly bounded. -/
theorem exists_encard_orbit_le {n₁ n₂ : ℕ} (h : Nat.lcm n₁ n₂ ∈ ({1, 2, 3, 4, 6} : Finset ℕ))
    (r₁ r₂ : ℝ) : ∃ N : ℕ, ∀ p : ℂ, (orbit n₁ n₂ r₁ r₂ p).encard ≤ N :=
  sorry

/-- The converse direction of Theorem 1 of arXiv:2302.12950: if `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}`,
then the two-disk compound symmetry group is finite for all radii. -/
theorem finite_GG {n₁ n₂ : ℕ} (h : Nat.lcm n₁ n₂ ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) (r₁ r₂ : ℝ) :
    Finite (GG n₁ n₂ r₁ r₂) :=
  sorry

/-- Right stability of finite orbits (equal radii, closed disks). -/
theorem exists_orbit_eq_of_finite (n₁ n₂ : ℕ) {r₀ : ℝ} {p : ℂ}
    (h : (orbit n₁ n₂ r₀ r₀ p).Finite) :
    ∃ δ > 0, ∀ r, r₀ ≤ r → r < r₀ + δ → orbit n₁ n₂ r r p = orbit n₁ n₂ r₀ r₀ p :=
  sorry

/-- The radii at which the orbit of `p` is infinite form the empty set or a closed half-line. -/
theorem infinite_orbit_radii (n₁ n₂ : ℕ) (p : ℂ) :
    {r : ℝ | (orbit n₁ n₂ r r p).Infinite} = ∅ ∨
      ∃ r₀ > 0, {r : ℝ | (orbit n₁ n₂ r r p).Infinite} = Set.Ici r₀ :=
  sorry

/-- Boundary contact, part 1: at the critical radius `r₀` of `p`, orbit points come arbitrarily
close to a boundary circle from inside (or lie on it). -/
theorem boundary_depth (n₁ n₂ : ℕ) {r₀ : ℝ} {p : ℂ} (hO : (orbit n₁ n₂ r₀ r₀ p).Infinite)
    (hfin : ∀ r < r₀, (orbit n₁ n₂ r r p).Finite) :
    ∀ ε > 0, ∃ y ∈ orbit n₁ n₂ r₀ r₀ p, ∃ c ∈ ({leftCenter, rightCenter} : Set ℂ),
      r₀ - ε < dist y c ∧ dist y c ≤ r₀ :=
  sorry

/-- Boundary contact, part 2: at the critical radius of `p`, the orbit touches a boundary circle
or accumulates at one from inside. -/
theorem touchesBoundary_or_accumulatesInside (n₁ n₂ : ℕ) {r₀ : ℝ} {p : ℂ}
    (hO : (orbit n₁ n₂ r₀ r₀ p).Infinite) (hfin : ∀ r < r₀, (orbit n₁ n₂ r r p).Finite) :
    TouchesBoundary (orbit n₁ n₂ r₀ r₀ p) r₀ ∨ AccumulatesInside (orbit n₁ n₂ r₀ r₀ p) r₀ :=
  sorry

/-- Boundary contact, part 3: if the orbit at the critical radius touches no boundary circle,
then it accumulates at one from inside, it is the union of the orbits at smaller radii, and the
sizes of those orbits tend to infinity. -/
theorem of_not_touchesBoundary (n₁ n₂ : ℕ) {r₀ : ℝ} {p : ℂ}
    (hO : (orbit n₁ n₂ r₀ r₀ p).Infinite) (hfin : ∀ r < r₀, (orbit n₁ n₂ r r p).Finite)
    (hB : ¬TouchesBoundary (orbit n₁ n₂ r₀ r₀ p) r₀) :
    AccumulatesInside (orbit n₁ n₂ r₀ r₀ p) r₀ ∧
      orbit n₁ n₂ r₀ r₀ p = ⋃ r ∈ Set.Iio r₀, orbit n₁ n₂ r r p ∧
      ∀ N : ℕ, ∃ r₁ < r₀, ∀ r ∈ Set.Ico r₁ r₀, (N : ℕ∞) < (orbit n₁ n₂ r r p).encard :=
  sorry

/-- Sanity check of the definitions: for disjoint closed disks of positive radii the group is
`C_{n₁} × C_{n₂}`, of order `n₁ * n₂`. -/
theorem card_GG_of_add_lt_two {n₁ n₂ : ℕ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ + r₂ < 2) : Nat.card (GG n₁ n₂ r₁ r₂) = n₁ * n₂ :=
  sorry

end TDCSG.Statements

end
