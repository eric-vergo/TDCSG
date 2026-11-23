/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
module

public import TDCSG.CriticalRadius.Five.Chord
public import TDCSG.CriticalRadius.Five.Confinement

/-!
# The fivefold critical radius

Two closed disks of radius `r` about `-1` and `1`, each turned clockwise by a fifth of a turn,
generate the group `GG 5 5 r r` of permutations of `ℂ`. It is finite exactly when
`r < √(3 + φ)`, where `φ` is the golden ratio, so the critical radius of the fivefold family is
`√(3 + φ)`.

The proof has two halves.

* At and above `√(3 + φ)`, three words act on a chord through `0` as an irrational rotation, so
  the orbit of `0` is infinite (`TDCSG.CriticalRadius.Five.Chord`).
* Below `√(3 + φ)`, the disk centres met along a word are labelled by `ℤ⁵`, words give walks in
  a graph on the labels (`TDCSG.CriticalRadius.Five.Labels`), the lens estimate
  (`TDCSG.CriticalRadius.Five.Lens`) turns recurring good levels into barriers for these walks
  (`TDCSG.CriticalRadius.Five.Levels`), and the walks stay in a box, which bounds every orbit
  uniformly (`TDCSG.CriticalRadius.Five.Confinement`).

The written proofs are `notes/proofs/critical-radius-n5.md` (Part A) and
`notes/proofs/sharp-lower-bound-n5-pentagrid.md`.

## Main statements

* `TDCSG.CriticalRadius.criticalRadius_five`: `criticalRadius 5 = √(3 + φ)`.
* `TDCSG.CriticalRadius.finite_GG_five_iff`: `GG 5 5 r r` is finite if and only if
  `r < √(3 + φ)`.
* `TDCSG.CriticalRadius.sSup_setOf_finite_GG_five`: the supremum of the radii with a finite
  group is `√(3 + φ)`.
* `TDCSG.CriticalRadius.infinite_GG_five`: for `r ≥ √(3 + φ)` the group `GG 5 5 r r` is
  infinite.
* `TDCSG.CriticalRadius.infinite_orbit_zero_five`: for `r ≥ √(3 + φ)` the orbit of `0` is
  infinite.
-/

@[expose] public section

open scoped Real goldenRatio

namespace TDCSG.CriticalRadius

/-- `GG 5 5 r r` is finite exactly below `√(3 + φ)`. -/
theorem finite_GG_five_iff (r : ℝ) : Finite (GG 5 5 r r) ↔ r < √(3 + φ) :=
  ⟨fun h ↦ lt_of_not_ge fun hr ↦ not_finite_iff_infinite.2 (Five.infinite_GG hr) h,
    Five.finite_GG_of_lt⟩

/-- **The fivefold critical radius** is `√(3 + φ)`. -/
theorem criticalRadius_five : criticalRadius 5 = √(3 + φ) :=
  criticalRadius_eq_of_forall_finite_iff finite_GG_five_iff

/-- The supremum of the radii at which `GG 5 5 r r` is finite is `√(3 + φ)`. -/
theorem sSup_setOf_finite_GG_five : sSup {r : ℝ | Finite (GG 5 5 r r)} = √(3 + φ) := by
  rw [show {r : ℝ | Finite (GG 5 5 r r)} = Set.Iio √(3 + φ) from
    Set.ext finite_GG_five_iff, csSup_Iio]

/-- For every `r ≥ √(3 + φ)` the group `GG 5 5 r r` is infinite. -/
theorem infinite_GG_five {r : ℝ} (hr : √(3 + φ) ≤ r) : Infinite (GG 5 5 r r) :=
  Five.infinite_GG hr

/-- For every `r ≥ √(3 + φ)`, including the critical radius itself, the orbit of `0` under
`GG 5 5 r r` is infinite. -/
theorem infinite_orbit_zero_five {r : ℝ} (hr : √(3 + φ) ≤ r) : (orbit 5 5 r r 0).Infinite :=
  Five.infinite_orbit_zero hr

end TDCSG.CriticalRadius

end
