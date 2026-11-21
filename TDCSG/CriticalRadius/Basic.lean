/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import TDCSG.Disjoint
public import TDCSG.Monotonicity

/-!
# The critical radius of the equal-radius family

For a rotation order `n`, the radii `r` at which the equal-radius group `GG n n r r` is infinite
form an up-set (`TDCSG.infinite_GG_of_le`), contained in `[1, ∞)`. The critical radius
`TDCSG.criticalRadius n` is its infimum. This file proves the basic properties of this
definition, and sets up words in the generators acting on segments, the tool behind the
infinite-orbit constructions of `notes/proofs/critical-radius-n5.md` and its companions.

## Main definitions

* `TDCSG.infiniteRadii n`: the set of radii `r` at which `GG n n r r` is infinite.
* `TDCSG.criticalRadius n`: its infimum.
* `TDCSG.Letter`: the four letters `a`, `a⁻¹`, `b`, `b⁻¹`.
* `TDCSG.applyWord n r w`: the action of the word `w`, read left to right, at radius `r`.
* `TDCSG.globalWord n w`: the composite of the global rotations of the letters of `w`.
* `TDCSG.WordValid n r w P Q`: every letter of `w` is applied inside its closed disk at both
  current endpoints of the segment from `P` to `Q`.

## Main statements

* `TDCSG.infinite_GG_of_le`: infinitude passes to larger radii.
* `TDCSG.one_le_of_mem_infiniteRadii`: the group is finite for every radius below `1`.
* `TDCSG.criticalRadius_le`, `TDCSG.finite_GG_of_lt_criticalRadius`,
  `TDCSG.infinite_GG_of_criticalRadius_lt`: the critical radius separates finite from infinite.
* `TDCSG.infinite_GG_of_infinite_orbit`: an infinite orbit forces an infinite group.
* `TDCSG.applyWord_mem_orbit`: words map orbits into themselves.
* `TDCSG.applyWord_segment`: a word valid on a segment acts on it as its global rotation.

## Implementation notes

If `GG n n r r` is finite for every `r` (for example when `n ∣ 4` or `n ∣ 6`), then
`TDCSG.infiniteRadii n` is empty and `TDCSG.criticalRadius n` is the junk value `0`. Every
statement about the critical radius beyond `TDCSG.finite_GG_of_lt_criticalRadius` therefore
assumes, or proves, that `TDCSG.infiniteRadii n` is nonempty.
-/

@[expose] public section

open Complex Metric Equiv
open scoped Real

namespace TDCSG

/-! ### The critical radius -/

/-- The radii `r` at which the equal-radius group `GG n n r r` is infinite. -/
def infiniteRadii (n : ℕ) : Set ℝ := {r | Infinite (GG n n r r)}

/-- The critical radius of the equal-radius family `GG n n r r`: the infimum of the radii at
which the group is infinite. It is `0` if the group is finite for every radius. -/
noncomputable def criticalRadius (n : ℕ) : ℝ := sInf (infiniteRadii n)

theorem mem_infiniteRadii {n : ℕ} {r : ℝ} : r ∈ infiniteRadii n ↔ Infinite (GG n n r r) :=
  Iff.rfl

/-- Infinitude of the group passes to larger radii. -/
theorem infinite_GG_of_le {n : ℕ} {r r' : ℝ} (h : r ≤ r') (hr : Infinite (GG n n r r)) :
    Infinite (GG n n r' r') := by
  rw [← not_finite_iff_infinite] at hr ⊢
  exact fun h' ↦ hr (finite_GG_of_le n n h h h')

/-- The radii with an infinite group form an up-set. -/
theorem mem_infiniteRadii_of_le {n : ℕ} {r r' : ℝ} (h : r ≤ r') (hr : r ∈ infiniteRadii n) :
    r' ∈ infiniteRadii n :=
  infinite_GG_of_le h hr

/-- If both generators are the identity, the group is trivial. -/
theorem GG_eq_bot_of_eq_one {n₁ n₂ : ℕ} {r₁ r₂ : ℝ} (hA : permA n₁ r₁ = 1)
    (hB : permB n₂ r₂ = 1) : GG n₁ n₂ r₁ r₂ = ⊥ := by
  rw [GG, hA, hB, Set.pair_eq_singleton, Subgroup.closure_singleton_one]

theorem diskPerm_eq_one_of_nonpos (n : ℕ) (c : ℂ) {r : ℝ} (hr : r ≤ 0) : diskPerm n c r = 1 :=
  Perm.ext fun z ↦ by
    by_cases hz : z ∈ closedBall c r
    · have : z = c := dist_le_zero.1 ((mem_closedBall.1 hz).trans hr)
      subst this
      simp [diskRotation_of_mem hz, rotation]
    · simp [diskRotation_of_notMem hz]

theorem diskPerm_zero (c : ℂ) (r : ℝ) : diskPerm 0 c r = 1 :=
  Perm.ext fun z ↦ by simp [diskRotation_zero]

/-- The equal-radius group is finite for every radius `r < 1`. -/
theorem finite_GG_of_lt_one (n : ℕ) {r : ℝ} (hr : r < 1) : Finite (GG n n r r) := by
  rcases le_or_gt r 0 with h0 | h0
  · rw [GG_eq_bot_of_eq_one (diskPerm_eq_one_of_nonpos n _ h0)
      (diskPerm_eq_one_of_nonpos n _ h0)]
    infer_instance
  rcases eq_or_ne n 0 with rfl | hn
  · rw [GG_eq_bot_of_eq_one (diskPerm_zero _ _) (diskPerm_zero _ _)]
    infer_instance
  · refine Nat.finite_of_card_ne_zero ?_
    rw [card_GG_of_add_lt_two hn hn h0 h0 (by linarith)]
    exact mul_ne_zero hn hn

/-- The group is finite below radius `1`, so every radius with an infinite group is at
least `1`. -/
theorem one_le_of_mem_infiniteRadii {n : ℕ} {r : ℝ} (hr : r ∈ infiniteRadii n) : 1 ≤ r := by
  by_contra h
  exact not_finite_iff_infinite.2 hr (finite_GG_of_lt_one n (not_le.1 h))

theorem bddBelow_infiniteRadii (n : ℕ) : BddBelow (infiniteRadii n) :=
  ⟨1, fun _ ↦ one_le_of_mem_infiniteRadii⟩

/-- The critical radius is at most every radius with an infinite group. -/
theorem criticalRadius_le {n : ℕ} {r : ℝ} (hr : Infinite (GG n n r r)) :
    criticalRadius n ≤ r :=
  csInf_le (bddBelow_infiniteRadii n) hr

/-- Below the critical radius the group is finite. -/
theorem finite_GG_of_lt_criticalRadius {n : ℕ} {r : ℝ} (hr : r < criticalRadius n) :
    Finite (GG n n r r) := by
  by_contra h
  exact (criticalRadius_le (not_finite_iff_infinite.1 h)).not_gt hr

/-- Above the critical radius the group is infinite, provided it is infinite for some radius. -/
theorem infinite_GG_of_criticalRadius_lt {n : ℕ} (hne : (infiniteRadii n).Nonempty) {r : ℝ}
    (hr : criticalRadius n < r) : Infinite (GG n n r r) := by
  obtain ⟨s, hs, hsr⟩ := exists_lt_of_csInf_lt hne hr
  exact infinite_GG_of_le hsr.le hs

/-- If the group is infinite for some radius, the critical radius is at least `1`. -/
theorem one_le_criticalRadius {n : ℕ} (hne : (infiniteRadii n).Nonempty) :
    1 ≤ criticalRadius n :=
  le_csInf hne fun _ ↦ one_le_of_mem_infiniteRadii

/-- An infinite orbit forces an infinite group. -/
theorem infinite_GG_of_infinite_orbit {n₁ n₂ : ℕ} {r₁ r₂ : ℝ} {p : ℂ}
    (h : (orbit n₁ n₂ r₁ r₂ p).Infinite) : Infinite (GG n₁ n₂ r₁ r₂) := by
  rw [← not_finite_iff_infinite]
  intro hfin
  refine h ((Set.finite_range fun g : GG n₁ n₂ r₁ r₂ ↦ (g : Perm ℂ) p).subset ?_)
  rintro y ⟨g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

/-! ### Words acting on segments -/

/-- The four letters `a`, `a⁻¹`, `b`, `b⁻¹` of words in the generators. -/
inductive Letter
  /-- The left generator `a`. -/
  | a
  /-- The inverse `a⁻¹` of the left generator. -/
  | aInv
  /-- The right generator `b`. -/
  | b
  /-- The inverse `b⁻¹` of the right generator. -/
  | bInv
  deriving DecidableEq, Repr

namespace Letter

/-- The permutation of `ℂ` that a letter stands for, in the group `GG n n r r`. -/
noncomputable def perm (n : ℕ) (r : ℝ) : Letter → Perm ℂ
  | a => permA n r
  | aInv => (permA n r)⁻¹
  | b => permB n r
  | bInv => (permB n r)⁻¹

/-- The centre of the disk of a letter. -/
def center : Letter → ℂ
  | a | aInv => leftCenter
  | b | bInv => rightCenter

/-- The rotation factor of a letter: `exp (-2πi / n)` for `a` and `b`, its inverse for `a⁻¹`
and `b⁻¹`. -/
noncomputable def factor (n : ℕ) : Letter → ℂ
  | a | b => exp (-(2 * π * I / n))
  | aInv | bInv => exp (2 * π * I / n)

/-- The global rotation of the plane by which a letter acts on its closed disk. -/
noncomputable def glob (n : ℕ) (l : Letter) (z : ℂ) : ℂ :=
  l.center + l.factor n * (z - l.center)

theorem perm_mem_GG (n : ℕ) (r : ℝ) (l : Letter) : l.perm n r ∈ GG n n r r := by
  cases l
  exacts [permA_mem_GG n n r r, Subgroup.inv_mem _ (permA_mem_GG n n r r),
    permB_mem_GG n n r r, Subgroup.inv_mem _ (permB_mem_GG n n r r)]

theorem _root_.TDCSG.norm_exp_two_pi_I_div (n : ℕ) : ‖exp (2 * π * I / n)‖ = 1 := by
  rw [show 2 * π * I / n = ((2 * π / n : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

theorem norm_factor (n : ℕ) (l : Letter) : ‖l.factor n‖ = 1 := by
  cases l <;> simp only [factor, norm_exp_rotationAngle, norm_exp_two_pi_I_div]

theorem dist_glob (n : ℕ) (l : Letter) (z : ℂ) : dist (l.glob n z) l.center = dist z l.center := by
  simp [glob, dist_eq_norm, norm_factor]

/-- Inside its closed disk a letter acts as its global rotation. -/
theorem perm_apply_of_mem {n : ℕ} {r : ℝ} {l : Letter} {z : ℂ}
    (hz : z ∈ closedBall l.center r) : l.perm n r z = l.glob n z := by
  have hinv (c : ℂ) (hz : z ∈ closedBall c r) :
      (diskPerm n c r)⁻¹ z = c + exp (2 * π * I / n) * (z - c) := by
    rw [Perm.inv_eq_iff_eq]
    have hw : c + exp (2 * π * I / n) * (z - c) ∈ closedBall c r := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_exp_two_pi_I_div,
        one_mul, ← dist_eq_norm]
      exact hz
    rw [diskPerm_apply, diskRotation_of_mem hw, rotation, add_sub_cancel_left, ← mul_assoc,
      ← exp_add, neg_add_cancel, exp_zero, one_mul, add_sub_cancel]
  cases l
  · exact diskRotation_of_mem hz
  · exact hinv _ hz
  · exact diskRotation_of_mem hz
  · exact hinv _ hz

/-- A global rotation commutes with affine combinations. -/
theorem glob_affine (n : ℕ) (l : Letter) (P Q s : ℂ) :
    l.glob n (P + s * (Q - P)) = l.glob n P + s * (l.glob n Q - l.glob n P) := by
  simp only [glob]
  ring

end Letter

/-- The action of a word at radius `r`, read left to right: the head of the list is applied
first. -/
noncomputable def applyWord (n : ℕ) (r : ℝ) : List Letter → ℂ → ℂ
  | [], z => z
  | l :: w, z => applyWord n r w (l.perm n r z)

/-- The composite of the global rotations of the letters of a word, read left to right. -/
noncomputable def globalWord (n : ℕ) : List Letter → ℂ → ℂ
  | [], z => z
  | l :: w, z => globalWord n w (l.glob n z)

/-- A word `w` is valid at radius `r` on the segment from `P` to `Q` if every letter is applied,
under the global rotations of the earlier letters, to two endpoints in the letter's closed
disk. -/
def WordValid (n : ℕ) (r : ℝ) : List Letter → ℂ → ℂ → Prop
  | [], _, _ => True
  | l :: w, P, Q => P ∈ closedBall l.center r ∧ Q ∈ closedBall l.center r ∧
      WordValid n r w (l.glob n P) (l.glob n Q)

/-- Words map orbits into themselves. -/
theorem applyWord_mem_orbit {n : ℕ} {r : ℝ} {p : ℂ} (w : List Letter) {y : ℂ}
    (hy : y ∈ orbit n n r r p) : applyWord n r w y ∈ orbit n n r r p := by
  induction w generalizing y with
  | nil => exact hy
  | cons l w ih => exact ih (apply_mem_orbit (l.perm_mem_GG n r) hy)

/-- Validity passes to larger radii. -/
theorem WordValid.mono {n : ℕ} {r r' : ℝ} (h : r ≤ r') {w : List Letter} {P Q : ℂ}
    (hw : WordValid n r w P Q) : WordValid n r' w P Q := by
  induction w generalizing P Q with
  | nil => trivial
  | cons l w ih =>
    exact ⟨closedBall_subset_closedBall h hw.1, closedBall_subset_closedBall h hw.2.1,
      ih hw.2.2⟩

/-- A word valid on a segment acts on every point of it as its global rotation, which is
affine. This is Lemma 1.2 of `notes/proofs/critical-radius-n5.md`. -/
theorem applyWord_segment {n : ℕ} {r : ℝ} {w : List Letter} {P Q : ℂ}
    (hw : WordValid n r w P Q) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    applyWord n r w (P + s * (Q - P)) =
      globalWord n w P + s * (globalWord n w Q - globalWord n w P) := by
  induction w generalizing P Q with
  | nil => rfl
  | cons l w ih =>
    have hmem : P + s * (Q - P) ∈ closedBall l.center r := by
      have := (convex_closedBall l.center r).add_smul_sub_mem hw.1 hw.2.1 hs
      rwa [Complex.real_smul] at this
    simp only [applyWord, globalWord]
    rw [Letter.perm_apply_of_mem hmem, Letter.glob_affine]
    exact ih hw.2.2

/-- A word valid on a segment of a line `t ↦ t • V`, which translates both endpoints along the
line by `c`, translates every point of the segment by `c`. -/
theorem applyWord_line {n : ℕ} {r : ℝ} {w : List Letter} {V : ℂ} {t₀ t₁ c : ℝ} (h01 : t₀ < t₁)
    (hw : WordValid n r w (t₀ * V) (t₁ * V)) (h₀ : globalWord n w (t₀ * V) = (t₀ + c : ℝ) * V)
    (h₁ : globalWord n w (t₁ * V) = (t₁ + c : ℝ) * V) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    applyWord n r w (t * V) = (t + c : ℝ) * V := by
  have hd : t₁ - t₀ ≠ 0 := sub_ne_zero.2 h01.ne'
  set s := (t - t₀) / (t₁ - t₀) with hs_def
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [ht.1]) (by linarith)
    · rw [div_le_one (by linarith)]
      linarith [ht.2]
  have hst : (t : ℂ) = t₀ + s * (t₁ - t₀) := by
    rw [hs_def]
    push_cast
    field_simp [show (t₁ : ℂ) - t₀ ≠ 0 by exact_mod_cast hd]
    ring
  have key := applyWord_segment hw hs
  rw [h₀, h₁] at key
  rw [hst, show ((t₀ : ℂ) + s * (t₁ - t₀)) * V = t₀ * V + s * (t₁ * V - t₀ * V) by ring, key]
  push_cast
  rw [hst]
  ring

end TDCSG

end
