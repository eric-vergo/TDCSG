/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TDCSG.CriticalRadius.Five.Cyclotomic

/-!
# Integer labels of the disk centres, and words as walks in the centre graph

This is §1 of `notes/proofs/sharp-lower-bound-n5-pentagrid.md`. Fix a starting point `z` and put
`x = (z + 1) / 2`. Along a word in the generators of `GG 5 5 r r` applied to `z`, pull the two
disk centres back to the initial frame and normalize them by `w ↦ (w + 1) / 2`. They are then
the projections `P(n) = ∑ⱼ nⱼ ζʲ` of integer labels `n ∈ ℤ⁵`, a letter acts exactly when the
normalized centre of its disk lies within `r / 2` of `x`, and every switch between the two
disks moves along one coordinate. So the active centres form a walk in a bipartite graph on the
labels of coordinate sum `0` and `1`, starting at `0` or `e₀`.

## Main definitions

* `TDCSG.Five.Label`: integer labels `ℤ⁵` of disk centres.
* `TDCSG.Five.dir j`: the direction `ζʲ` indexed by `j : Fin 5`.
* `TDCSG.Five.Label.basis`, `TDCSG.Five.Label.proj`, `TDCSG.Five.Label.weight`: the unit labels
  `e_j`, the projection `P` to the plane, and the coordinate sum.
* `TDCSG.Five.InWindow r x n`: the centre labelled `n` lies within `r / 2` of `x`.
* `TDCSG.Five.centerGraph r x`: the centre graph, joining a sum-zero label `n` in the window to
  each `n + e_j` in the window.
* `TDCSG.Five.CenterReach r x n`: `n` is reachable in the centre graph from `0` or `e₀`.
* `TDCSG.Five.Framed r x y`: the invariant carried along an orbit.

## Main statements

* `TDCSG.Five.framed_of_mem_orbit`: every point of the orbit of `z` is framed.
* `TDCSG.Five.exists_centerReach_of_mem_orbit`: every point of the orbit of `z` inside the two
  disks is `c + 2 (x - P(n)) / ζʲ` for a centre `c = ∓1`, a direction `j` and a label `n`
  reachable in the centre graph (Lemma 1 of the written proof).
-/

@[expose] public section

open Complex Metric
open scoped Real goldenRatio

namespace TDCSG.Five

@[inherit_doc] local notation "ζ" => zeta

/-! ### Directions -/

/-- The direction `ζʲ` indexed by `j : Fin 5`. -/
noncomputable def dir (j : Fin 5) : ℂ := ζ ^ (j : ℕ)

/-- `ζ⁰ = 1`. -/
@[simp] theorem dir_zero : dir 0 = 1 := by
  simp [dir]

/-- The directions form a homomorphism from `Fin 5` to the multiplicative group of `ℂ`. -/
theorem dir_add (j k : Fin 5) : dir (j + k) = dir j * dir k := by
  rw [dir, dir, dir, Fin.val_add, zeta_pow_mod, pow_add]

/-- Each direction has norm `1`. -/
@[simp] theorem norm_dir (j : Fin 5) : ‖dir j‖ = 1 := by
  simp [dir, norm_pow, norm_zeta]

/-- No direction is `0`. -/
theorem dir_ne_zero (j : Fin 5) : dir j ≠ 0 :=
  norm_ne_zero_iff.1 (by simp)

/-- Turning by `ζ⁴ = ζ⁻¹` moves the direction index down by one. -/
theorem dir_add_one_mul_zeta_pow_four (j : Fin 5) : dir (j + 1) * ζ ^ 4 = dir j := by
  rw [dir_add, show dir 1 = ζ from pow_one ζ, mul_assoc, ← pow_succ', zeta_pow_five, mul_one]

/-- `ζᵏ ζ̄ʲ = ζᵏ⁻ʲ`. -/
theorem dir_mul_conj_dir (j k : Fin 5) : dir k * (starRingEnd ℂ) (dir j) = dir (k - j) := by
  have h := dir_add (k - j) j
  rw [sub_add_cancel] at h
  rw [h, mul_assoc, mul_conj', norm_dir]
  simp

/-! ### Labels -/

/-- Integer labels of disk centres: the coefficients of the five directions `ζʲ`. -/
abbrev Label := Fin 5 → ℤ

namespace Label

/-- The unit label `e_j`. Moving from a sum-zero centre to the other centre in direction `j`
adds `e_j`. -/
def basis (j : Fin 5) : Label := Pi.single j 1

/-- The projection `P(n) = ∑ⱼ nⱼ ζʲ` of a label to the plane. -/
noncomputable def proj : Label →+ ℂ where
  toFun n := ∑ j, (n j : ℂ) * dir j
  map_zero' := by simp
  map_add' n m := by simp [add_mul, Finset.sum_add_distrib]

/-- The coordinate sum of a label. The left centres have sum `0`, the right centres sum `1`. -/
def weight : Label →+ ℤ where
  toFun n := ∑ j, n j
  map_zero' := by simp
  map_add' n m := by simp [Finset.sum_add_distrib]

/-- The projection as a sum. -/
theorem proj_apply (n : Label) : proj n = ∑ j, (n j : ℂ) * dir j :=
  rfl

/-- The coordinate sum as a sum. -/
theorem weight_apply (n : Label) : weight n = ∑ j, n j :=
  rfl

/-- A unit label projects to its direction. -/
@[simp] theorem proj_basis (j : Fin 5) : proj (basis j) = dir j := by
  simp [proj_apply, basis, Pi.single_apply]

/-- A unit label has coordinate sum `1`. -/
@[simp] theorem weight_basis (j : Fin 5) : weight (basis j) = 1 := by
  simp [weight_apply, basis, Pi.single_apply]

/-- The coordinates of a unit label. -/
theorem basis_apply (j k : Fin 5) : basis j k = if k = j then 1 else 0 :=
  Pi.single_apply j 1 k

end Label

open Label

/-! ### The centre graph -/

/-- The centre labelled `n` lies within `r / 2` of `x`. In the normalized initial frame of a
starting point `z`, with `x = (z + 1) / 2`, this is the disk test for the current point. -/
def InWindow (r : ℝ) (x : ℂ) (n : Label) : Prop :=
  ‖proj n - x‖ ≤ r / 2

/-- An edge of the centre graph, oriented from a sum-zero label `n` to `m = n + e_j`, with both
centres in the window. -/
def CenterEdge (r : ℝ) (x : ℂ) (n m : Label) : Prop :=
  weight n = 0 ∧ (∃ j, m = n + basis j) ∧ InWindow r x n ∧ InWindow r x m

/-- The centre graph at radius `r` for the window centre `x`. -/
def centerGraph (r : ℝ) (x : ℂ) : SimpleGraph Label :=
  SimpleGraph.fromRel (CenterEdge r x)

/-- The labels reachable in the centre graph from one of the two original centres `0`, `e₀`. -/
def CenterReach (r : ℝ) (x : ℂ) (n : Label) : Prop :=
  ∃ s : Label, (s = 0 ∨ s = basis 0) ∧ (centerGraph r x).Reachable s n

variable {r : ℝ} {x : ℂ}

/-- The two ends of an edge have coordinate sums `0` and `1`, so they differ. -/
theorem CenterEdge.ne {n m : Label} (h : CenterEdge r x n m) : n ≠ m := by
  rintro rfl
  obtain ⟨h0, ⟨j, hj⟩, -⟩ := h
  have := congrArg weight hj
  simp [h0] at this

/-- An edge is an adjacency of the centre graph. -/
theorem CenterEdge.adj {n m : Label} (h : CenterEdge r x n m) : (centerGraph r x).Adj n m :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨h.ne, .inl h⟩

/-- Two labels are adjacent in the centre graph when an edge joins them in either
orientation. -/
theorem centerGraph_adj {n m : Label} :
    (centerGraph r x).Adj n m ↔ CenterEdge r x n m ∨ CenterEdge r x m n := by
  rw [centerGraph, SimpleGraph.fromRel_adj]
  exact ⟨And.right, fun h ↦ ⟨h.elim CenterEdge.ne fun h ↦ h.ne.symm, h⟩⟩

/-- A neighbour of a reachable label is reachable. -/
theorem CenterReach.of_adj {n m : Label} (h : CenterReach r x n) (he : (centerGraph r x).Adj n m) :
    CenterReach r x m := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨s, hs, hp.trans he.reachable⟩

/-! ### Words give walks -/

/-- The invariant carried along an orbit with normalized base point `x`: the current point `y`
is framed by a sum-zero label `n` and a direction `j` with `2 (x - P(n)) = ζʲ (y + 1)`, so that
the current left and right centres are `n` and `n + e_j`; each of them that lies in the window
is reachable in the centre graph. -/
def Framed (r : ℝ) (x y : ℂ) : Prop :=
  ∃ (n : Label) (j : Fin 5), weight n = 0 ∧ 2 * (x - proj n) = dir j * (y + 1) ∧
    (InWindow r x n → CenterReach r x n) ∧
    (InWindow r x (n + basis j) → CenterReach r x (n + basis j))

/-- The frame of the right centre `n + e_j`. -/
theorem two_mul_sub_proj_add_basis {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) :
    2 * (x - proj (n + basis j)) = dir j * (y - 1) := by
  rw [map_add, proj_basis]
  linear_combination h

/-- A centre whose frame puts the current point in its disk lies in the window. -/
theorem inWindow_of_two_mul_sub_proj {y p : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y - p)) (hy : y ∈ closedBall p r) : InWindow r x n := by
  have e := congrArg norm h
  rw [norm_mul, norm_mul, norm_dir, one_mul, norm_sub_rev x, Complex.norm_ofNat] at e
  rw [mem_closedBall, dist_eq_norm] at hy
  rw [InWindow]
  linarith

/-- The left generator preserves frames: if it acts, the left centre is unchanged and the
direction index `j` becomes `j + 1`. -/
theorem Framed.genA {y : ℂ} (hf : Framed r x y) : Framed r x (TDCSG.genA 5 r y) := by
  obtain ⟨n, j, hn, h, hL, hR⟩ := hf
  by_cases hy : y ∈ closedBall leftCenter r
  · have hw := inWindow_of_two_mul_sub_proj (p := leftCenter) (by simpa [leftCenter] using h) hy
    refine ⟨n, j + 1, hn, ?_, hL, fun hright ↦ (hL hw).of_adj ?_⟩
    · rw [TDCSG.genA, diskRotation_of_mem hy, rotation, leftCenter, Nat.cast_ofNat,
        exp_rotationAngle_five]
      linear_combination h - (y + 1) * dir_add_one_mul_zeta_pow_four j
    · exact CenterEdge.adj ⟨hn, ⟨j + 1, rfl⟩, hw, hright⟩
  · rw [TDCSG.genA, diskRotation_of_notMem hy]
    exact ⟨n, j, hn, h, hL, hR⟩

/-- The right generator preserves frames: if it acts, the right centre is unchanged, the
direction index `j` becomes `j + 1`, and the left centre moves to the other end of the edge. -/
theorem Framed.genB {y : ℂ} (hf : Framed r x y) : Framed r x (TDCSG.genB 5 r y) := by
  obtain ⟨n, j, hn, h, hL, hR⟩ := hf
  by_cases hy : y ∈ closedBall rightCenter r
  · have h' := two_mul_sub_proj_add_basis h
    have hw := inWindow_of_two_mul_sub_proj (p := rightCenter) h' hy
    have hm : n + basis j - basis (j + 1) + basis (j + 1) = n + basis j := sub_add_cancel _ _
    have hmw : weight (n + basis j - basis (j + 1)) = 0 := by simp [hn]
    refine ⟨n + basis j - basis (j + 1), j + 1, hmw, ?_, fun hleft ↦ (hR hw).of_adj ?_,
      by rwa [hm]⟩
    · rw [TDCSG.genB, diskRotation_of_mem hy, rotation, rightCenter, Nat.cast_ofNat,
        exp_rotationAngle_five, map_sub, proj_basis]
      linear_combination h' - (y - 1) * dir_add_one_mul_zeta_pow_four j
    · exact (CenterEdge.adj ⟨hmw, ⟨j + 1, hm.symm⟩, hleft, hm ▸ hw⟩).symm
  · rw [TDCSG.genB, diskRotation_of_notMem hy]
    exact ⟨n, j, hn, h, hL, hR⟩

/-- Every point is framed for its own normalized base point, by the label `0` and the
direction index `0`, whose direction is `ζ⁰ = 1`. -/
theorem framed_self (r : ℝ) (z : ℂ) : Framed r ((z + 1) / 2) z := by
  refine ⟨0, 0, map_zero _, ?_, fun _ ↦ ⟨0, .inl rfl, .rfl⟩, fun _ ↦ ?_⟩
  · rw [map_zero, sub_zero, dir_zero, one_mul]
    ring
  · rw [zero_add]
    exact ⟨_, .inr rfl, .rfl⟩

/-- Every point of the orbit of `z` is framed for the normalized base point `(z + 1) / 2`. -/
theorem framed_of_mem_orbit {z y : ℂ} (hy : y ∈ orbit 5 5 r r z) : Framed r ((z + 1) / 2) y :=
  orbit_subset (S := {y | Framed r ((z + 1) / 2) y}) (framed_self r z)
    (mem_preserving_of_mapsTo (by norm_num) (iterate_genA_self (by norm_num) r)
      fun _ h ↦ Framed.genA h)
    (mem_preserving_of_mapsTo (by norm_num) (iterate_genB_self (by norm_num) r)
      fun _ h ↦ Framed.genB h) hy

/-- **Words give walks.** Every point `y` of the orbit of `z` that lies in one of the two disks
is `c + 2 (x - P(n)) / ζʲ`, with `x = (z + 1) / 2`, for a disk centre `c`, a direction `j` and a
label `n` reachable in the centre graph. -/
theorem exists_centerReach_of_mem_orbit {z y : ℂ} (hy : y ∈ orbit 5 5 r r z)
    (hyD : y ∈ diskUnion r r) :
    ∃ c ∈ ({leftCenter, rightCenter} : Set ℂ), ∃ (j : Fin 5) (n : Label),
      CenterReach r ((z + 1) / 2) n ∧ y = c + 2 * ((z + 1) / 2 - proj n) / dir j := by
  obtain ⟨n, j, -, he, hL, hR⟩ := framed_of_mem_orbit hy
  rcases hyD with hyD | hyD
  · have hw := inWindow_of_two_mul_sub_proj (p := leftCenter) (by simpa [leftCenter] using he) hyD
    refine ⟨leftCenter, .inl rfl, j, n, hL hw, ?_⟩
    rw [he, mul_div_cancel_left₀ _ (dir_ne_zero j), leftCenter]
    ring
  · have he' := two_mul_sub_proj_add_basis he
    have hw := inWindow_of_two_mul_sub_proj (p := rightCenter) he' hyD
    refine ⟨rightCenter, .inr rfl, j, n + basis j, hR hw, ?_⟩
    rw [he', mul_div_cancel_left₀ _ (dir_ne_zero j), rightCenter]
    ring

/-! ### A step in the two frames

The halved starting frame shows the two disks as the disks of radius `r / 2` about `0` and `1`
and the current point as `(y + 1) / 2`. The moving frame of `Framed` shows the window of radius
`r / 2` about `x`, fixed, and the current left and right centres `P(n)` and `P(n + e_j)`. The
rigid motion `frameMap n j` carries the first picture onto the second, and each acting letter
turns one centre of the moving frame about the other by `ζ`. -/

/-- `ζʲ⁺¹ = ζ ζʲ`. -/
theorem dir_add_one (j : Fin 5) : dir (j + 1) = ζ * dir j := by
  rw [dir_add, show dir 1 = ζ from pow_one ζ, mul_comm]

/-- The right centre seen from the left centre is the direction `ζʲ`. -/
theorem proj_add_basis_sub (n : Label) (j : Fin 5) : proj (n + basis j) - proj n = dir j := by
  rw [map_add, proj_basis, add_sub_cancel_left]

/-- **The turn of `a` in the moving frame.** When `a` acts, the left centre `P(n)` stays and the
new right centre `P(n + e_{j+1})` is the old one `P(n + e_j)` turned about `P(n)` by `ζ`, a fifth
of a turn counter-clockwise. -/
theorem proj_turn_genA (n : Label) (j : Fin 5) :
    proj (n + basis (j + 1)) - proj n = ζ * (proj (n + basis j) - proj n) := by
  rw [proj_add_basis_sub, proj_add_basis_sub, dir_add_one]

/-- **The turn of `b` in the moving frame.** When `b` acts, the right centre `P(n + e_j)` stays
and the new left centre `P(n + e_j - e_{j+1})` is the old one `P(n)` turned about `P(n + e_j)`
by `ζ`. -/
theorem proj_turn_genB (n : Label) (j : Fin 5) :
    proj (n + basis j - basis (j + 1)) - proj (n + basis j) =
      ζ * (proj n - proj (n + basis j)) := by
  simp only [map_add, map_sub, proj_basis, dir_add_one]
  ring

/-- The turn of `a⁻¹ = a⁴` in the moving frame: the left centre stays and the right centre turns
about it by `ζ⁴ = ζ⁻¹`, so the direction index goes down by one. -/
theorem proj_turn_genA_inv (n : Label) (j : Fin 5) :
    proj (n + basis (j - 1)) - proj n = ζ ^ 4 * (proj (n + basis j) - proj n) := by
  have h := dir_add_one_mul_zeta_pow_four (j - 1)
  rw [sub_add_cancel] at h
  rw [proj_add_basis_sub, proj_add_basis_sub, ← h, mul_comm]

/-- The turn of `b⁻¹ = b⁴` in the moving frame: the right centre stays and the left centre turns
about it by `ζ⁴`, to `P(n + e_j - e_{j-1})`. -/
theorem proj_turn_genB_inv (n : Label) (j : Fin 5) :
    proj (n + basis j - basis (j - 1)) - proj (n + basis j) =
      ζ ^ 4 * (proj n - proj (n + basis j)) := by
  have h := dir_add_one_mul_zeta_pow_four (j - 1)
  rw [sub_add_cancel] at h
  simp only [map_add, map_sub, proj_basis]
  linear_combination h

/-- **The turn of `a` in the halved frame.** When `a` acts, the halved point `(y + 1) / 2` turns
about the halved left centre `0` by `ζ⁴`, a fifth of a turn clockwise. -/
theorem halved_genA {y : ℂ} (hy : y ∈ closedBall leftCenter r) :
    (TDCSG.genA 5 r y + 1) / 2 = ζ ^ 4 * ((y + 1) / 2) := by
  rw [TDCSG.genA, diskRotation_of_mem hy, rotation, leftCenter, Nat.cast_ofNat,
    exp_rotationAngle_five]
  ring

/-- **The turn of `b` in the halved frame.** When `b` acts, the halved point `(y + 1) / 2` turns
about the halved right centre `1` by `ζ⁴`. -/
theorem halved_genB {y : ℂ} (hy : y ∈ closedBall rightCenter r) :
    (TDCSG.genB 5 r y + 1) / 2 - 1 = ζ ^ 4 * ((y + 1) / 2 - 1) := by
  rw [TDCSG.genB, diskRotation_of_mem hy, rotation, rightCenter, Nat.cast_ofNat,
    exp_rotationAngle_five]
  ring

/-- The point lies in a disk exactly when the centre that its frame equation pairs with that disk
lies in the window: `2 (x - P(n)) = ζʲ (y - p)` makes `|y - p| = 2 |P(n) - x|`. -/
theorem mem_closedBall_iff_inWindow {y p : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y - p)) : y ∈ closedBall p r ↔ InWindow r x n := by
  have e := congrArg norm h
  rw [norm_mul, norm_mul, norm_dir, one_mul, norm_sub_rev x, Complex.norm_ofNat] at e
  rw [mem_closedBall, dist_eq_norm, InWindow]
  constructor <;> intro <;> linarith

/-- The rigid motion `T(w) = P(n) + ζʲ w` from the halved starting frame to the moving frame of
the state with label `n` and direction index `j`. -/
noncomputable def frameMap (n : Label) (j : Fin 5) (w : ℂ) : ℂ :=
  proj n + dir j * w

/-- `T` sends the halved left centre `0` to the left centre `P(n)`. -/
@[simp] theorem frameMap_zero (n : Label) (j : Fin 5) : frameMap n j 0 = proj n := by
  simp [frameMap]

/-- `T` sends the halved right centre `1` to the right centre `P(n + e_j)`. -/
@[simp] theorem frameMap_one (n : Label) (j : Fin 5) : frameMap n j 1 = proj (n + basis j) := by
  simp [frameMap]

/-- `T` sends the halved point `(y + 1) / 2` to the window centre `x`, for a framed state. -/
theorem frameMap_apply_halved {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) : frameMap n j ((y + 1) / 2) = x := by
  rw [frameMap]
  linear_combination -h / 2

/-- `T` preserves distances: it is a rotation followed by a translation, with no reflection. -/
@[simp] theorem dist_frameMap (n : Label) (j : Fin 5) (w w' : ℂ) :
    dist (frameMap n j w) (frameMap n j w') = dist w w' := by
  simp [frameMap, dist_eq_norm, ← mul_sub]

/-- After `a` acts, the motion of the new state undoes the turn of the halved frame:
`T'(ζ⁴ w) = T(w)` for `T' = frameMap n (j + 1)`. So the window centre `x` and the left centre stay
where they are while the halved picture turns. -/
theorem frameMap_genA (n : Label) (j : Fin 5) (w : ℂ) :
    frameMap n (j + 1) (ζ ^ 4 * w) = frameMap n j w := by
  rw [frameMap, frameMap, ← dir_add_one_mul_zeta_pow_four j]
  ring

/-- After `b` acts, the motion of the new state undoes the turn of the halved frame about `1`:
`T'(1 + ζ⁴ (w - 1)) = T(w)` for `T' = frameMap (n + e_j - e_{j+1}) (j + 1)`. So the window centre
`x` and the right centre stay where they are. -/
theorem frameMap_genB (n : Label) (j : Fin 5) (w : ℂ) :
    frameMap (n + basis j - basis (j + 1)) (j + 1) (1 + ζ ^ 4 * (w - 1)) = frameMap n j w := by
  have h := dir_add_one_mul_zeta_pow_four j
  simp only [frameMap, map_add, map_sub, proj_basis]
  linear_combination (w - 1) * h

end TDCSG.Five

end
