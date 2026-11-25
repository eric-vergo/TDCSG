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
* `TDCSG.Five.frameMap n j`: the rigid motion `w ↦ P(n) + ζʲ w` from the halved starting frame to
  the moving frame of the label `n` and the direction `j`, and `TDCSG.Five.FramePicture`: it
  sends `0`, `1` and the halved point to the left centre, the right centre and `x`.

## Main statements

* `TDCSG.Five.framed_of_mem_orbit`: every point of the orbit of `z` is framed.
* `TDCSG.Five.exists_centerReach_of_mem_orbit`: every point of the orbit of `z` inside the two
  disks is `c + 2 (x - P(n)) / ζʲ` for a centre `c = ∓1`, a direction `j` and a label `n`
  reachable in the centre graph (Lemma 1 of the written proof).
* `TDCSG.Five.two_mul_sub_proj_genA`, `TDCSG.Five.two_mul_sub_proj_genB` and their forms for a
  letter that does not act and for the inverse letters: how a letter updates the frame.
* `TDCSG.Five.framePicture_genA_genB`, `TDCSG.Five.framePicture_symm`: before and after any
  letter, the moving-frame picture is the halved picture moved rigidly by `frameMap`.
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

/-- The point lies in a disk exactly when the centre that its frame equation pairs with that disk
lies in the window: `2 (x - P(n)) = ζʲ (y - p)` makes `|y - p| = 2 |P(n) - x|`. -/
theorem mem_closedBall_iff_inWindow {y p : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y - p)) : y ∈ closedBall p r ↔ InWindow r x n := by
  have e := congrArg norm h
  rw [norm_mul, norm_mul, norm_dir, one_mul, norm_sub_rev x, Complex.norm_ofNat] at e
  rw [mem_closedBall, dist_eq_norm, InWindow]
  constructor <;> intro <;> linarith

/-- A centre whose frame puts the current point in its disk lies in the window. -/
theorem inWindow_of_two_mul_sub_proj {y p : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y - p)) (hy : y ∈ closedBall p r) : InWindow r x n :=
  (mem_closedBall_iff_inWindow h).1 hy

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
rigid motion `frameMap n j` carries the first picture onto the second (`FramePicture`). After a
letter the picture of the updated frame is again the halved picture moved rigidly
(`framePicture_genA_genB`, `framePicture_symm`): when `a` acts the left centre stays and the
right centre turns about it by `ζ`, when `b` acts the right centre stays and the left centre
turns about it by `ζ`, and a letter that does not act changes neither the point nor the frame. -/

/-! #### Label identities -/

/-- `ζʲ⁺¹ = ζ ζʲ`. -/
theorem dir_add_one (j : Fin 5) : dir (j + 1) = ζ * dir j := by
  rw [dir_add, show dir 1 = ζ from pow_one ζ, mul_comm]

/-- The centre labelled `n + e_j` seen from the centre labelled `n` is the direction `ζʲ`. -/
theorem proj_add_basis_sub (n : Label) (j : Fin 5) : proj (n + basis j) - proj n = dir j := by
  rw [map_add, proj_basis, add_sub_cancel_left]

/-- A label identity: `P(n + e_{j+1})` is `P(n + e_j)` turned about `P(n)` by `ζ`. It is the turn
of the right centre when `a` acts (`two_mul_sub_proj_genA`). -/
theorem proj_add_basis_succ_sub (n : Label) (j : Fin 5) :
    proj (n + basis (j + 1)) - proj n = ζ * (proj (n + basis j) - proj n) := by
  rw [proj_add_basis_sub, proj_add_basis_sub, dir_add_one]

/-- A label identity: `P(n + e_j - e_{j+1})` is `P(n)` turned about `P(n + e_j)` by `ζ`. It is the
turn of the left centre when `b` acts (`two_mul_sub_proj_genB`). -/
theorem proj_add_basis_sub_basis_succ_sub (n : Label) (j : Fin 5) :
    proj (n + basis j - basis (j + 1)) - proj (n + basis j) =
      ζ * (proj n - proj (n + basis j)) := by
  simp only [map_add, map_sub, proj_basis, dir_add_one]
  ring

/-- A label identity: `P(n + e_{j-1})` is `P(n + e_j)` turned about `P(n)` by `ζ⁴ = ζ⁻¹`. It is
the turn of the right centre when `a⁻¹` acts (`two_mul_sub_proj_permA_symm`). -/
theorem proj_add_basis_pred_sub (n : Label) (j : Fin 5) :
    proj (n + basis (j - 1)) - proj n = ζ ^ 4 * (proj (n + basis j) - proj n) := by
  have h := dir_add_one_mul_zeta_pow_four (j - 1)
  rw [sub_add_cancel] at h
  rw [proj_add_basis_sub, proj_add_basis_sub, ← h, mul_comm]

/-- A label identity: `P(n + e_j - e_{j-1})` is `P(n)` turned about `P(n + e_j)` by `ζ⁴`. It is
the turn of the left centre when `b⁻¹` acts (`two_mul_sub_proj_permB_symm`). -/
theorem proj_add_basis_sub_basis_pred_sub (n : Label) (j : Fin 5) :
    proj (n + basis j - basis (j - 1)) - proj (n + basis j) =
      ζ ^ 4 * (proj n - proj (n + basis j)) := by
  have h := dir_add_one_mul_zeta_pow_four (j - 1)
  rw [sub_add_cancel] at h
  simp only [map_add, map_sub, proj_basis]
  linear_combination h

/-! #### The generators and their inverses on a framed point -/

/-- **`a` acting, in the moving frame.** If `a` acts on a point framed by `(n, j)`, the image is
framed by `(n, j + 1)`: the left centre `P(n)` stays and the right centre turns about it by `ζ`
(`proj_add_basis_succ_sub`). -/
theorem two_mul_sub_proj_genA {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) (hy : y ∈ closedBall leftCenter r) :
    2 * (x - proj n) = dir (j + 1) * (TDCSG.genA 5 r y + 1) := by
  rw [TDCSG.genA, diskRotation_of_mem hy, rotation, leftCenter, Nat.cast_ofNat,
    exp_rotationAngle_five]
  linear_combination h - (y + 1) * dir_add_one_mul_zeta_pow_four j

/-- **`b` acting, in the moving frame.** If `b` acts on a point framed by `(n, j)`, the image is
framed by `(n + e_j - e_{j+1}, j + 1)`: the right centre `P(n + e_j)` stays and the left centre
turns about it by `ζ` (`proj_add_basis_sub_basis_succ_sub`). -/
theorem two_mul_sub_proj_genB {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) (hy : y ∈ closedBall rightCenter r) :
    2 * (x - proj (n + basis j - basis (j + 1))) = dir (j + 1) * (TDCSG.genB 5 r y + 1) := by
  have h' := two_mul_sub_proj_add_basis h
  rw [TDCSG.genB, diskRotation_of_mem hy, rotation, rightCenter, Nat.cast_ofNat,
    exp_rotationAngle_five, map_sub, proj_basis]
  linear_combination h' - (y - 1) * dir_add_one_mul_zeta_pow_four j

/-- **`a` not acting.** Outside the left disk `a` fixes the point, so the frame `(n, j)` stays. -/
theorem two_mul_sub_proj_genA_of_notMem {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) (hy : y ∉ closedBall leftCenter r) :
    TDCSG.genA 5 r y = y ∧ 2 * (x - proj n) = dir j * (TDCSG.genA 5 r y + 1) := by
  rw [TDCSG.genA, diskRotation_of_notMem hy]
  exact ⟨rfl, h⟩

/-- **`b` not acting.** Outside the right disk `b` fixes the point, so the frame `(n, j)`
stays. -/
theorem two_mul_sub_proj_genB_of_notMem {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) (hy : y ∉ closedBall rightCenter r) :
    TDCSG.genB 5 r y = y ∧ 2 * (x - proj n) = dir j * (TDCSG.genB 5 r y + 1) := by
  rw [TDCSG.genB, diskRotation_of_notMem hy]
  exact ⟨rfl, h⟩

/-- On the left disk, `a⁻¹` turns about `-1` by `ζ`, a fifth of a turn counter-clockwise. -/
theorem permA_symm_of_mem {y : ℂ} (hy : y ∈ closedBall leftCenter r) :
    (permA 5 r).symm y = leftCenter + ζ * (y - leftCenter) := by
  have hm : leftCenter + ζ * (y - leftCenter) ∈ closedBall leftCenter r := by
    rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_zeta, one_mul,
      ← dist_eq_norm, ← mem_closedBall]
  rw [Equiv.symm_apply_eq, permA_apply, TDCSG.genA, diskRotation_of_mem hm, rotation,
    Nat.cast_ofNat, exp_rotationAngle_five]
  linear_combination -(y - leftCenter) * zeta_pow_five

/-- Off the left disk, `a⁻¹` is the identity. -/
theorem permA_symm_of_notMem {y : ℂ} (hy : y ∉ closedBall leftCenter r) :
    (permA 5 r).symm y = y := by
  rw [Equiv.symm_apply_eq, permA_apply, TDCSG.genA, diskRotation_of_notMem hy]

/-- On the right disk, `b⁻¹` turns about `1` by `ζ`. -/
theorem permB_symm_of_mem {y : ℂ} (hy : y ∈ closedBall rightCenter r) :
    (permB 5 r).symm y = rightCenter + ζ * (y - rightCenter) := by
  have hm : rightCenter + ζ * (y - rightCenter) ∈ closedBall rightCenter r := by
    rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_zeta, one_mul,
      ← dist_eq_norm, ← mem_closedBall]
  rw [Equiv.symm_apply_eq, permB_apply, TDCSG.genB, diskRotation_of_mem hm, rotation,
    Nat.cast_ofNat, exp_rotationAngle_five]
  linear_combination -(y - rightCenter) * zeta_pow_five

/-- Off the right disk, `b⁻¹` is the identity. -/
theorem permB_symm_of_notMem {y : ℂ} (hy : y ∉ closedBall rightCenter r) :
    (permB 5 r).symm y = y := by
  rw [Equiv.symm_apply_eq, permB_apply, TDCSG.genB, diskRotation_of_notMem hy]

/-- **`a⁻¹` acting, in the moving frame.** If `a⁻¹` acts on a point framed by `(n, j)`, the image
is framed by `(n, j - 1)`: the left centre stays and the right centre turns about it by `ζ⁴`
(`proj_add_basis_pred_sub`). -/
theorem two_mul_sub_proj_permA_symm {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) (hy : y ∈ closedBall leftCenter r) :
    2 * (x - proj n) = dir (j - 1) * ((permA 5 r).symm y + 1) := by
  have e := dir_add_one_mul_zeta_pow_four (j - 1)
  rw [sub_add_cancel] at e
  rw [permA_symm_of_mem hy, leftCenter]
  linear_combination h + (y + 1) * ζ * e - (y + 1) * dir j * zeta_pow_five

/-- **`b⁻¹` acting, in the moving frame.** If `b⁻¹` acts on a point framed by `(n, j)`, the image
is framed by `(n + e_j - e_{j-1}, j - 1)`: the right centre stays and the left centre turns about
it by `ζ⁴` (`proj_add_basis_sub_basis_pred_sub`). -/
theorem two_mul_sub_proj_permB_symm {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) (hy : y ∈ closedBall rightCenter r) :
    2 * (x - proj (n + basis j - basis (j - 1))) = dir (j - 1) * ((permB 5 r).symm y + 1) := by
  have e := dir_add_one_mul_zeta_pow_four (j - 1)
  rw [sub_add_cancel] at e
  rw [permB_symm_of_mem hy, rightCenter]
  simp only [map_add, map_sub, proj_basis]
  linear_combination h + (y - 1) * ζ * e - (y - 1) * dir j * zeta_pow_five

/-! #### The halved frame -/

/-- **`a` acting, in the halved frame.** The halved point `(y + 1) / 2` turns about the halved
left centre `0` by `ζ⁴`, a fifth of a turn clockwise. -/
theorem halved_genA {y : ℂ} (hy : y ∈ closedBall leftCenter r) :
    (TDCSG.genA 5 r y + 1) / 2 = ζ ^ 4 * ((y + 1) / 2) := by
  rw [TDCSG.genA, diskRotation_of_mem hy, rotation, leftCenter, Nat.cast_ofNat,
    exp_rotationAngle_five]
  ring

/-- **`b` acting, in the halved frame.** The halved point `(y + 1) / 2` turns about the halved
right centre `1` by `ζ⁴`. -/
theorem halved_genB {y : ℂ} (hy : y ∈ closedBall rightCenter r) :
    (TDCSG.genB 5 r y + 1) / 2 - 1 = ζ ^ 4 * ((y + 1) / 2 - 1) := by
  rw [TDCSG.genB, diskRotation_of_mem hy, rotation, rightCenter, Nat.cast_ofNat,
    exp_rotationAngle_five]
  ring

/-- **`a⁻¹` acting, in the halved frame.** The halved point turns about `0` by `ζ`. -/
theorem halved_permA_symm {y : ℂ} (hy : y ∈ closedBall leftCenter r) :
    ((permA 5 r).symm y + 1) / 2 = ζ * ((y + 1) / 2) := by
  rw [permA_symm_of_mem hy, leftCenter]
  ring

/-- **`b⁻¹` acting, in the halved frame.** The halved point turns about `1` by `ζ`. -/
theorem halved_permB_symm {y : ℂ} (hy : y ∈ closedBall rightCenter r) :
    ((permB 5 r).symm y + 1) / 2 - 1 = ζ * ((y + 1) / 2 - 1) := by
  rw [permB_symm_of_mem hy, rightCenter]
  ring

/-! #### The rigid motion between the frames -/

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

/-- `T` preserves distances. -/
@[simp] theorem dist_frameMap (n : Label) (j : Fin 5) (w w' : ℂ) :
    dist (frameMap n j w) (frameMap n j w') = dist w w' := by
  simp [frameMap, dist_eq_norm, ← mul_sub]

/-- An identity of the motions: `frameMap n (j + 1)` after the turn of the plane by `ζ⁴` about `0`
is `frameMap n j`. -/
theorem frameMap_succ_zeta_pow_four_mul (n : Label) (j : Fin 5) (w : ℂ) :
    frameMap n (j + 1) (ζ ^ 4 * w) = frameMap n j w := by
  rw [frameMap, frameMap, ← dir_add_one_mul_zeta_pow_four j]
  ring

/-- An identity of the motions: `frameMap (n + e_j - e_{j+1}) (j + 1)` after the turn of the plane
by `ζ⁴` about `1` is `frameMap n j`. -/
theorem frameMap_add_basis_sub_basis_succ (n : Label) (j : Fin 5) (w : ℂ) :
    frameMap (n + basis j - basis (j + 1)) (j + 1) (1 + ζ ^ 4 * (w - 1)) = frameMap n j w := by
  have h := dir_add_one_mul_zeta_pow_four j
  simp only [frameMap, map_add, map_sub, proj_basis]
  linear_combination (w - 1) * h

/-- **`a` acting: the window centre stays fixed.** The motion of the updated frame sends the
turned halved point to `x`. -/
theorem frameMap_genA_halved {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) (hy : y ∈ closedBall leftCenter r) :
    frameMap n (j + 1) ((TDCSG.genA 5 r y + 1) / 2) = x :=
  frameMap_apply_halved (two_mul_sub_proj_genA h hy)

/-- **`b` acting: the window centre stays fixed.** The motion of the updated frame sends the
turned halved point to `x`. -/
theorem frameMap_genB_halved {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) (hy : y ∈ closedBall rightCenter r) :
    frameMap (n + basis j - basis (j + 1)) (j + 1) ((TDCSG.genB 5 r y + 1) / 2) = x :=
  frameMap_apply_halved (two_mul_sub_proj_genB h hy)

/-- The moving-frame picture of the frame `(n, j)` is the halved picture of the point `y` moved
by `frameMap n j`: the halved left centre `0`, the halved right centre `1` and the halved point
`(y + 1) / 2` go to the left centre `P(n)`, the right centre `P(n + e_j)` and the window centre
`x`. -/
def FramePicture (x y : ℂ) (n : Label) (j : Fin 5) : Prop :=
  frameMap n j 0 = proj n ∧ frameMap n j 1 = proj (n + basis j) ∧ frameMap n j ((y + 1) / 2) = x

/-- A frame equation makes the picture of its frame the halved picture moved rigidly. -/
theorem framePicture_of_two_mul_sub_proj {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) : FramePicture x y n j :=
  ⟨frameMap_zero n j, frameMap_one n j, frameMap_apply_halved h⟩

/-- **The two frames, before and after a generator.** For a point `y` framed by `(n, j)`, the
moving-frame picture is the halved picture moved by `frameMap n j`, and after `a` or `b` it is the
halved picture of the image moved by `frameMap` of the updated frame: `(n, j + 1)` when `a` acts,
`(n + e_j - e_{j+1}, j + 1)` when `b` acts, and `(n, j)`, with the point fixed, when the letter
does not act. -/
theorem framePicture_genA_genB {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) :
    FramePicture x y n j ∧
    (y ∈ closedBall leftCenter r → FramePicture x (TDCSG.genA 5 r y) n (j + 1)) ∧
    (y ∉ closedBall leftCenter r →
      TDCSG.genA 5 r y = y ∧ FramePicture x (TDCSG.genA 5 r y) n j) ∧
    (y ∈ closedBall rightCenter r →
      FramePicture x (TDCSG.genB 5 r y) (n + basis j - basis (j + 1)) (j + 1)) ∧
    (y ∉ closedBall rightCenter r →
      TDCSG.genB 5 r y = y ∧ FramePicture x (TDCSG.genB 5 r y) n j) :=
  ⟨framePicture_of_two_mul_sub_proj h,
    fun hy ↦ framePicture_of_two_mul_sub_proj (two_mul_sub_proj_genA h hy),
    fun hy ↦ have e := two_mul_sub_proj_genA_of_notMem h hy
      ⟨e.1, framePicture_of_two_mul_sub_proj e.2⟩,
    fun hy ↦ framePicture_of_two_mul_sub_proj (two_mul_sub_proj_genB h hy),
    fun hy ↦ have e := two_mul_sub_proj_genB_of_notMem h hy
      ⟨e.1, framePicture_of_two_mul_sub_proj e.2⟩⟩

/-- **The two frames, before and after an inverse generator.** For a point `y` framed by `(n, j)`,
after `a⁻¹` or `b⁻¹` the moving-frame picture is the halved picture of the image moved by
`frameMap` of the updated frame: `(n, j - 1)` when `a⁻¹` acts, `(n + e_j - e_{j-1}, j - 1)` when
`b⁻¹` acts, and `(n, j)`, with the point fixed, when the letter does not act. -/
theorem framePicture_symm {y : ℂ} {n : Label} {j : Fin 5}
    (h : 2 * (x - proj n) = dir j * (y + 1)) :
    (y ∈ closedBall leftCenter r → FramePicture x ((permA 5 r).symm y) n (j - 1)) ∧
    (y ∉ closedBall leftCenter r →
      (permA 5 r).symm y = y ∧ FramePicture x ((permA 5 r).symm y) n j) ∧
    (y ∈ closedBall rightCenter r →
      FramePicture x ((permB 5 r).symm y) (n + basis j - basis (j - 1)) (j - 1)) ∧
    (y ∉ closedBall rightCenter r →
      (permB 5 r).symm y = y ∧ FramePicture x ((permB 5 r).symm y) n j) :=
  ⟨fun hy ↦ framePicture_of_two_mul_sub_proj (two_mul_sub_proj_permA_symm h hy),
    fun hy ↦ ⟨permA_symm_of_notMem hy,
      framePicture_of_two_mul_sub_proj (by rw [permA_symm_of_notMem hy]; exact h)⟩,
    fun hy ↦ framePicture_of_two_mul_sub_proj (two_mul_sub_proj_permB_symm h hy),
    fun hy ↦ ⟨permB_symm_of_notMem hy,
      framePicture_of_two_mul_sub_proj (by rw [permB_symm_of_notMem hy]; exact h)⟩⟩

end TDCSG.Five

end
