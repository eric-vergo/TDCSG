/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
module

public import TDCSG.CriticalRadius.Five.Levels
public import TDCSG.DiskUnion
public import TDCSG.ForMathlib.SimpleGraph

/-!
# Confinement: `GG₅(r)` is finite for every `r < √(3 + φ)`

This is §4 of `notes/proofs/sharp-lower-bound-n5-pentagrid.md`. In each coordinate `j`, choose
good levels `lo < -2` and `hi > 2` with `|lo|, |hi|` bounded uniformly in the window centre. The
labels strictly above `lo` and at most `hi` contain the starting labels `0`, `e₀` and their
neighbours, and every edge leaving them crosses a good level, so it has a leaf end. A walk from
`0` or `e₀` therefore stays within one step of this slab. Hence the labels reachable in the
centre graph lie in a box independent of the starting point, and by the correspondence between
words and walks every orbit consists of its base point and the images of one finite set.

## Main statements

* `TDCSG.Five.abs_sub_le_one_of_adj`: adjacent labels differ by at most one in each coordinate.
* `TDCSG.Five.leaf_of_crossing`: an edge that crosses a good level has a leaf end.
* `TDCSG.Five.exists_abs_le_of_centerReach`: below the critical radius, the reachable labels lie
  in a box independent of the window centre.
* `TDCSG.Five.finite_GG_of_lt`: below the critical radius, `GG 5 5 r r` is finite.
-/

@[expose] public section

open Complex Metric
open scoped goldenRatio

namespace TDCSG.Five

open Label

variable {r : ℝ} {x : ℂ}

/-- Adjacent labels differ by at most one in every coordinate. -/
theorem abs_sub_le_one_of_adj {a b : Label} (h : (centerGraph r x).Adj a b) (j : Fin 5) :
    |b j - a j| ≤ 1 := by
  rw [abs_le]
  rcases centerGraph_adj.1 h with ⟨-, ⟨k, rfl⟩, -⟩ | ⟨-, ⟨k, rfl⟩, -⟩ <;>
    simp only [Pi.add_apply, basis_apply] <;> split_ifs <;> omega

/-- The edge from a sum-zero label `n` to `n + e_j` at a good level `n_j` has a leaf end: `n + e_j`
is the only neighbour of `n`, or `n` is the only neighbour of `n + e_j`. -/
theorem leaf_of_isGoodLevel (hr : 0 ≤ r) (hc : r < √(3 + φ)) {n : Label} {j : Fin 5}
    (he : CenterEdge r x n (n + basis j)) (hm : IsGoodLevel r x j (n j)) :
    (∀ w, (centerGraph r x).Adj n w → w = n + basis j) ∨
      (∀ w, (centerGraph r x).Adj (n + basis j) w → w = n) := by
  obtain ⟨h0, -, hlo, hhi⟩ := he
  rcases hm.leaf hr hc h0 rfl hlo hhi with hl | hl
  · left
    intro w hw
    rcases centerGraph_adj.1 hw with ⟨-, ⟨k, rfl⟩, -, hwk⟩ | ⟨hw0, ⟨k, e⟩, -⟩
    · by_contra hne
      exact hl k (fun hkj ↦ hne (by rw [hkj])) hwk
    · have := congrArg weight e
      simp [h0, hw0] at this
  · right
    intro w hw
    rcases centerGraph_adj.1 hw with ⟨hw0, -⟩ | ⟨-, ⟨k, e⟩, hwin, -⟩
    · simp [h0] at hw0
    · have hwe : w = n + basis j - basis k := by rw [e, add_sub_cancel_right]
      by_contra hne
      exact hl k (fun hkj ↦ hne (by rw [hwe, hkj, add_sub_cancel_right])) (hwe ▸ hwin)

/-- If exactly one of `n` and `n + e_k` lies in the slab `lo < m_j ≤ hi`, then `k = j` and
`n_j` is `lo` or `hi`. So if both of these levels are good, so is `n_j`. -/
theorem isGoodLevel_of_crossing {j k : Fin 5} {lo hi : ℤ} (hlo : IsGoodLevel r x j lo)
    (hhi : IsGoodLevel r x j hi) {n : Label}
    (h : (lo < n j ∧ n j ≤ hi) ↔ ¬(lo < (n + basis k) j ∧ (n + basis k) j ≤ hi)) :
    k = j ∧ IsGoodLevel r x j (n j) := by
  simp only [Pi.add_apply, basis_apply] at h
  split_ifs at h with hjk
  · refine ⟨hjk.symm, ?_⟩
    obtain hn | hn : n j = hi ∨ n j = lo := by omega
    exacts [hn ▸ hhi, hn ▸ hlo]
  · rw [add_zero] at h
    exact (iff_not_self h).elim

/-- **A crossing edge has a leaf end.** Let `lo` and `hi` be good levels of coordinate `j`. An
edge from a label `a` with `lo < a_j ≤ hi` to a label `b` outside this slab has a leaf end. -/
theorem leaf_of_crossing (hr : 0 ≤ r) (hc : r < √(3 + φ)) {j : Fin 5} {lo hi : ℤ}
    (hlo : IsGoodLevel r x j lo) (hhi : IsGoodLevel r x j hi) {a b : Label}
    (ha : lo < a j ∧ a j ≤ hi) (hb : ¬(lo < b j ∧ b j ≤ hi)) (hab : (centerGraph r x).Adj a b) :
    (∀ w, (centerGraph r x).Adj a w → w = b) ∨ (∀ w, (centerGraph r x).Adj b w → w = a) := by
  rcases centerGraph_adj.1 hab with he | he
  · obtain ⟨k, rfl⟩ := he.2.1
    obtain ⟨rfl, hm⟩ := isGoodLevel_of_crossing hlo hhi (iff_of_true ha hb)
    exact leaf_of_isGoodLevel hr hc he hm
  · obtain ⟨k, rfl⟩ := he.2.1
    obtain ⟨rfl, hm⟩ := isGoodLevel_of_crossing hlo hhi (iff_of_false hb (not_not_intro ha))
    exact (leaf_of_isGoodLevel hr hc he hm).symm

/-- **Paths stay in a box.** Below the critical radius there is a bound `N` such that, for every
window centre `x`, every label reachable in the centre graph has coordinates of absolute value
at most `N`. -/
theorem exists_abs_le_of_centerReach (hr : 0 ≤ r) (hc : r < √(3 + φ)) :
    ∃ N : ℕ, ∀ (x : ℂ) (n : Label), CenterReach r x n → ∀ j, |n j| ≤ N := by
  obtain ⟨K, hK⟩ := exists_isGoodLevel hr hc
  refine ⟨2 * K + 4, fun x n ⟨s, hs, hp⟩ j ↦ ?_⟩
  obtain ⟨i, hi, hlo⟩ := hK x j (-K - 3)
  obtain ⟨i', hi', hhi⟩ := hK x j (K + 3)
  rw [abs_le] at hi hi'
  have hsj : 0 ≤ s j ∧ s j ≤ 1 := by
    rcases hs with rfl | rfl
    · simp
    · rw [basis_apply]
      split_ifs <;> simp
  let S : Set Label := {v | -K - 3 + i < v j ∧ v j ≤ K + 3 + i'}
  have hstart : (centerGraph r x).neighborSet s ⊆ S := fun y he ↦ by
    have := abs_le.1 (abs_sub_le_one_of_adj he j)
    simp only [S, Set.mem_ofPred_eq]
    omega
  have hs' : s ∈ S := by
    simp only [S, Set.mem_ofPred_eq]
    omega
  rw [abs_le]
  push_cast
  rcases hp.mem_or_exists_adj_of_leaf hs' hstart
      (fun a b ha hb hab ↦ leaf_of_crossing hr hc hlo hhi ha hb hab) with hn | ⟨v, hv, he⟩
  · simp only [S, Set.mem_ofPred_eq] at hn
    omega
  · have := abs_le.1 (abs_sub_le_one_of_adj he j)
    simp only [S, Set.mem_ofPred_eq] at hv
    omega

/-- **Finiteness below the threshold.** For every `r < √(3 + φ)` the group `GG 5 5 r r` is
finite. -/
theorem finite_GG_of_lt (hc : r < √(3 + φ)) : Finite (GG 5 5 r r) := by
  rcases lt_or_ge r 0 with hr | hr
  · exact finite_GG_of_lt_one 5 (by linarith)
  obtain ⟨N, hN⟩ := exists_abs_le_of_centerReach hr hc
  let box : Set Label := Set.pi Set.univ fun _ ↦ Set.Icc (-(N : ℤ)) N
  let T : Set (ℂ × Fin 5 × Label) := ({leftCenter, rightCenter} : Set ℂ) ×ˢ Set.univ ×ˢ box
  have hT : T.Finite := ((Set.finite_singleton _).insert _).prod
    (Set.finite_univ.prod (Set.Finite.pi fun _ ↦ Set.finite_Icc _ _))
  refine finite_of_orbit_subset_insert_image hT
    (fun z q ↦ q.1 + 2 * ((z + 1) / 2 - proj q.2.2) / dir q.2.1) fun z ↦ ?_
  rintro y ⟨g, hg, rfl⟩
  by_cases hz : z ∈ diskUnion r r
  · obtain ⟨c, hc', j, n, hn, hy⟩ :=
      exists_centerReach_of_mem_orbit ⟨g, hg, rfl⟩ (apply_mem_diskUnion hg hz)
    exact .inr ⟨(c, j, n), ⟨hc', Set.mem_univ _, fun k _ ↦ abs_le.1 (hN _ n hn k)⟩, hy.symm⟩
  · exact .inl (apply_eq_of_notMem_diskUnion hg hz)

end TDCSG.Five

end
