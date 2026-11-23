/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Bounded return times of dense cyclic subgroups

In a compact additive topological group whose element `a` has dense multiples, every translate
`y` returns to a fixed nonempty open set under a multiple `i • a` with `|i|` uniformly bounded:
the open sets `-(i • a) + U` cover the group, and finitely many of them suffice.

For an irrational rotation `y ↦ α + y` of the circle `ℝ / L ℤ` this says that every orbit
enters the neighbourhood `{y | L / 2 - η < ‖y‖}` of the half period within a fixed number of
steps, forwards or backwards.

## Main statements

* `DenseRange.exists_natAbs_le_zsmul_add_mem`: bounded return times to a nonempty open set.
* `Irrational.exists_abs_le_lt_norm_zsmul_add`: the version for an irrational rotation of
  `ℝ / L ℤ` and a neighbourhood of the half period.
-/

@[expose] public section

/-- In a compact additive group, if the multiples of `a` are dense, then for every nonempty open
set `U` there is a bound `K` such that every `y` has a translate `i • a + y ∈ U` with
`|i| ≤ K`. -/
theorem DenseRange.exists_natAbs_le_zsmul_add_mem {G : Type*} [AddGroup G] [TopologicalSpace G]
    [ContinuousAdd G] [CompactSpace G] {a : G} (ha : DenseRange fun i : ℤ ↦ i • a)
    {U : Set G} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ K : ℕ, ∀ y : G, ∃ i : ℤ, i.natAbs ≤ K ∧ i • a + y ∈ U := by
  let V (i : ℤ) : Set G := (fun y ↦ i • a + y) ⁻¹' U
  have hV (i : ℤ) : IsOpen (V i) := hU.preimage (continuous_const.add continuous_id)
  have hcov : Set.univ ⊆ ⋃ i, V i := fun y _ ↦ by
    obtain ⟨u, hu⟩ := hne
    obtain ⟨i, hi⟩ := ha.exists_mem_open (s := (· + y) ⁻¹' U)
      (hU.preimage (continuous_id.add continuous_const)) ⟨u - y, by simpa using hu⟩
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV hcov
  refine ⟨s.sup Int.natAbs, fun y ↦ ?_⟩
  obtain ⟨i, his, hi⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  exact ⟨i, Finset.le_sup (f := Int.natAbs) his, hi⟩

/-- For an irrational rotation number `α / L` and every `η > 0` there is a bound `K` such that
every point `y` of `ℝ / L ℤ` has a translate `i • α + y` with `|i| ≤ K` whose norm, its distance
from `0`, exceeds `L / 2 - η`. -/
theorem Irrational.exists_abs_le_lt_norm_zsmul_add {L η α : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hirr : Irrational (α / L)) :
    ∃ K : ℕ, ∀ y : AddCircle L, ∃ i : ℤ, |i| ≤ K ∧ L / 2 - η < ‖i • (α : AddCircle L) + y‖ := by
  have : Fact (0 < L) := ⟨hL⟩
  have hne : {y : AddCircle L | L / 2 - η < ‖y‖}.Nonempty := ⟨((L / 2 : ℝ) : AddCircle L), by
    simp only [Set.mem_ofPred_eq, AddCircle.norm_half_period_eq, abs_of_pos hL]
    linarith⟩
  obtain ⟨K, hK⟩ := (AddCircle.denseRange_zsmul_coe_iff.2 hirr).exists_natAbs_le_zsmul_add_mem
    (isOpen_lt continuous_const continuous_norm) hne
  refine ⟨K, fun y ↦ ?_⟩
  obtain ⟨i, hiK, hi⟩ := hK y
  exact ⟨i, by rw [← Int.natCast_natAbs]; exact_mod_cast hiK, hi⟩
