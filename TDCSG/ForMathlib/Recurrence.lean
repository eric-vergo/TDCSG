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

For an irrational rotation of the circle `ℝ / L ℤ` this says that, along every run of a fixed
number of consecutive integers `m`, some phase `α m + b` is farther than `L / 2 - η` from every
point of `L ℤ`.

## Main statements

* `DenseRange.exists_natAbs_le_zsmul_add_mem`: bounded return times to a nonempty open set.
* `Irrational.exists_abs_le_forall_lt_abs_add_mul`: the version for an irrational rotation of
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
  classical
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

/-- For an irrational rotation number `α / L` and every `η > 0` there is a bound `K` such that,
for every offset `b` and every integer `z`, some `z + i` with `|i| ≤ K` puts the phase
`α (z + i) + b` farther than `L / 2 - η` from every point of `L ℤ`. -/
theorem Irrational.exists_abs_le_forall_lt_abs_add_mul {L η α : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hirr : Irrational (α / L)) :
    ∃ K : ℕ, ∀ (b : ℝ) (z : ℤ), ∃ i : ℤ, |i| ≤ K ∧
      ∀ p : ℤ, L / 2 - η < |α * (z + i) + b + L * p| := by
  have : Fact (0 < L) := ⟨hL⟩
  let U : Set (AddCircle L) := {y | L / 2 - η < ‖y‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hne : U.Nonempty := ⟨((L / 2 : ℝ) : AddCircle L), by
    simp only [U, Set.mem_ofPred_eq, AddCircle.norm_half_period_eq, abs_of_pos hL]
    linarith⟩
  obtain ⟨K, hK⟩ := (AddCircle.denseRange_zsmul_coe_iff.2 hirr).exists_natAbs_le_zsmul_add_mem
    hU hne
  refine ⟨K, fun b z ↦ ?_⟩
  obtain ⟨i, hiK, hi⟩ := hK ((z * α + b : ℝ) : AddCircle L)
  refine ⟨i, by rw [← Int.natCast_natAbs]; exact_mod_cast hiK, fun p ↦ hi.trans_le ?_⟩
  have hw : (((α * (z + i) + b + L * p : ℝ)) : AddCircle L) =
      i • (α : AddCircle L) + ((z * α + b : ℝ) : AddCircle L) := by
    rw [mul_comm L, ← zsmul_eq_mul, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, add_zero, ← AddCircle.coe_zsmul, ← AddCircle.coe_add, zsmul_eq_mul]
    congr 1
    ring
  rw [← hw]
  exact QuotientAddGroup.norm_mk_le_norm
