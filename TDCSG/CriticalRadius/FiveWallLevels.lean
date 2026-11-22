/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Tactic

/-! # Pairs of uniformly bounded cuts for an irrational rotation -/

@[expose] public section

namespace TDCSG.Five.Walls

/-- At two bounded levels on opposite sides of the origin, every representative of the
phase is close to or beyond half the period in absolute value. -/
theorem exists_levels {L η α : ℝ} (hL : 0 < L) (hη : 0 < η) (hirr : Irrational (α / L)) :
    ∃ N : ℕ, ∀ b : ℝ, ∃ lo hi : ℤ, -(N : ℤ) ≤ lo ∧ lo < -2 ∧ 2 < hi ∧ hi ≤ N ∧
      ∀ m : ℤ, (m = lo ∨ m = hi) → ∀ p : ℤ, L / 2 - η < |α * m + b + L * p| := by
  classical
  let _ : Fact (0 < L) := ⟨hL⟩
  let a : AddCircle L := α
  let U (i : ℤ) := {y : AddCircle L | L / 2 - η < ‖i • a + y‖}
  have hU (i : ℤ) : IsOpen (U i) := isOpen_lt continuous_const (by fun_prop)
  have hd : DenseRange (fun i : ℤ ↦ i • a) := AddCircle.denseRange_zsmul_coe_iff.mpr hirr
  have hcov : Set.univ ⊆ ⋃ i, U i := by
    intro y _
    obtain ⟨i, hi⟩ := hd.exists_dist_lt (((L / 2 : ℝ) : AddCircle L) - y) hη
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change L / 2 - η < ‖i • a + y‖
    have hnear : dist (((L / 2 : ℝ) : AddCircle L)) (i • a + y) < η := by
      rw [← dist_add_right _ _ y, sub_add_cancel] at hi
      exact hi
    have htriangle := norm_sub_norm_le (((L / 2 : ℝ) : AddCircle L)) (i • a + y)
    rw [← dist_eq_norm, AddCircle.norm_half_period_eq, abs_of_pos hL] at htriangle
    linarith
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  let K := s.sup Int.natAbs
  have hhit (b : ℝ) (z : ℤ) : ∃ i : ℤ, i.natAbs ≤ K ∧
      ∀ p : ℤ, L / 2 - η < |α * (z + i) + b + L * p| := by
    have hy := hs (Set.mem_univ (z • a + (b : AddCircle L)))
    obtain ⟨i, hiy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨his, hi⟩ := Set.mem_iUnion.mp hiy
    refine ⟨i, Finset.le_sup (f := Int.natAbs) his, fun p ↦ ?_⟩
    change L / 2 - η < ‖i • a + (z • a + (b : AddCircle L))‖ at hi
    let w := α * ((z : ℝ) + i) + b + L * p
    have hw : (w : AddCircle L) = i • a + (z • a + (b : AddCircle L)) := by
      dsimp [w, a]
      rw [mul_add, mul_comm α (z : ℝ), mul_comm α (i : ℝ), mul_comm L (p : ℝ)]
      simp only [← zsmul_eq_mul, AddCircle.coe_add, AddCircle.coe_zsmul,
        AddCircle.coe_period, smul_zero, add_zero]
      abel
    have hnorm : ‖(w : AddCircle L)‖ ≤ |w| := QuotientAddGroup.norm_mk_le_norm
    exact hi.trans_le (hw ▸ hnorm)
  refine ⟨2 * K + 3, fun b ↦ ?_⟩
  obtain ⟨i, hi, hlow⟩ := hhit b (-(K : ℤ) - 3)
  obtain ⟨j, hj, hhigh⟩ := hhit b ((K : ℤ) + 3)
  have hi' : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
  have hj' : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have hni : -i ≤ (i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -i))
  have hnj : -j ≤ (j.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -j))
  refine ⟨-(K : ℤ) - 3 + i, (K : ℤ) + 3 + j, by omega, by omega, by omega, by omega, ?_⟩
  rintro m (rfl | rfl) p
  · simpa using hlow p
  · simpa using hhigh p

end TDCSG.Five.Walls
