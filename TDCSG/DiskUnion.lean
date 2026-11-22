/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.Group

/-! # The bounded support of the two-disk action -/

@[expose] public section

open Complex Metric Equiv

namespace TDCSG

/-- Every element of the group fixes each point outside the two disks. -/
theorem apply_eq_of_notMem_diskUnion {n₁ n₂ : ℕ} {r₁ r₂ : ℝ} {g : Perm ℂ}
    (hg : g ∈ GG n₁ n₂ r₁ r₂) {z : ℂ} (hz : z ∉ diskUnion r₁ r₂) : g z = z :=
  apply_eq_of_notMem_ballUnion hg (by rwa [ballUnion_eq_diskUnion])

/-- Every element of the group maps the union of the two disks into itself. -/
theorem apply_mem_diskUnion {n₁ n₂ : ℕ} {r₁ r₂ : ℝ} {g : Perm ℂ} (hg : g ∈ GG n₁ n₂ r₁ r₂)
    {z : ℂ} (hz : z ∈ diskUnion r₁ r₂) : g z ∈ diskUnion r₁ r₂ := by
  rw [← ballUnion_eq_diskUnion] at hz ⊢
  exact (apply_mem_ballUnion_iff hg z).2 hz

/-- Points of the two disks have norm at most `1 + max r₁ r₂`. -/
theorem norm_le_of_mem_diskUnion {r₁ r₂ : ℝ} {z : ℂ} (hz : z ∈ diskUnion r₁ r₂) :
    ‖z‖ ≤ 1 + max r₁ r₂ := by
  rcases hz with hz | hz
  · rw [leftDisk, mem_closedBall, dist_eq_norm, leftCenter, sub_neg_eq_add] at hz
    have := norm_sub_le (z + 1) 1
    simp only [add_sub_cancel_right, norm_one] at this
    linarith [le_max_left r₁ r₂]
  · rw [rightDisk, mem_closedBall, dist_eq_norm, rightCenter] at hz
    have := norm_add_le (z - 1) 1
    simp only [sub_add_cancel, norm_one] at this
    linarith [le_max_right r₁ r₂]

end TDCSG
