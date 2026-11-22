/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.FiveCenterPaths

/-! # Confinement of integer labels by cuts with terminal crossing edges -/

@[expose] public section

namespace TDCSG.Five.Walls

/-- A path starting inside a region with terminal crossing edges stays within one step of it. -/
private theorem confined {V : Type*} {E : V → V → Prop} (hsym : ∀ {a b}, E a b → E b a)
    (inside : V → Prop) {s v : V} (hs : inside s) (hstart : ∀ y, E s y → inside y)
    (hcross : ∀ a b, inside a → ¬inside b → E a b →
      (∀ w, E a w → w = b) ∨ (∀ w, E b w → w = a))
    (hp : Relation.ReflTransGen E s v) : inside v ∨ ∃ w, inside w ∧ E w v := by
  let anchored (a : V) := inside a ∧ (a = s ∨ ∃ b, inside b ∧ E b a)
  suffices h : anchored v ∨ ∃ a, anchored a ∧ E a v ∧ ∀ w, E v w → w = a by
    rcases h with h | ⟨a, ha, he, _⟩
    · exact .inl h.1
    · exact .inr ⟨a, ha.1, he⟩
  induction hp with
  | refl => exact .inl ⟨hs, .inl rfl⟩
  | @tail a b _ he ih =>
    rcases ih with ha | ⟨u, hu, _, hleaf⟩
    · by_cases hb : inside b
      · exact .inl ⟨hb, .inr ⟨a, ha.1, he⟩⟩
      · rcases hcross a b ha.1 hb he with hl | hl
        · exfalso
          rcases ha.2 with rfl | ⟨w, hw, hwa⟩
          · exact hb (hstart b he)
          · exact hb (hl w (hsym hwa) ▸ hw)
        · exact .inr ⟨a, ha, he, hl⟩
    · exact .inl (hleaf _ he ▸ hu)

private abbrev Adj (r : ℝ) (x : ℂ) (a b : Label) :=
  CenterEdge r x a b ∨ CenterEdge r x b a

private def terminal (r : ℝ) (x : ℂ) (a b : Label) : Prop :=
  ∀ w, Adj r x a w → w = b

private def AtWall (r : ℝ) (x : ℂ) (j : Fin 5) (m : ℤ) : Prop :=
  ∀ n : Label, weight n = 0 → n j = m → ‖proj n - x‖ ≤ r / 2 →
    ‖proj (n + basis j) - x‖ ≤ r / 2 →
    ((∀ k ≠ j, r / 2 < ‖proj (n + basis k) - x‖) ∨
      (∀ k ≠ j, r / 2 < ‖proj (n + basis j - basis k) - x‖))

private theorem weight_add_basis (n : Label) (k : Fin 5) :
    weight (n + basis k) = weight n + 1 := by
  classical
  simp [weight, basis, Pi.single_apply, Finset.sum_add_distrib]

private theorem directed_wall {r : ℝ} {x : ℂ} {j : Fin 5} {lo hi : ℤ}
    (hw : ∀ m, m = lo ∨ m = hi → AtWall r x j m) {a b : Label}
    (he : CenterEdge r x a b) (hm : ¬ ((lo < a j ∧ a j ≤ hi) ↔ (lo < b j ∧ b j ≤ hi))) :
    terminal r x a b ∨ terminal r x b a := by
  obtain ⟨h0, ⟨k, rfl⟩, hlow, hhigh⟩ := he
  by_cases hkj : j = k
  · subst k
    have hval : (a + basis j) j = a j + 1 := by simp [basis]
    have hcut : a j = lo ∨ a j = hi := by omega
    have h1 : weight (a + basis j) = 1 := by simp [weight_add_basis, h0]
    rcases hw (a j) hcut a h0 rfl hlow hhigh with hl | hl
    · left
      rintro w (⟨_, ⟨l, rfl⟩, _, hwl⟩ | ⟨hw0, ⟨l, e⟩, _, _⟩)
      · by_cases el : l = j
        · rw [el]
        · exact ((hl l el).not_ge hwl).elim
      · have := congrArg weight e
        rw [weight_add_basis, hw0, h0] at this
        omega
    · right
      rintro w (⟨hw0, _⟩ | ⟨_, ⟨l, e⟩, hwl, _⟩)
      · omega
      · have hwe : a + basis j - basis l = w := by rw [e, add_sub_cancel_right]
        by_cases el : l = j
        · simpa [el] using hwe.symm
        · exact ((hl l el).not_ge (hwe.symm ▸ hwl)).elim
  · have hval : (a + basis k) j = a j := by simp [basis, hkj]
    exact (hm (by rw [hval])).elim

private theorem adj_distance {r : ℝ} {x : ℂ} {a b : Label} (he : Adj r x a b) (j : Fin 5) :
    a j - 1 ≤ b j ∧ b j ≤ a j + 1 := by
  rcases he with ⟨_, ⟨k, rfl⟩, _⟩ | ⟨_, ⟨k, rfl⟩, _⟩ <;>
    by_cases h : k = j <;> simp [basis, Ne.symm, *] <;> omega

/-- Uniform bounding walls in the five coordinates bound all reachable center labels. -/
theorem centerBox_of_walls {r : ℝ}
    (hwalls : ∃ N : ℕ, ∀ x : ℂ, ‖x‖ ≤ 4 → ∀ j : Fin 5, ∃ lo hi : ℤ,
      -(N : ℤ) ≤ lo ∧ lo < -2 ∧ 2 < hi ∧ hi ≤ N ∧
      ∀ m : ℤ, (m = lo ∨ m = hi) → ∀ n : Label, weight n = 0 → n j = m →
      ‖proj n - x‖ ≤ r / 2 → ‖proj (n + basis j) - x‖ ≤ r / 2 →
      ((∀ k ≠ j, r / 2 < ‖proj (n + basis k) - x‖) ∨
        (∀ k ≠ j, r / 2 < ‖proj (n + basis j - basis k) - x‖))) : CenterBox r := by
  obtain ⟨N, hN⟩ := hwalls
  refine ⟨N + 1, fun x hx n ⟨s, hs, hp⟩ j ↦ ?_⟩
  obtain ⟨lo, hi, hNlo, hlo, hhi, hNhi, hw⟩ := hN x hx j
  let inside (v : Label) := lo < v j ∧ v j ≤ hi
  have hsj : 0 ≤ s j ∧ s j ≤ 1 := by
    rcases hs with rfl | rfl
    · simp
    · by_cases hj : j = 0 <;> simp [basis, *]
  have hstart (y : Label) (he : Adj r x s y) : inside y := by
    have hy := adj_distance he j
    dsimp [inside]
    omega
  have hcross (a b : Label) (ha : inside a) (hb : ¬inside b) (he : Adj r x a b) :
      terminal r x a b ∨ terminal r x b a := by
    rcases he with h | h
    · exact directed_wall hw h (fun e ↦ hb (e.mp ha))
    · exact (directed_wall hw h (fun e ↦ hb (e.mpr ha))).symm
  have hs' : inside s := by dsimp [inside]; omega
  rcases confined (E := Adj r x) (fun h ↦ h.symm) inside hs' hstart hcross hp with
    hn | ⟨v, hv, he⟩
  · dsimp [inside] at hn
    omega
  · have hd := adj_distance he j
    dsimp [inside] at hv
    omega

end TDCSG.Five.Walls
