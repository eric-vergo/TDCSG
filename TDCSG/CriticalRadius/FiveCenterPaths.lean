/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.FiveCenterModel

/-! # Paths of active disk centers in the fivefold integer model -/

@[expose] public section

namespace TDCSG.Five.Walls

/-- An edge between two retained centers, oriented from the sum-zero layer. -/
def CenterEdge (r : ℝ) (x : ℂ) (n m : Label) : Prop :=
  weight n = 0 ∧ (∃ j, m = n + basis j) ∧ ‖proj n - x‖ ≤ r / 2 ∧ ‖proj m - x‖ ≤ r / 2

/-- Centers reached from one of the two original disk centers by retained edges. -/
def CenterReach (r : ℝ) (x : ℂ) (n : Label) : Prop :=
  ∃ s : Label, (s = 0 ∨ s = basis 0) ∧
    Relation.ReflTransGen (fun v w ↦ CenterEdge r x v w ∨ CenterEdge r x w v) s n

/-- A uniform box for center labels reachable in bounded windows. -/
def CenterBox (r : ℝ) : Prop :=
  ∃ N : ℕ, ∀ x : ℂ, ‖x‖ ≤ 4 → ∀ n : Label, CenterReach r x n →
    ∀ j : Fin 5, -(N : ℤ) ≤ n j ∧ n j ≤ N

end TDCSG.Five.Walls
