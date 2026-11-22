/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import TDCSG.Compound.Basic

/-!
# Staging: the general theorems about compound symmetry groups, as targets

This staging file lists, as propositions, the general theorems to be proved about
`TDCSG.compoundSymmetryGroup`. Each target is replaced by a theorem of the same content in
`TDCSG.Compound.Basic`, after which this file is removed.
-/

@[expose] public section

open Equiv Function Metric Set

namespace TDCSG.Targets

variable {X ι : Type*} [PseudoMetricSpace X] (c : ι → X) (r : ι → ℝ)
  (H : ∀ i, Subgroup (closedBall (c i) (r i) ≃ᵢ closedBall (c i) (r i)))

/-- The extension of ball isometries is injective. -/
def BallPermInjective (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (c : X) (r : ℝ), Injective (ballPerm c r)

/-- On its ball the extension acts as the isometry. -/
def BallPermApplyOfMem (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (c : X) (r : ℝ) (h : closedBall c r ≃ᵢ closedBall c r) (x : X) (hx : x ∈ closedBall c r),
    ballPerm c r h x = h ⟨x, hx⟩

/-- Off its ball the extension is the identity. -/
def BallPermApplyOfNotMem (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (c : X) (r : ℝ) (h : closedBall c r ≃ᵢ closedBall c r) (x : X), x ∉ closedBall c r →
    ballPerm c r h x = x

/-- Balls of negative radius contribute only the identity. -/
def BallPermEqOneOfNeg (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (c : X) (r : ℝ), r < 0 → ∀ h : closedBall c r ≃ᵢ closedBall c r, ballPerm c r h = 1

/-- The compound symmetry group is monotone in the groups `H i`. -/
def Mono : Prop :=
  ∀ H' : ∀ i, Subgroup (closedBall (c i) (r i) ≃ᵢ closedBall (c i) (r i)),
    (∀ i, H i ≤ H' i) → compoundSymmetryGroup c r H ≤ compoundSymmetryGroup c r H'

/-- Generators of the groups `H i` give generators of the compound symmetry group. -/
def EqClosureOfEqClosure : Prop :=
  ∀ (S : ∀ i, Set (closedBall (c i) (r i) ≃ᵢ closedBall (c i) (r i))),
    (∀ i, H i = Subgroup.closure (S i)) →
      compoundSymmetryGroup c r H = Subgroup.closure (⋃ i, ballPerm (c i) (r i) '' S i)

/-- Every element fixes each point outside the union of the balls. -/
def ApplyEqOfNotMemBallUnion : Prop :=
  ∀ (g : Perm X), g ∈ compoundSymmetryGroup c r H → ∀ x ∉ ballUnion c r, g x = x

/-- Every element maps the union of the balls onto itself. -/
def ImageBallUnion : Prop :=
  ∀ (g : Perm X), g ∈ compoundSymmetryGroup c r H → g '' ballUnion c r = ballUnion c r

/-- Orbits lie in the union of the balls together with the base point. -/
def OrbitSubset : Prop :=
  ∀ x : X, MulAction.orbit (compoundSymmetryGroup c r H) x ⊆ insert x (ballUnion c r)

/-- For finitely many pairwise disjoint balls the compound symmetry group is the product of the
groups `H i`. -/
def NonemptyMulEquivPi : Prop :=
  Finite ι → Pairwise (Disjoint on fun i ↦ closedBall (c i) (r i)) →
      Nonempty (compoundSymmetryGroup c r H ≃* ∀ i, H i)

/-- A finitely generated compound symmetry group with uniformly bounded orbits is finite. -/
def FiniteOfEncardOrbitLe : Prop :=
  Group.FG (compoundSymmetryGroup c r H) → ∀ N : ℕ,
    (∀ x : X, (MulAction.orbit (compoundSymmetryGroup c r H) x).encard ≤ N) →
      Finite (compoundSymmetryGroup c r H)

/-- Finitely many balls with finitely generated groups give a finitely generated group. -/
def FG : Prop :=
  Finite ι → (∀ i, Group.FG (H i)) → Group.FG (compoundSymmetryGroup c r H)

/-- Monotonicity in the balls: if each generator of each `H i` agrees on its ball with an
element of a group `G'`, then orbits under the compound symmetry group lie in orbits under
`G'`. -/
def OrbitSubsetOrbit : Prop :=
  ∀ (S : ∀ i, Set (closedBall (c i) (r i) ≃ᵢ closedBall (c i) (r i))) (G' : Subgroup (Perm X)),
    (∀ i, H i = Subgroup.closure (S i)) →
    (∀ i, ∀ s ∈ S i, ∃ g ∈ G', EqOn (ballPerm (c i) (r i) s) g (closedBall (c i) (r i))) →
      ∀ x : X, MulAction.orbit (compoundSymmetryGroup c r H) x ⊆ MulAction.orbit G' x

end TDCSG.Targets

end
