/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finitely generated groups with uniformly bounded orbits

A finitely generated group acting faithfully on a set, with all orbits of size at most `N`, is
finite.

## Main statements

* `MonoidHom.finite_of_fg`: there are only finitely many homomorphisms from a finitely
  generated group to a finite monoid.
* `MulAction.finite_of_encard_orbit_le`: a finitely generated group acting faithfully with
  uniformly bounded orbits is finite.

## Implementation notes

Every orbit `G • x` of size `j ≤ N` gives, after numbering its points, a homomorphism
`G →* Equiv.Perm (Fin j)`. There are finitely many such homomorphisms, so the action map embeds
`G` into a finite product of finite symmetric groups. This is the embedding of `G` into a product
of finite symmetric groups that underlies the finite-index argument in the written proof
(`notes/proofs/theorem1-converse.md`, Proposition 4.2); it avoids free groups.
-/

@[expose] public section

/-- There are only finitely many homomorphisms from a finitely generated group to a finite
monoid. -/
theorem MonoidHom.finite_of_fg (G M : Type*) [Group G] [Group.FG G] [Monoid M] [Finite M] :
    Finite (G →* M) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.1 ‹Group.FG G›
  have := hSfin.to_subtype
  refine Finite.of_injective (fun f : G →* M ↦ fun s : S ↦ f s) fun f g hfg ↦ ?_
  exact MonoidHom.eq_of_eqOn_dense hS fun x hx ↦ congrFun hfg ⟨x, hx⟩

namespace MulAction

/-- A finitely generated group acting faithfully on a set, with all orbits of size at most `N`,
is finite. -/
theorem finite_of_encard_orbit_le {G X : Type*} [Group G] [Group.FG G] [MulAction G X]
    [FaithfulSMul G X] (N : ℕ) (h : ∀ x : X, (orbit G x).encard ≤ N) : Finite G := by
  have (j : Fin (N + 1)) : Finite (G →* Equiv.Perm (Fin j)) := MonoidHom.finite_of_fg _ _
  have : Finite (Σ j : Fin (N + 1), G →* Equiv.Perm (Fin j)) := inferInstance
  let Φ : G → ∀ ρ : Σ j : Fin (N + 1), G →* Equiv.Perm (Fin j), Equiv.Perm (Fin ρ.1) :=
    fun g ρ ↦ ρ.2 g
  refine Finite.of_injective Φ fun g g' hgg' ↦ FaithfulSMul.eq_of_smul_eq_smul (α := X) fun x ↦ ?_
  have hfin : (orbit G x).Finite := Set.finite_of_encard_le_coe (h x)
  have := hfin.to_subtype
  have hj : Nat.card (orbit G x) < N + 1 := by
    rw [Nat.lt_add_one_iff, Nat.card_coe_set_eq, ← ENat.natCast_le_natCast, hfin.cast_ncard_eq]
    exact h x
  let e : orbit G x ≃ Fin (Nat.card (orbit G x)) := Finite.equivFin _
  let ρ : G →* Equiv.Perm (Fin (Nat.card (orbit G x))) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (toPermHom G (orbit G x))
  have hρ : toPermHom G (orbit G x) g = toPermHom G (orbit G x) g' :=
    (Equiv.permCongrHom e).injective (congrFun hgg' ⟨⟨_, hj⟩, ρ⟩)
  have := congrArg Subtype.val (Equiv.congr_fun hρ ⟨x, mem_orbit_self x⟩)
  simpa using this

end MulAction

end
