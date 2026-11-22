/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import TDCSG.CriticalRadius.Five
public import TDCSG.CriticalRadius.Statements

/-!
# The orbit structure of `GG₅(r)` and the Galois conjugate embedding

This file formalizes the arithmetic set-up of Part B of `notes/proofs/critical-radius-n5.md`.
Let `ζ = exp (2πi / 5)`. The integer model `TDCSG.Five.Cyc` of `ℤ[ζ]` is a commutative ring, and
the Galois automorphism `σ : ζ ↦ ζ²` of `ℤ[ζ]` is a ring automorphism of it. Every element of
`GG 5 5 r r` acts at each point as `x ↦ ζʲ x + t` with `t` in the ideal `(1 - ζ) ℤ[ζ]`
(Lemma 1.1 of the written proof). The map `x ↦ (x, σ x)` embeds `ℤ[ζ]` as a lattice in `ℂ × ℂ`,
so a subset of `ℤ[ζ]` bounded in both embeddings is finite. Consequently `GG 5 5 r r` is finite
exactly when the Galois conjugates `σ t` of the translation parts are bounded (Lemma 4.1).

## Main definitions

* `TDCSG.Five.Cyc.instCommRing`: the ring structure of `ℤ[ζ]` on the model.
* `TDCSG.Five.Cyc.embedHom`: `TDCSG.Five.Cyc.embed`, the embedding `ζ ↦ ζ` into `ℂ`, as a ring
  homomorphism.
* `TDCSG.Five.Cyc.embedTwo`: the second complex embedding `ζ ↦ ζ²`.
* `TDCSG.Five.Cyc.galois`: the Galois automorphism `σ : ζ ↦ ζ²` of `ℤ[ζ]`, as a ring
  homomorphism.
* `TDCSG.Five.ConjugatesBounded r`: the Galois conjugates of the translation parts of the elements
  of `GG 5 5 r r` are bounded.
-/

@[expose] public section

open Complex Metric Equiv
open scoped Real goldenRatio

namespace TDCSG.Five

@[inherit_doc] local notation "ζ" => zeta

namespace Cyc

/-! ### The ring structure of the model -/

instance : Zero Cyc := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Cyc := ⟨⟨1, 0, 0, 0⟩⟩
instance : Neg Cyc := ⟨fun v ↦ ⟨-v.c0, -v.c1, -v.c2, -v.c3⟩⟩
instance : Mul Cyc := ⟨mul⟩

theorem zero_def : (0 : Cyc) = ⟨0, 0, 0, 0⟩ :=
  rfl

theorem one_def : (1 : Cyc) = ⟨1, 0, 0, 0⟩ :=
  rfl

theorem neg_def (v : Cyc) : -v = ⟨-v.c0, -v.c1, -v.c2, -v.c3⟩ :=
  rfl

theorem mul_def (v w : Cyc) : v * w = mul v w :=
  rfl

/-- The coordinates of a product, in the basis `1, ζ, ζ², ζ³`. -/
theorem mul_eq (v w : Cyc) : v * w =
    ⟨v.c0 * w.c0 - v.c1 * w.c3 - v.c2 * (w.c2 - w.c3) - v.c3 * (w.c1 - w.c2),
      v.c0 * w.c1 + v.c1 * (w.c0 - w.c3) - v.c2 * w.c2 - v.c3 * (w.c1 - w.c3),
      v.c0 * w.c2 + v.c1 * (w.c1 - w.c3) + v.c2 * (w.c0 - w.c2) - v.c3 * w.c1,
      v.c0 * w.c3 + v.c1 * (w.c2 - w.c3) + v.c2 * (w.c1 - w.c2) + v.c3 * (w.c0 - w.c1)⟩ := by
  simp only [mul_def, mul, mulZeta, add_def, smul_def]
  ext <;> simp only <;> ring

/-- The ring `ℤ[ζ]`, in the coordinates of the model. -/
instance instCommRing : CommRing Cyc where
  add_assoc _ _ _ := by ext <;> simp only [add_def] <;> ring
  zero_add _ := by ext <;> simp only [add_def, zero_def] <;> ring
  add_zero _ := by ext <;> simp only [add_def, zero_def] <;> ring
  add_comm _ _ := by ext <;> simp only [add_def] <;> ring
  nsmul := nsmulRec
  zsmul k v := k • v
  zsmul_zero' _ := by ext <;> simp only [smul_def, zero_def] <;> ring
  zsmul_succ' _ _ := by ext <;> simp only [smul_def, add_def] <;> push_cast <;> ring
  zsmul_neg' _ _ := by
    ext <;> simp only [smul_def, neg_def, Int.negSucc_eq] <;> push_cast <;> ring
  neg_add_cancel _ := by ext <;> simp only [add_def, neg_def, zero_def] <;> ring
  sub_eq_add_neg _ _ := by ext <;> simp only [sub_def, add_def, neg_def] <;> ring
  mul_assoc _ _ _ := by ext <;> simp only [mul_eq] <;> ring
  one_mul _ := by ext <;> simp only [mul_eq, one_def] <;> ring
  mul_one _ := by ext <;> simp only [mul_eq, one_def] <;> ring
  zero_mul _ := by ext <;> simp only [mul_eq, zero_def] <;> ring
  mul_zero _ := by ext <;> simp only [mul_eq, zero_def] <;> ring
  left_distrib _ _ _ := by ext <;> simp only [mul_eq, add_def] <;> ring
  right_distrib _ _ _ := by ext <;> simp only [mul_eq, add_def] <;> ring
  mul_comm _ _ := by ext <;> simp only [mul_eq] <;> ring

/-- The element `ζ` of the model. -/
def zetaC : Cyc := ⟨0, 1, 0, 0⟩

/-- `TDCSG.Five.Cyc.embed`, the complex embedding `ζ ↦ ζ` of `ℤ[ζ]`, as a ring
homomorphism. -/
noncomputable def embedHom : Cyc →+* ℂ where
  toFun := embed
  map_one' := by simp [embed, one_def]
  map_mul' := embed_mul
  map_zero' := by simp [embed, zero_def]
  map_add' := embed_add

/-- The second complex embedding `ζ ↦ ζ²` of `ℤ[ζ]`. -/
noncomputable def embedTwo (v : Cyc) : ℂ :=
  v.c0 + v.c1 * ζ ^ 2 + v.c2 * (ζ ^ 2) ^ 2 + v.c3 * (ζ ^ 2) ^ 3

/-- The Galois automorphism `σ : ζ ↦ ζ²` of `ℤ[ζ]`. In coordinates it uses
`ζ⁴ = -1 - ζ - ζ² - ζ³` and `ζ⁶ = ζ`. -/
def galois : Cyc →+* Cyc where
  toFun v := ⟨v.c0 - v.c2, v.c3 - v.c2, v.c1 - v.c2, -v.c2⟩
  map_one' := by ext <;> simp [one_def]
  map_mul' _ _ := by ext <;> simp only [mul_eq] <;> ring
  map_zero' := by ext <;> simp [zero_def]
  map_add' _ _ := by ext <;> simp only [add_def] <;> ring

end Cyc

open Cyc

/-- The Galois conjugates `σ t` of the translation parts `t` of the elements of `GG 5 5 r r` are
bounded: there is `R` such that every element acts at every point `z` as `x ↦ ζʲ x + t` for some
`j` and some `t ∈ ℤ[ζ]` with `|σ t| ≤ R`. -/
def ConjugatesBounded (r : ℝ) : Prop :=
  ∃ R : ℝ, ∀ g ∈ GG 5 5 r r, ∀ z : ℂ, ∃ j : ℕ, ∃ t : Cyc,
    g z = ζ ^ j * z + embed t ∧ ‖embed (galois t)‖ ≤ R

/-! ### Staging: the targets, as propositions -/

namespace Targets

/-- `embed ∘ σ` is the second complex embedding. -/
def EmbedGalois : Prop := ∀ v : Cyc, embed (galois v) = embedTwo v

/-- Lemma 1.1: every element of `GG 5 5 r r` acts at each point as `x ↦ ζʲ x + t` with `t` in
`(1 - ζ) ℤ[ζ]`. -/
def ExistsAffine : Prop :=
  ∀ (r : ℝ) (g : Perm ℂ), g ∈ GG 5 5 r r → ∀ z : ℂ,
    ∃ j < 5, ∃ s : Cyc, g z = ζ ^ j * z + embed ((1 - zetaC) * s)

/-- A subset of `ℤ[ζ]` bounded in both embeddings is finite. -/
def FiniteSetOfNormLe : Prop :=
  ∀ R : ℝ, {v : Cyc | ‖embed v‖ ≤ R ∧ ‖embed (galois v)‖ ≤ R}.Finite

/-- Lemma 4.1: bounded conjugates of the translation parts give a finite group. -/
def FiniteOfConjugatesBounded : Prop :=
  ∀ r : ℝ, ConjugatesBounded r → Finite (GG 5 5 r r)

/-- The converse of Lemma 4.1, which shows that its hypothesis is not vacuous. -/
def ConjugatesBoundedOfFinite : Prop :=
  ∀ r : ℝ, Finite (GG 5 5 r r) → ConjugatesBounded r

end Targets

end TDCSG.Five

end
