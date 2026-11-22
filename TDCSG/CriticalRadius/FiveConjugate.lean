/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import TDCSG.CriticalRadius.Five
public import TDCSG.Finiteness
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

## Main statements

* `TDCSG.Five.Cyc.embed_galois`: `embed ∘ σ` is the second complex embedding `ζ ↦ ζ²`.
* `TDCSG.Five.exists_affine`, `TDCSG.Five.exists_finset_affine`: every element of `GG 5 5 r r`
  acts at each point as `x ↦ ζʲ x + (1 - ζ) s` with `s ∈ ℤ[ζ]`, and the `s` that occur for one
  element form a finite set (Lemma 1.1).
* `TDCSG.Five.Cyc.finite_setOf_norm_le`: a subset of `ℤ[ζ]` bounded in both embeddings is
  finite.
* `TDCSG.Five.finite_GG_of_conjugatesBounded`, `TDCSG.Five.finite_GG_iff_conjugatesBounded`:
  `GG 5 5 r r` is finite exactly when the Galois conjugates of the translation parts are bounded
  (Lemma 4.1 and its converse). The condition holds for `r < 1` and fails for `r ≥ √(3 + φ)`
  (`TDCSG.Five.conjugatesBounded_of_lt_one`, `TDCSG.Five.not_conjugatesBounded`).
* `TDCSG.Five.finiteBelowClosedFormFive_iff`: the unproved proposition
  `TDCSG.CriticalRadius.FiniteBelowClosedFormFive` is equivalent to bounded conjugates at every
  `r < √(3 + φ)`.

## Implementation notes

The ring axioms of `TDCSG.Five.Cyc` and the multiplicativity of `σ` are polynomial identities
in the integer coordinates, checked by `ring`. `TDCSG.Five.Cyc.conj` is complex conjugation
`ζ ↦ ζ⁴`; together with `σ` and `σ` followed by conjugation it gives the four embeddings, whose
sum is the trace (`TDCSG.Five.Cyc.trace_eq`). Bounding the traces of `ζ⁻ᵏ v` for `k ≤ 4` bounds
the coordinates of `v`.
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

@[simp]
theorem embedHom_apply (v : Cyc) : embedHom v = embed v :=
  rfl

@[simp]
theorem embed_zero : embed 0 = 0 :=
  map_zero embedHom

@[simp]
theorem embed_one : embed 1 = 1 :=
  map_one embedHom

@[simp]
theorem embed_mul' (v w : Cyc) : embed (v * w) = embed v * embed w :=
  map_mul embedHom v w

@[simp]
theorem embed_neg (v : Cyc) : embed (-v) = -embed v :=
  map_neg embedHom v

@[simp]
theorem embed_pow (v : Cyc) (k : ℕ) : embed (v ^ k) = embed v ^ k :=
  map_pow embedHom v k

@[simp]
theorem embed_zetaC : embed zetaC = ζ := by
  simp [embed, zetaC]

theorem galois_apply (v : Cyc) : galois v = ⟨v.c0 - v.c2, v.c3 - v.c2, v.c1 - v.c2, -v.c2⟩ :=
  rfl

/-- `σ` sends `ζ` to `ζ²`. -/
theorem galois_zetaC : galois zetaC = zetaC ^ 2 := by
  rw [pow_two, mul_eq, galois_apply, zetaC]
  ext <;> simp

/-- `embed ∘ σ` is the second complex embedding `ζ ↦ ζ²`. -/
theorem embed_galois (v : Cyc) : embed (galois v) = embedTwo v := by
  simp only [embed, embedTwo, galois_apply]
  push_cast
  linear_combination (-(v.c2 : ℂ)) * one_add_zeta_add - (v.c3 : ℂ) * ζ * zeta_pow_five

/-- `embed ∘ σ` is the second complex embedding `ζ ↦ ζ²`, as ring homomorphisms. -/
theorem embedHom_comp_galois_apply (v : Cyc) : embedHom.comp galois v = embedTwo v :=
  embed_galois v

/-- The second complex embedding is a ring homomorphism. -/
theorem embedTwo_mul (v w : Cyc) : embedTwo (v * w) = embedTwo v * embedTwo w := by
  rw [← embed_galois, ← embed_galois, ← embed_galois, map_mul, embed_mul']

end Cyc

open Cyc

/-- `|ζ| = 1`. -/
theorem norm_zeta : ‖ζ‖ = 1 :=
  isPrimitiveRoot_zeta.norm'_eq_one (by norm_num)

/-- Powers of `ζ` only depend on the exponent modulo `5`. -/
theorem zeta_pow_mod (k : ℕ) : ζ ^ (k % 5) = ζ ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k 5, pow_add, pow_mul, zeta_pow_five, one_pow, mul_one]

theorem embed_oneSub_mul (s : Cyc) : embed ((1 - zetaC) * s) = (1 - ζ) * embed s := by
  rw [embed_mul', ← embedHom_apply, map_sub, map_one, embedHom_apply, embed_zetaC]

/-! ### Lemma 1.1: the translation lattice -/

/-- Lemma 1.1, with finitely many translation parts: for every element `g` of `GG 5 5 r r` there
is a finite set `F ⊆ ℤ[ζ]` such that at each point `z`, `g` acts as `x ↦ ζʲ x + (1 - ζ) s` for
some `j < 5` and `s ∈ F`. -/
theorem exists_finset_affine {r : ℝ} {g : Perm ℂ} (hg : g ∈ GG 5 5 r r) :
    ∃ F : Finset Cyc, ∀ z : ℂ, ∃ j < 5, ∃ s ∈ F, g z = ζ ^ j * z + embed ((1 - zetaC) * s) := by
  classical
  rw [GG_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem σ hσ =>
    have hrot (c z : ℂ) :
        rotation 5 c z = ζ ^ 4 * z + (1 - ζ) * ((1 + ζ + ζ ^ 2 + ζ ^ 3) * c) := by
      rw [rotation, Nat.cast_ofNat, exp_rotationAngle_five]
      ring
    rcases hσ with rfl | rfl
    · refine ⟨{0, ⟨-1, -1, -1, -1⟩}, fun z ↦ ?_⟩
      by_cases hz : z ∈ closedBall leftCenter r
      · refine ⟨4, by norm_num, ⟨-1, -1, -1, -1⟩, by simp, ?_⟩
        rw [permA_apply, genA, diskRotation_of_mem hz, hrot, embed_oneSub_mul, leftCenter]
        simp only [embed]
        push_cast
        ring
      · refine ⟨0, by norm_num, 0, by simp, ?_⟩
        rw [permA_apply, genA, diskRotation_of_notMem hz]
        simp
    · refine ⟨{0, ⟨1, 1, 1, 1⟩}, fun z ↦ ?_⟩
      by_cases hz : z ∈ closedBall rightCenter r
      · refine ⟨4, by norm_num, ⟨1, 1, 1, 1⟩, by simp, ?_⟩
        rw [permB_apply, genB, diskRotation_of_mem hz, hrot, embed_oneSub_mul, rightCenter]
        simp only [embed]
        push_cast
        ring
      · refine ⟨0, by norm_num, 0, by simp, ?_⟩
        rw [permB_apply, genB, diskRotation_of_notMem hz]
        simp
  | one => exact ⟨{0}, fun z ↦ ⟨0, by norm_num, 0, by simp, by simp⟩⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨Fg, hFg⟩ := ihg
    obtain ⟨Fh, hFh⟩ := ihh
    refine ⟨((Finset.range 5 ×ˢ Fg) ×ˢ Fh).image fun x ↦ zetaC ^ x.1.1 * x.2 + x.1.2,
      fun z ↦ ?_⟩
    obtain ⟨j', -, s', hs', e'⟩ := hFh z
    obtain ⟨j, hj, s, hs, e⟩ := hFg (h z)
    refine ⟨(j + j') % 5, Nat.mod_lt _ (by norm_num), zetaC ^ j * s' + s,
      Finset.mem_image.2 ⟨((j, s), s'), by simp [hj, hs, hs'], rfl⟩, ?_⟩
    rw [Perm.mul_apply, e, e', zeta_pow_mod, embed_oneSub_mul, embed_oneSub_mul,
      embed_oneSub_mul, embed_add, embed_mul', embed_pow, embed_zetaC]
    ring
  | inv g _ ihg =>
    obtain ⟨F, hF⟩ := ihg
    refine ⟨(Finset.range 5 ×ˢ F).image fun x ↦ -(zetaC ^ (4 * x.1) * x.2), fun z ↦ ?_⟩
    obtain ⟨j, hj, s, hs, e⟩ := hF (g⁻¹ z)
    rw [show g (g⁻¹ z) = z by simp] at e
    refine ⟨4 * j % 5, Nat.mod_lt _ (by norm_num), -(zetaC ^ (4 * j) * s),
      Finset.mem_image.2 ⟨(j, s), by simp [hj, hs], rfl⟩, ?_⟩
    have h1 : ζ ^ (4 * j) * ζ ^ j = 1 := by
      rw [← pow_add, show 4 * j + j = 5 * j by ring, pow_mul, zeta_pow_five, one_pow]
    rw [zeta_pow_mod, embed_oneSub_mul, embed_neg, embed_mul', embed_pow, embed_zetaC]
    rw [embed_oneSub_mul] at e
    linear_combination (-ζ ^ (4 * j)) * e - g⁻¹ z * h1

/-- Lemma 1.1 of `notes/proofs/critical-radius-n5.md`: every element of `GG 5 5 r r` acts at
each point as `x ↦ ζʲ x + t` with `t` in the ideal `(1 - ζ) ℤ[ζ]`. -/
theorem exists_affine {r : ℝ} {g : Perm ℂ} (hg : g ∈ GG 5 5 r r) (z : ℂ) :
    ∃ j < 5, ∃ s : Cyc, g z = ζ ^ j * z + embed ((1 - zetaC) * s) :=
  let ⟨_, hF⟩ := exists_finset_affine hg
  let ⟨j, hj, s, _, e⟩ := hF z
  ⟨j, hj, s, e⟩

/-! ### Lattice points bounded in both embeddings -/

namespace Cyc

/-- The trace of `ℚ(ζ) / ℚ`, on the model. -/
def trace (v : Cyc) : ℤ := 4 * v.c0 - v.c1 - v.c2 - v.c3

/-- The trace is the sum of the four complex embeddings. -/
theorem trace_eq (v : Cyc) : (trace v : ℂ) = embed v + (starRingEnd ℂ) (embed v) +
    embed (galois v) + (starRingEnd ℂ) (embed (galois v)) := by
  rw [← embed_conj, ← embed_conj, ← embed_add, ← embed_add, ← embed_add]
  have : v + conj v + galois v + conj (galois v) = ⟨trace v, 0, 0, 0⟩ := by
    simp only [add_def, conj, galois_apply, trace]
    ext <;> simp only <;> ring
  rw [this]
  simp [embed]

/-- The trace is bounded by the two embeddings. -/
theorem abs_trace_le (v : Cyc) :
    |(trace v : ℝ)| ≤ 2 * ‖embed v‖ + 2 * ‖embed (galois v)‖ := by
  have h := congrArg norm (trace_eq v)
  rw [norm_intCast] at h
  rw [h]
  calc _ ≤ ‖embed v‖ + ‖(starRingEnd ℂ) (embed v)‖ + ‖embed (galois v)‖ +
        ‖(starRingEnd ℂ) (embed (galois v))‖ := norm_add₄_le
    _ = 2 * ‖embed v‖ + 2 * ‖embed (galois v)‖ := by simp only [Complex.norm_conj]; ring

theorem norm_embed_mulZetaInv (v : Cyc) : ‖embed (mulZetaInv v)‖ = ‖embed v‖ := by
  rw [embed_mulZetaInv, norm_mul, norm_pow, norm_zeta, one_pow, one_mul]

theorem norm_embed_galois_mulZetaInv (v : Cyc) :
    ‖embed (galois (mulZetaInv v))‖ = ‖embed (galois v)‖ := by
  have : galois (mulZetaInv v) = mulZeta (mulZeta (mulZeta (galois v))) := by
    simp only [galois_apply, mulZeta, mulZetaInv]
    ext <;> simp only <;> ring
  rw [this, embed_mulZeta, embed_mulZeta, embed_mulZeta, norm_mul, norm_mul, norm_mul, norm_zeta,
    one_mul, one_mul, one_mul]

/-- The coordinates of a lattice point are bounded by its two embeddings. -/
theorem abs_coords_le {v : Cyc} {R : ℝ} (h₁ : ‖embed v‖ ≤ R) (h₂ : ‖embed (galois v)‖ ≤ R) :
    |(v.c0 : ℝ)| ≤ 2 * R ∧ |(v.c1 : ℝ)| ≤ 2 * R ∧ |(v.c2 : ℝ)| ≤ 2 * R ∧
      |(v.c3 : ℝ)| ≤ 2 * R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans h₁
  have e₁ (k : ℕ) : ‖embed (mulZetaInv^[k] v)‖ = ‖embed v‖ := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', norm_embed_mulZetaInv, ih]
  have e₂ (k : ℕ) : ‖embed (galois (mulZetaInv^[k] v))‖ = ‖embed (galois v)‖ := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', norm_embed_galois_mulZetaInv, ih]
  have hT (k : ℕ) : |(trace (mulZetaInv^[k] v) : ℝ)| ≤ 4 * R := by
    refine (abs_trace_le _).trans ?_
    rw [e₁, e₂]
    linarith
  have t₀ := abs_le.1 (hT 0)
  have t₁ := abs_le.1 (hT 1)
  have t₂ := abs_le.1 (hT 2)
  have t₃ := abs_le.1 (hT 3)
  have t₄ := abs_le.1 (hT 4)
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, mulZetaInv, trace]
    at t₀ t₁ t₂ t₃ t₄
  push_cast at t₀ t₁ t₂ t₃ t₄
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩ <;>
    linarith [t₀.1, t₀.2, t₁.1, t₁.2, t₂.1, t₂.2, t₃.1, t₃.2, t₄.1, t₄.2]

/-- The lattice `ℤ[ζ]`, embedded in `ℂ × ℂ` by `x ↦ (x, σ x)`, is discrete: a subset bounded in
both embeddings is finite. -/
theorem finite_setOf_norm_le (R : ℝ) :
    {v : Cyc | ‖embed v‖ ≤ R ∧ ‖embed (galois v)‖ ≤ R}.Finite := by
  set B : ℤ := ⌈2 * R⌉
  let f : Cyc → ℤ × ℤ × ℤ × ℤ := fun v ↦ (v.c0, v.c1, v.c2, v.c3)
  have hf : Function.Injective f := fun v w h ↦ by
    simp only [f, Prod.mk.injEq] at h
    ext <;> tauto
  have hbox := (Set.finite_Icc (-B) B).prod ((Set.finite_Icc (-B) B).prod
    ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B)))
  refine (hbox.preimage hf.injOn).subset fun v ⟨h₁, h₂⟩ ↦ ?_
  have key : ∀ x : ℤ, |(x : ℝ)| ≤ 2 * R → x ∈ Set.Icc (-B) B := fun x hx ↦ by
    have hB := Int.le_ceil (2 * R)
    rw [abs_le] at hx
    refine ⟨?_, Int.cast_le.1 (hx.2.trans hB)⟩
    have : (-(B : ℝ)) ≤ x := by linarith [hx.1]
    exact_mod_cast this
  obtain ⟨a₀, a₁, a₂, a₃⟩ := abs_coords_le h₁ h₂
  exact ⟨key _ a₀, key _ a₁, key _ a₂, key _ a₃⟩

end Cyc

/-! ### Lemma 4.1: bounded conjugates and finiteness -/

/-- The Galois conjugates `σ t` of the translation parts `t` of the elements of `GG 5 5 r r` are
bounded: there is `R` such that every element acts at every point `z` as `x ↦ ζʲ x + t` for some
`j` and some `t ∈ ℤ[ζ]` with `|σ t| ≤ R`. -/
def ConjugatesBounded (r : ℝ) : Prop :=
  ∃ R : ℝ, ∀ g ∈ GG 5 5 r r, ∀ z : ℂ, ∃ j : ℕ, ∃ t : Cyc,
    g z = ζ ^ j * z + embed t ∧ ‖embed (galois t)‖ ≤ R

/-- Lemma 4.1 of `notes/proofs/critical-radius-n5.md`: if the Galois conjugates of the
translation parts are bounded, then `GG 5 5 r r` is finite. -/
theorem finite_GG_of_conjugatesBounded {r : ℝ} (h : ConjugatesBounded r) :
    Finite (GG 5 5 r r) := by
  obtain ⟨R, hR⟩ := h
  set P := 2 * (1 + max r r)
  set S := {t : Cyc | ‖embed t‖ ≤ max R P ∧ ‖embed (galois t)‖ ≤ max R P}
  set T := (Set.Iio 5 : Set ℕ) ×ˢ S
  have hT : T.Finite := (Set.finite_Iio 5).prod (finite_setOf_norm_le _)
  refine finite_of_encard_orbit_le (T.ncard + 1) fun z ↦ ?_
  set f := fun jt : ℕ × Cyc ↦ ζ ^ jt.1 * z + embed jt.2
  have hsub : orbit 5 5 r r z ⊆ insert z (f '' T) := by
    rintro y ⟨g, hg, rfl⟩
    by_cases hz : z ∈ diskUnion r r
    · right
      obtain ⟨j, t, e, ht⟩ := hR g hg z
      have hgz := norm_le_of_mem_diskUnion (apply_mem_diskUnion hg hz)
      have hzR := norm_le_of_mem_diskUnion hz
      have hnorm : ‖embed t‖ ≤ P := by
        rw [show embed t = g z - ζ ^ j * z by rw [e]; ring]
        calc ‖g z - ζ ^ j * z‖ ≤ ‖g z‖ + ‖ζ ^ j * z‖ := norm_sub_le _ _
          _ ≤ (1 + max r r) + (1 + max r r) := by
            rw [norm_mul, norm_pow, norm_zeta, one_pow, one_mul]
            exact add_le_add hgz hzR
          _ = P := by ring
      refine ⟨(j % 5, t), ⟨Nat.mod_lt _ (by norm_num), hnorm.trans (le_max_right _ _),
        ht.trans (le_max_left _ _)⟩, ?_⟩
      simp only [f, zeta_pow_mod, e]
    · left
      exact apply_eq_of_notMem_diskUnion hg hz
  calc (orbit 5 5 r r z).encard ≤ (insert z (f '' T)).encard := Set.encard_le_encard hsub
    _ ≤ (f '' T).encard + 1 := Set.encard_insert_le _ _
    _ ≤ T.encard + 1 := by gcongr; exact Set.encard_image_le _ _
    _ = ((T.ncard + 1 : ℕ) : ℕ∞) := by rw [← hT.cast_ncard_eq]; push_cast; rfl

/-- The converse of Lemma 4.1: if `GG 5 5 r r` is finite, the Galois conjugates of the
translation parts are bounded. So the hypothesis of `TDCSG.Five.finite_GG_of_conjugatesBounded`
holds for every radius at which the group is finite, for instance every `r < 1`. -/
theorem conjugatesBounded_of_finite {r : ℝ} [Finite (GG 5 5 r r)] : ConjugatesBounded r := by
  classical
  have := Fintype.ofFinite (GG 5 5 r r)
  choose F hF using fun g : GG 5 5 r r ↦ exists_finset_affine g.2
  refine ⟨∑ g, ∑ s ∈ F g, ‖embed (galois ((1 - zetaC) * s))‖, fun g hg z ↦ ?_⟩
  obtain ⟨j, -, s, hs, e⟩ := hF ⟨g, hg⟩ z
  refine ⟨j, (1 - zetaC) * s, e, ?_⟩
  calc ‖embed (galois ((1 - zetaC) * s))‖
      ≤ ∑ s ∈ F ⟨g, hg⟩, ‖embed (galois ((1 - zetaC) * s))‖ :=
        Finset.single_le_sum (f := fun s ↦ ‖embed (galois ((1 - zetaC) * s))‖)
          (fun _ _ ↦ norm_nonneg _) hs
    _ ≤ _ := Finset.single_le_sum (f := fun g ↦ ∑ s ∈ F g, ‖embed (galois ((1 - zetaC) * s))‖)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ _)

/-- `GG 5 5 r r` is finite exactly when the Galois conjugates of the translation parts of its
elements are bounded. -/
theorem finite_GG_iff_conjugatesBounded {r : ℝ} : Finite (GG 5 5 r r) ↔ ConjugatesBounded r :=
  ⟨fun _ ↦ conjugatesBounded_of_finite, finite_GG_of_conjugatesBounded⟩

/-- The hypothesis of Lemma 4.1 holds for every `r < 1`, where the disks are disjoint. -/
theorem conjugatesBounded_of_lt_one {r : ℝ} (hr : r < 1) : ConjugatesBounded r :=
  finite_GG_iff_conjugatesBounded.1 (finite_GG_of_lt_one 5 hr)

/-- The hypothesis of Lemma 4.1 fails for every `r ≥ √(3 + φ)`, where the group is infinite. -/
theorem not_conjugatesBounded {r : ℝ} (hr : √(3 + φ) ≤ r) : ¬ConjugatesBounded r := fun h ↦
  not_finite_iff_infinite.2 (infinite_GG hr) (finite_GG_of_conjugatesBounded h)

/-- Finiteness below the closed form, in terms of the Galois conjugates of the translation
parts. -/
theorem finiteBelowClosedFormFive_iff :
    CriticalRadius.FiniteBelowClosedFormFive ↔ ∀ r : ℝ, r < √(3 + φ) → ConjugatesBounded r :=
  forall₂_congr fun _ _ ↦ finite_GG_iff_conjugatesBounded

end TDCSG.Five

end
