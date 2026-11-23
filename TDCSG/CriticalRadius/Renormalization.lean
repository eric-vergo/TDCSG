/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The renormalization lemma

This is Lemma 2.1 of `notes/proofs/critical-radius-n8.md`, in an abstract form. A family of
partial isometries `t ↦ ±t + c` of the real line, each defined on a closed interval, is
*realized* if each of them is contained in a reflexive and transitive relation `R` on its
interval, and *closed under rescaling by `ε`* if each rescaled member `t ↦ ±t + ε c`, on the
rescaled interval, is pointwise a composite of family members. Then every member rescaled by
`ε ^ k` is realized, for every `k`.

In the application `R t t'` says that the point of parameter `t'` of a line lies in the orbit of
the point of parameter `t`.

## Main definitions

* `TDCSG.Renormalization.ract`: the isometry `t ↦ t + c` or `t ↦ c - t` of `ℝ`.
* `TDCSG.Renormalization.IsComposite`: a sequence of family members carrying `s` to `s'`, with every
  intermediate point in the domain of the next member.

## Main statements

* `TDCSG.Renormalization.renormalize`: the renormalization lemma.
-/

@[expose] public section

namespace TDCSG.Renormalization

/-- The isometry `t ↦ t + c` of `ℝ` if `pos`, and `t ↦ c - t` otherwise. -/
def ract (pos : Bool) (c t : ℝ) : ℝ := if pos then t + c else c - t

/-- Rescaling commutes with the isometries `t ↦ ±t + c`. -/
theorem ract_mul (pos : Bool) (ε c t : ℝ) : ract pos (ε * c) (ε * t) = ε * ract pos c t := by
  cases pos <;> simp only [ract, Bool.false_eq_true, ite_false, ite_true] <;> ring

/-- The composite of two isometries `t ↦ ±t + c`. -/
theorem ract_ract (p₁ p₂ : Bool) (c₁ c₂ t : ℝ) :
    ract p₂ c₂ (ract p₁ c₁ t) = ract (p₂ == p₁) ((if p₂ then c₁ else -c₁) + c₂) t := by
  cases p₁ <;> cases p₂ <;> simp [ract] <;> ring

/-- An isometry `t ↦ ±t + c` maps the unordered interval between `a` and `b` into the unordered
interval between their images. -/
theorem ract_mem_uIcc {pos : Bool} {c a b t : ℝ} (ht : t ∈ Set.uIcc a b) :
    ract pos c t ∈ Set.uIcc (ract pos c a) (ract pos c b) := by
  rw [Set.mem_uIcc] at ht ⊢
  cases pos <;> simp only [ract, Bool.false_eq_true, ite_false, ite_true] <;>
    rcases ht with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  exacts [Or.inr ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩,
    Or.inl ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩]

variable {ι : Type*} (S : ι → Prop) (pos : ι → Bool) (c lo hi : ι → ℝ)

/-- `IsComposite S pos c lo hi s gs s'`: the members `gs` of the family `S`, applied left to right,
carry `s` to `s'`, and each of them is applied at a point of its domain `[lo g, hi g]`. -/
def IsComposite : ℝ → List ι → ℝ → Prop
  | s, [], s' => s = s'
  | s, g :: gs, s' => S g ∧ s ∈ Set.Icc (lo g) (hi g) ∧ IsComposite (ract (pos g) (c g) s) gs s'

/-- **The renormalization lemma.** If every member `t ↦ ±t + c i` of a family is realized by `R`
on its domain `[lo i, hi i]`, and every member rescaled by `ε` is, on the rescaled domain, a
composite of members, then every member rescaled by `ε ^ k` is realized by `R` on its domain
rescaled by `ε ^ k`. -/
theorem renormalize (R : ℝ → ℝ → Prop) (hrefl : ∀ t, R t t)
    (htrans : ∀ a b d, R a b → R b d → R a d) {ε : ℝ} (hε : 0 < ε)
    (hreal : ∀ i, S i → ∀ t ∈ Set.Icc (lo i) (hi i), R t (ract (pos i) (c i) t))
    (hclos : ∀ i, S i → ∀ s ∈ Set.Icc (ε * lo i) (ε * hi i),
      ∃ gs, IsComposite S pos c lo hi s gs (ract (pos i) (ε * c i) s))
    (k : ℕ) {i : ι} (hS : S i) {t : ℝ} (ht : t ∈ Set.Icc (ε ^ k * lo i) (ε ^ k * hi i)) :
    R t (ract (pos i) (ε ^ k * c i) t) := by
  induction k generalizing i t with
  | zero => simpa using hreal i hS t (by simpa using ht)
  | succ k ih =>
    have hδ : 0 < ε ^ k := pow_pos hε k
    have chain : ∀ gs s s', IsComposite S pos c lo hi s gs s' → R (ε ^ k * s) (ε ^ k * s') := by
      intro gs
      induction gs with
      | nil => intro s s' h; rw [show s = s' from h]; exact hrefl _
      | cons g gs ihg =>
        rintro s s' ⟨hg, hs, hrest⟩
        refine htrans _ _ _ ?_ (ihg _ _ hrest)
        rw [← ract_mul]
        exact ih hg ⟨mul_le_mul_of_nonneg_left hs.1 hδ.le, mul_le_mul_of_nonneg_left hs.2 hδ.le⟩
    set s := t / ε ^ k with hs
    have hts : t = ε ^ k * s := by rw [hs]; field_simp
    have hmem : s ∈ Set.Icc (ε * lo i) (ε * hi i) := by
      rw [pow_succ] at ht
      rw [hs, Set.mem_Icc, le_div_iff₀ hδ, div_le_iff₀ hδ]
      constructor <;> linarith [ht.1, ht.2]
    obtain ⟨gs, hgs⟩ := hclos i hS s hmem
    have := chain gs _ _ hgs
    rwa [← hts, ← ract_mul, ← mul_assoc, ← pow_succ, ← hts] at this

end TDCSG.Renormalization

end
