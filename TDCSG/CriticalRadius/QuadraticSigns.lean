/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact signs in real quadratic towers

The elements `a + b √m` of `ℤ[√m]`, and exact tests for the signs of `x + y √h` and of
`x + y √h₁ + z √h₂` with `x, y, z, h, h₁, h₂ ∈ ℤ[√m]`, by repeated squaring. They decide the
inequalities behind the renormalization families of `notes/proofs/critical-radius-n8.md` and
`critical-radius-n12.md`, whose numbers lie in such towers.

## Main definitions

* `TDCSG.Quad m`: the element `a + b √m` of `ℤ[√m]`, by its integer coordinates.
* `TDCSG.sqrtNonneg`: from a sign test on a ring, a sign test for `x + y √h`.
* `TDCSG.Quad.nonneg`, `TDCSG.Quad.nonneg₂`, `TDCSG.Quad.nonneg₃`: exact tests for
  `0 ≤ a + b √m`, `0 ≤ x + y √h` and `0 ≤ x + y √h₁ + z √h₂`.

## Main statements

* `TDCSG.nonneg_add_mul_sqrt`: the real inequality behind `TDCSG.sqrtNonneg`.
* `TDCSG.Quad.nonneg_toReal`, `TDCSG.Quad.nonneg₂_sound`, `TDCSG.Quad.nonneg₃_sound`: the tests
  are sound.
-/

@[expose] public section

namespace TDCSG

/-- If `x + y √h` has nonnegative parts, or parts of opposite signs with the nonnegative one
dominating in square, then it is nonnegative. -/
theorem nonneg_add_mul_sqrt {x y h : ℝ} (hh : 0 ≤ h)
    (H : 0 ≤ x ∧ 0 ≤ y ∨ 0 ≤ x ∧ 0 ≤ -y ∧ 0 ≤ x * x - y * y * h ∨
      0 ≤ -x ∧ 0 ≤ y ∧ 0 ≤ y * y * h - x * x) :
    0 ≤ x + y * √h := by
  have hs := Real.sqrt_nonneg h
  have hs2 := Real.mul_self_sqrt hh
  rcases H with ⟨hx, hy⟩ | ⟨hx, hy, hxy⟩ | ⟨hx, hy, hxy⟩
  · positivity
  · by_contra hneg
    push Not at hneg
    have h1 : 0 < x - y * √h := by nlinarith [mul_nonneg (neg_nonneg.1 hy |> neg_nonneg.2) hs]
    nlinarith [mul_pos h1 (neg_pos.2 hneg)]
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_nonneg hy hs]

/-- From a sign test `nn` on a ring, the test for `0 ≤ x + y √h` of
`TDCSG.nonneg_add_mul_sqrt`. -/
def sqrtNonneg {R : Type*} [Neg R] [Sub R] [Mul R] (nn : R → Bool) (x y h : R) : Bool :=
  nn x && nn y || nn x && nn (-y) && nn (x * x - y * y * h) ||
    nn (-x) && nn y && nn (y * y * h - x * x)

/-- The soundness of `TDCSG.sqrtNonneg`, along a map `e` to `ℝ` preserving the operations. -/
theorem sqrtNonneg_sound {R : Type*} [Neg R] [Sub R] [Mul R] {nn : R → Bool} {e : R → ℝ}
    (hnn : ∀ x, nn x = true → 0 ≤ e x) (hneg : ∀ x, e (-x) = -e x)
    (hsub : ∀ x y, e (x - y) = e x - e y) (hmul : ∀ x y, e (x * y) = e x * e y) {x y h : R}
    (hh : 0 ≤ e h) (H : sqrtNonneg nn x y h = true) : 0 ≤ e x + e y * √(e h) := by
  simp only [sqrtNonneg, Bool.or_eq_true, Bool.and_eq_true] at H
  apply nonneg_add_mul_sqrt hh
  rcases H with (⟨h₁, h₂⟩ | ⟨⟨h₁, h₂⟩, h₃⟩) | ⟨⟨h₁, h₂⟩, h₃⟩
  · exact Or.inl ⟨hnn _ h₁, hnn _ h₂⟩
  · refine Or.inr (Or.inl ⟨hnn _ h₁, ?_, ?_⟩)
    · simpa [hneg] using hnn _ h₂
    · simpa [hsub, hmul] using hnn _ h₃
  · refine Or.inr (Or.inr ⟨?_, hnn _ h₂, ?_⟩)
    · simpa [hneg] using hnn _ h₁
    · simpa [hsub, hmul] using hnn _ h₃

/-- The element `a + b √m` of `ℤ[√m]`, by its integer coordinates. -/
@[ext]
structure Quad (m : ℕ) where
  /-- The rational coordinate. -/
  a : ℤ
  /-- The coordinate of `√m`. -/
  b : ℤ
  deriving DecidableEq, Repr

namespace Quad

variable {m : ℕ}

instance : Zero (Quad m) := ⟨⟨0, 0⟩⟩
instance : Add (Quad m) := ⟨fun x y ↦ ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg (Quad m) := ⟨fun x ↦ ⟨-x.a, -x.b⟩⟩
instance : Sub (Quad m) := ⟨fun x y ↦ ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Mul (Quad m) := ⟨fun x y ↦ ⟨x.a * y.a + m * x.b * y.b, x.a * y.b + x.b * y.a⟩⟩

/-- The real number `a + b √m`. -/
noncomputable def toReal (x : Quad m) : ℝ := x.a + x.b * √(m : ℝ)

@[simp] theorem toReal_zero : (0 : Quad m).toReal = 0 := by simp [toReal, show (0 : Quad m) =
  ⟨0, 0⟩ from rfl]

@[simp] theorem toReal_add (x y : Quad m) : (x + y).toReal = x.toReal + y.toReal := by
  simp only [toReal, show x + y = ⟨x.a + y.a, x.b + y.b⟩ from rfl]
  push_cast
  ring

@[simp] theorem toReal_neg (x : Quad m) : (-x).toReal = -x.toReal := by
  simp only [toReal, show -x = ⟨-x.a, -x.b⟩ from rfl]
  push_cast
  ring

@[simp] theorem toReal_sub (x y : Quad m) : (x - y).toReal = x.toReal - y.toReal := by
  simp only [toReal, show x - y = ⟨x.a - y.a, x.b - y.b⟩ from rfl]
  push_cast
  ring

@[simp] theorem toReal_mul (x y : Quad m) : (x * y).toReal = x.toReal * y.toReal := by
  simp only [toReal, show x * y = ⟨x.a * y.a + m * x.b * y.b, x.a * y.b + x.b * y.a⟩ from rfl]
  have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) m)
  push_cast
  linear_combination (-(x.b : ℝ)) * y.b * this

/-- The exact test for `0 ≤ a + b √m`. -/
def nonneg (x : Quad m) : Bool :=
  sqrtNonneg (fun z : ℤ ↦ decide (0 ≤ z)) x.a x.b (m : ℤ)

theorem nonneg_toReal {x : Quad m} (h : x.nonneg = true) : 0 ≤ x.toReal := by
  have := sqrtNonneg_sound (nn := fun z : ℤ ↦ decide (0 ≤ z)) (e := fun z : ℤ ↦ (z : ℝ))
    (by simp) (by simp) (by simp) (by simp) (by simp) h
  simpa [toReal] using this

/-- The exact test for `0 ≤ x + y √h`. -/
def nonneg₂ (x y h : Quad m) : Bool := sqrtNonneg nonneg x y h

theorem nonneg₂_sound {x y h : Quad m} (hh : 0 ≤ h.toReal) (H : nonneg₂ x y h = true) :
    0 ≤ x.toReal + y.toReal * √h.toReal :=
  sqrtNonneg_sound (nn := nonneg) (e := toReal) (fun _ ↦ nonneg_toReal) toReal_neg toReal_sub
    toReal_mul hh H

/-- The exact test for `0 ≤ x + y √h₁ + z √h₂`: the test of `TDCSG.sqrtNonneg` over
`ℤ[√m][√h₁]`, with the signs there decided by `TDCSG.Quad.nonneg₂`. -/
def nonneg₃ (x y z h₁ h₂ : Quad m) : Bool :=
  nonneg₂ x y h₁ && z.nonneg ||
    nonneg₂ x y h₁ && (-z).nonneg &&
      nonneg₂ (x * x + y * y * h₁ - z * z * h₂) (x * y + x * y) h₁ ||
    nonneg₂ (-x) (-y) h₁ && z.nonneg &&
      nonneg₂ (z * z * h₂ - x * x - y * y * h₁) (-(x * y + x * y)) h₁

theorem nonneg₃_sound {x y z h₁ h₂ : Quad m} (hh₁ : 0 ≤ h₁.toReal) (hh₂ : 0 ≤ h₂.toReal)
    (H : nonneg₃ x y z h₁ h₂ = true) :
    0 ≤ x.toReal + y.toReal * √h₁.toReal + z.toReal * √h₂.toReal := by
  have hs := Real.mul_self_sqrt hh₁
  simp only [nonneg₃, Bool.or_eq_true, Bool.and_eq_true] at H
  apply nonneg_add_mul_sqrt hh₂
  rcases H with (⟨h₁', h₂'⟩ | ⟨⟨h₁', h₂'⟩, h₃'⟩) | ⟨⟨h₁', h₂'⟩, h₃'⟩
  · exact Or.inl ⟨nonneg₂_sound hh₁ h₁', nonneg_toReal h₂'⟩
  · refine Or.inr (Or.inl ⟨nonneg₂_sound hh₁ h₁', by simpa using nonneg_toReal h₂', ?_⟩)
    have := nonneg₂_sound hh₁ h₃'
    simp only [toReal_add, toReal_sub, toReal_mul] at this
    linear_combination this - y.toReal * y.toReal * hs
  · refine Or.inr (Or.inr ⟨?_, nonneg_toReal h₂', ?_⟩)
    · have := nonneg₂_sound hh₁ h₁'
      simp only [toReal_neg] at this
      linarith
    · have := nonneg₂_sound hh₁ h₃'
      simp only [toReal_add, toReal_sub, toReal_mul, toReal_neg] at this
      linear_combination this + y.toReal * y.toReal * hs

end Quad

end TDCSG

end
