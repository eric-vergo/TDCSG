/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import TDCSGFigures.Data

/-!
# Exact points for the figures of Part II

Two exact representations of points beyond `ℤ[ζ₅]`, for the figures of chapters 4 to 7:

* `ZetaFrac`: an element of `ℤ[ζ₅]` over a positive integer denominator, such as the point
  `(y + 1) / 2` of the halved starting frame or a label's projection moved by a rational shift.
  Its real part and its squared modulus are exact in `ℚ(√5)`.
* `Surd`: a real number `a + ∑ sᵢ √Qᵢ` with `a` and the radicands `Qᵢ ≥ 0` in `ℚ(√5)` and signs
  `sᵢ = ±1`, and `SurdPoint`, a point with two such coordinates. The tip of the lens of chapter 5
  at a rational radius is such a point. Its relations to the disks and cuts are decided in
  `ℚ(√5)` by squaring (`sqrtLt`, `sqrtEq`), from the radicands.

Floating point enters only where PILean converts a point to page coordinates
(`PILean.Exact.PlanePoint.toPoint`), as for the points of `ℤ[ζ₅]`.
-/

namespace TDCSGFigures

open PILean PILean.Exact

/-! ### Elements of `ℤ[ζ₅]` over a denominator -/

/-- The number `num / den` of `ℚ(ζ₅)`, `den > 0`. -/
structure ZetaFrac where
  /-- The numerator. -/
  num : Zeta5
  /-- The denominator, positive. -/
  den : Nat := 1

namespace ZetaFrac

/-- An element of `ℤ[ζ₅]`. -/
def ofZeta (z : Zeta5) : ZetaFrac := ⟨z, 1⟩

/-- The real part, exact in `ℚ(√5)`. -/
def realPart (z : ZetaFrac) : QSqrt5 := z.num.realPart * rat (1 / z.den)

/-- The squared modulus, exact in `ℚ(√5)`. -/
def normSq (z : ZetaFrac) : QSqrt5 := z.num.normSq * rat (1 / (z.den * z.den))

/-- The difference. -/
def sub (z w : ZetaFrac) : ZetaFrac :=
  ⟨z.num * Zeta5.ofInt w.den - w.num * Zeta5.ofInt z.den, z.den * w.den⟩

instance : Sub ZetaFrac := ⟨sub⟩

/-- The number moved by the rational `q` along the real axis: `z + q`. -/
def shiftRe (z : ZetaFrac) (q : Rat) : ZetaFrac :=
  ⟨z.num * Zeta5.ofInt (q.den : Int) + Zeta5.ofInt (q.num * z.den), z.den * q.den⟩

end ZetaFrac

/-- A number of `ℚ(ζ₅)` as a point: the balls of its numerator divided by the denominator. -/
instance : PlanePoint ZetaFrac where
  re z k := (QSqrt.ball z.num.realPart k).smul (1 / z.den)
  im z k := (Zeta5.imBall z.num k).smul (1 / z.den)

/-! ### Sums of square roots -/

/-- The real number `a + ∑ sᵢ √Qᵢ`: `a` in `ℚ(√5)` and each term a sign `sᵢ` and a radicand
`Qᵢ ≥ 0` in `ℚ(√5)` (`√Qᵢ` is read as `√(max Qᵢ 0)`, as in `PILean.Exact.SqrtOf`). -/
structure Surd where
  /-- The part in `ℚ(√5)`. -/
  base : QSqrt5 := ⟨0, 0⟩
  /-- The signed square roots. -/
  roots : List (Int × QSqrt5) := []

/-- `a` as a `Surd`. -/
def Surd.ofQ (a : QSqrt5) : Surd := { base := a }

/-- A ball around `a + ∑ sᵢ √Qᵢ` of radius at most `2⁻ᵏ`: each of the `m` terms at precision
`k + m + 1`, so that the radii add up to less than `2⁻ᵏ`. -/
instance : RealValue Surd where
  ball s k :=
    let k' := k + s.roots.length + 1
    s.roots.foldl (fun acc (sgn, q) =>
      acc.add ((RealValue.ball (SqrtOf.mk q) k').smul (sgn : Rat))) (QSqrt.ball s.base k')

/-- A point whose coordinates are `Surd`s. -/
structure SurdPoint where
  /-- The abscissa (real part). -/
  re : Surd
  /-- The ordinate (imaginary part). -/
  im : Surd

instance : PlanePoint SurdPoint where
  re p k := RealValue.ball p.re k
  im p k := RealValue.ball p.im k

/-- Whether `√Q < K` for `Q ≥ 0`: exactly when `K > 0` and `Q < K²`. -/
def sqrtLt (Q K : QSqrt5) : Bool := QSqrt.lt ⟨0, 0⟩ K && QSqrt.lt Q (K * K)

/-- Whether `√Q = K` for `Q ≥ 0`: exactly when `K ≥ 0` and `Q = K²`. -/
def sqrtEq (Q K : QSqrt5) : Bool := QSqrt.le ⟨0, 0⟩ K && Q == K * K

/-! ### Decimal text -/

/-- The decimal text of a real value rounded to `d` places, with a true minus sign: for labels and
slider values only, never for a decision. -/
def decimalText {α : Type} [RealValue α] (a : α) (d : Nat := 2) : String :=
  let scale : Int := 10 ^ d
  let c := (RealValue.ball a 64).centre
  let n := (c * scale + 1 / 2).floor
  let sign := if n < 0 then "−" else ""
  let m := n.natAbs
  let ip := m / scale.toNat
  let fp := toString (m % scale.toNat)
  let fp := String.ofList (List.replicate (d - fp.length) '0') ++ fp
  if d == 0 then s!"{sign}{ip}" else s!"{sign}{ip}.{fp}"

end TDCSGFigures
