/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Tower
import TDCSGCompute.Disk

/-!
# Exact geometry of intersection points of equal circles

All circles here have the same radius `r`, with `r² = ρ = R / q` exact (`R ∈ ℤ[ζ_n]⁺`, `q ≥ 1`),
and centres in `ℤ[ζ_n]`. This module is the exact layer shared by the certificate generator
(`TDCSGCompute.Closure`) and the independent checker (`TDCSGCompute.CertCheck`).

## Symbols

A point of the circle `C(c)` about `c` is named by a *symbol* `(e, s)`, `e ∈ ℤ[ζ_n]`, `s = ±1`:
the intersection point of `C(c)` with `C(e)` on side `s`,

`P = c + (d / 2) (1 + i s h)`,  `d = e - c`,  `h = √(4ρ / N - 1)`,  `N = |d|²`.

It is defined when the two circles cross, i.e. `N ≠ 0` and `4ρ - N > 0`, equivalently
`G₀ = 4R - qN > 0`; `validSym` checks this exactly. Walking counterclockwise around `C(c)`, the
arc of `C(c)` inside the closed disk of radius `r` about `p` runs from `(p, -1)` to `(p, +1)`,
because `P - c` has argument `arg d + s β` with `β = arccos (√N / 2r) ∈ (0, π/2)`.

A rotation `z ↦ p + ζ^k (z - p)` maps the symbol `(e, s)` on `C(c)` to the symbol
`(p + ζ^k (e - p), s)` on the image circle, since it preserves orientation and intersections.

Different symbols can name the same point (three circles through one point). Equality of points
is therefore never decided by comparing symbols, except that identical symbols on the same circle
name the same point.

## The direction vector, with integral coordinates

`P - c = (1 / 2qN) · d · (qN + i s √H)` with `H = q N G₀ ∈ ℤ[ζ_n]⁺`, `H > 0`, because
`h = √(G₀ / qN) = √H / qN`. The factor `1 / 2qN` is positive, so `U = d (qN + i s √H)` has the
same direction as `P - c`.

To write `Re U` and `Im U` over `ℤ[ζ_n]⁺`, let `ω = ζ - ζ⁻¹ = 2i sin (2π/n)` and
`S₄ = -ω² = 4 sin² (2π/n) ∈ ℤ[ζ_n]⁺`, `S₄ > 0` for `n ≥ 3`. For `z ∈ ℤ[ζ_n]`, put
`A(z) = z + z̄ = 2 Re z` and `T(z) = -(z - z̄) ω = 4 sin (2π/n) Im z = 2 √S₄ Im z`; both are in
`ℤ[ζ_n]⁺`. Multiplying by the positive constant `2 √S₄`:

`X = 2√S₄ Re U = √S₄ · qN · A(d) - s T(d) √H`,
`Y = 2√S₄ Im U = qN · T(d) + s A(d) √S₄ √H`,

elements of the tower `ℚ(ζ_n)⁺(√S₄, √H)` of `TDCSGCompute.Tower` with integral coefficients.
`(X, Y)` is a positive multiple of `P - c`, the multiple depending on the point.

## Order around a circle

Angles about `c` are taken in `[0, 2π)`. The *half* of a point is `upper` (angle in `[0, π)`)
when `Y > 0`, or `Y = 0` and `X > 0`, and `lower` otherwise. Two points of `C(c)` in the same half
have angles differing by less than `π`, so their order is the sign of the cross product
`X₁ Y₂ - Y₁ X₂` (positive: the first comes first), and they are equal exactly when it is `0`;
points in different halves are ordered by their halves and are distinct. Positive rescaling of
either vector does not change any of these signs. The cross product lies in the tower over
`(S₄, H₁, H₂)` and its sign is decided exactly by `Tower.sign`. This gives `cmpExact`, the exact
total order of the points of one circle by angle, in which `.eq` means *the same point*.

## A certified enclosure first

Exact tower signs are expensive, so `exactPt` also encloses the values of `X` and `Y` in balls
(`TDCSGCompute.Ball`: fixed-point integer arithmetic with a proven enclosure invariant, no
floating point) at 96 bits, from the certified cosine table (rescaled, which keeps it an
enclosure), `Ball.sqrt?`
for `√S₄` and `√H`, and `Ball.mul`. A half or a cross-product sign is taken from a ball only when
the ball excludes `0`; then it is the true sign. Otherwise the exact tower sign is computed. The
result is the same either way; only the cost differs.

`CircleCtx.rot` is the rotation about a disk centre used by the generators.
-/

namespace TDCSGCompute

/-- A symbol `(e, s)`: on the circle about `c`, the intersection point with the circle about `e`
on side `s = +1` (`plus`) or `s = -1`. -/
structure Sym where
  /-- The centre of the other circle. -/
  e : Elem
  /-- The side: `true` for `s = +1`. -/
  plus : Bool
  deriving BEq, Hashable, Inhabited, Repr

/-- The side as an integer `±1`. -/
def Sym.side (s : Sym) : Int := if s.plus then 1 else -1

/-- The fixed data of a radius: the ring, `r² = R / q`, and the constants of the module
docstring. -/
structure CircleCtx where
  /-- The ring `ℤ[ζ_n]`. -/
  F : CycField
  /-- Exact signs of real elements. -/
  S : RealSign
  /-- The squared radius `R / q`. -/
  r2 : RadiusSq
  /-- `4R`. -/
  R4 : Elem
  /-- `ω = ζ - ζ⁻¹`. -/
  omega : Elem
  /-- `S₄ = -ω² = 4 sin² (2π/n)`. -/
  S4 : Elem
  /-- The left disk centre `-1`. -/
  left : Elem
  /-- The right disk centre `+1`. -/
  right : Elem
  /-- The precision of the enclosures (bits). -/
  ballPrec : Nat
  /-- Enclosures of `cos (2πk/n)` at precision `ballPrec`. -/
  cosBall : Array Ball

/-- Set up the constants for `r² = r2`. -/
def CircleCtx.make (F : CycField) (r2 : RadiusSq) : CircleCtx :=
  let omega := F.sub (F.zetaPow 1) (F.zetaPow (-1))
  { F, S := RealSign.make F, r2, R4 := F.smul 4 r2.num, omega, S4 := F.neg (F.mul omega omega),
    left := F.ofInt (-1), right := F.ofInt 1, ballPrec := min 96 F.basePrec,
    cosBall := F.cosB.map (·.rescale (F.basePrec - min 96 F.basePrec)) }

namespace CircleCtx

variable (C : CircleCtx)

/-- `4R - q |x - y|²`, which has the sign of `4ρ - |x - y|²`: positive when the circles about `x`
and `y` cross (for `x ≠ y`), zero when they are tangent, negative when they are disjoint. -/
def gap (x y : Elem) : Elem :=
  C.F.sub C.R4 (C.F.smul (C.r2.den : Int) (C.F.normSq (C.F.sub x y)))

/-- The exact sign of `gap x y`. -/
def gapSign (x y : Elem) : Except String Int :=
  match C.S.sign (C.gap x y) with
  | some s => .ok s
  | none => .error "sign determination failed (precision bound exceeded)"

/-- Whether `ρ > 1`, decided exactly (`R - q > 0`). -/
def radiusAboveOne : Except String Bool :=
  match C.S.sign (C.F.addInt C.r2.num (-(C.r2.den : Int))) with
  | some s => .ok (s > 0)
  | none => .error "sign determination failed (precision bound exceeded)"

/-- The rotation `z ↦ p + ζ^k (z - p)` for `k = ±1`. -/
def rot (p : Elem) (k : Int) (z : Elem) : Elem :=
  let w := C.F.sub z p
  C.F.add p (if k > 0 then C.F.mulZeta w else C.F.mulZetaInv w)

/-- The rotation applied to a symbol. -/
def rotSym (p : Elem) (k : Int) (s : Sym) : Sym := { s with e := C.rot p k s.e }

/-- Check exactly that the symbol `s` names a point of the circle about `c`: the circles about `c`
and `s.e` cross. -/
def validSym (c : Elem) (s : Sym) : Except String Unit := do
  if C.F.isZero (C.F.sub s.e c) then throw "symbol names the centre of its own circle"
  let g ← C.gapSign c s.e
  if g == 0 then throw "symbol circle is tangent to the carrying circle"
  if g < 0 then throw "symbol circle does not meet the carrying circle"

/-- The exact direction data of a point (see the module docstring). -/
structure ExactPt where
  /-- `X` over the radicands `(S₄, H)`. -/
  X : TowerElem
  /-- `Y` over the radicands `(S₄, H)`. -/
  Y : TowerElem
  /-- The radicand `H = q N G₀ > 0`. -/
  H : Elem
  /-- Whether the point is in the lower half (angle in `[π, 2π)`). -/
  lower : Bool
  /-- An enclosure of `X` at precision `ballPrec`, if one could be formed. -/
  bx : Option Ball
  /-- An enclosure of `Y` at precision `ballPrec`. -/
  by_ : Option Ball
  deriving Inhabited

/-- Exact direction data of the point named by `s` on the circle about `c`. Fails if the symbol
is not valid. -/
def exactPt (c : Elem) (s : Sym) : Except String ExactPt := do
  let F := C.F
  C.validSym c s
  let d := F.sub s.e c
  let q : Int := C.r2.den
  let N := F.normSq d
  let qN := F.smul q N
  let G0 := F.sub C.R4 qN
  let H := F.mul qN G0
  let dc := F.conj d
  let A := F.add d dc
  let T := F.neg (F.mul (F.sub d dc) C.omega)
  let sg := s.side
  let X : TowerElem := #[F.zero, F.mul qN A, F.smul (-sg) T, F.zero]
  let Y : TowerElem := #[F.mul qN T, F.zero, F.zero, F.smul sg A]
  let rs := #[C.S4, H]
  -- enclosures of `X` and `Y`
  let p := C.ballPrec
  let bl (z : Elem) : Ball := F.realBallWith C.cosBall z
  let (bx, by_) : Option Ball × Option Ball :=
    match (bl C.S4).sqrt? p, (bl H).sqrt? p with
    | some rS, some rH =>
      let x := (Ball.mul p rS (bl X[1]!)).add (Ball.mul p rH (bl X[2]!))
      let y := (bl Y[0]!).add (Ball.mul p (Ball.mul p rS rH) (bl Y[3]!))
      (some x, some y)
    | _, _ => (none, none)
  let ballSign (b : Option Ball) : Int := match b with
    | some b => b.sign
    | none => 0
  let sYb := ballSign by_
  let sY ← if sYb != 0 then pure sYb else
    match Tower.sign C.S rs Y with
    | some v => pure v
    | none => throw "sign determination failed (precision bound exceeded)"
  let lower : Bool ← if sY != 0 then pure (decide (sY < 0)) else
    match Tower.sign C.S rs X with
    | some v => pure (decide (v ≤ 0))
    | none => throw "sign determination failed (precision bound exceeded)"
  return { X := X, Y := Y, H := H, lower := lower, bx := bx, by_ := by_ }

/-- Re-index a tower element over `(S₄, H)` as one over `(S₄, H₁, H₂)`, with `H` in position
`slot` (1 or 2). -/
def embed3 (F : CycField) (slot : Nat) (x : TowerElem) : TowerElem := Id.run do
  let mut out := Array.replicate 8 F.zero
  for i in [0:4] do
    let j := (i % 2) + (if i / 2 == 1 then 2 ^ slot else 0)
    out := out.set! j x[i]!
  return out

/-- The exact sign of the cross product `X₁ Y₂ - Y₁ X₂` of two points of one circle. -/
def crossSign (p p' : ExactPt) : Except String Int := do
  let F := C.F
  match p.bx, p.by_, p'.bx, p'.by_ with
  | some x1, some y1, some x2, some y2 =>
    let pr := C.ballPrec
    let s := ((Ball.mul pr x1 y2).sub (Ball.mul pr y1 x2)).sign
    if s != 0 then return s
  | _, _, _, _ => pure ()
  let rs := #[C.S4, p.H, p'.H]
  let x1 := embed3 F 1 p.X
  let y1 := embed3 F 1 p.Y
  let x2 := embed3 F 2 p'.X
  let y2 := embed3 F 2 p'.Y
  let cr := Tower.sub F (Tower.mul F rs x1 y2) (Tower.mul F rs y1 x2)
  match Tower.sign C.S rs cr with
  | some v => return v
  | none => throw "sign determination failed (precision bound exceeded)"

/-- The exact order by angle about the common centre: `.eq` exactly when the two points are the
same point. -/
def cmpExact (p p' : ExactPt) : Except String Ordering := do
  if p.lower != p'.lower then return (if p.lower then .gt else .lt)
  let s ← C.crossSign p p'
  return (if s > 0 then .lt else if s == 0 then .eq else .gt)

end CircleCtx

/-- An element as comma-separated coefficients. -/
def elemToString (x : Elem) : String := ",".intercalate (x.toList.map toString)

/-- Lexicographic order on coefficient vectors (used only to order output deterministically). -/
def elemLexLt (x y : Elem) : Bool := Id.run do
  for i in [0:min x.size y.size] do
    if x[i]! < y[i]! then return true
    if x[i]! > y[i]! then return false
  return x.size < y.size

end TDCSGCompute
