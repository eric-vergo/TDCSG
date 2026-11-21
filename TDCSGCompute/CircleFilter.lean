/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.CirclePoint

/-!
# A certified floating-point filter for the order of points on a circle

The certificate generator compares intersection points on a circle millions of times. This
module decides most comparisons in double precision **with a rigorous error bound**, and reports
*undecided* otherwise, in which case the caller uses the exact comparison of
`TDCSGCompute.CirclePoint`. The independent checker does not use this module.

## The computed quantities

For the point named by `(e, s)` on the circle about `c` (`d = e - c`, `N = |d|²`), the filter
computes the vector `V = d · (√N + i s √(4ρ - N))`, a positive multiple of `P - c` (it is
`2√N (P - c)`), as `V_x = d_x √N - s d_y √G`, `V_y = d_y √N + s d_x √G` with `G = 4ρ - N`. The
half of the point is the sign of `V_y` (and of `V_x` if `V_y = 0`), and the order of two points in
the same half is the sign of `V_x V'_y - V_y V'_x`, exactly as in `TDCSGCompute.CirclePoint`;
positive rescaling does not change these signs.

## Running error bounds

Each computed quantity is a pair `(v, E)` of doubles with the invariant `|v - x| ≤ E`, `x` the
exact real value. Let `u = 2⁻⁵³`. The inputs:

* `d_x = Σ d_i cos (2πi/n)`, `d_y = Σ d_i sin (2πi/n)` from the certified tables of
  `TDCSGCompute.Field`, with the bound `2 ((φ(n) + 2) u Σ |d_i| |t_i| + δ Σ |d_i|)` justified in
  `TDCSGCompute.Disk` (there with one more summand `± 1`). Used only when every `|d_i| < 2⁵³`.
* `4ρ` as `4 r̂²`, `|r̂² - ρ| ≤ ε_r` certified by `Ball.toFloatCert` (scaling by 4 is exact).

The operations, assuming IEEE 754 arithmetic with correctly rounded `+`, `-`, `×`, `/` and `√`
(the C `sqrt` is correctly rounded under IEC 60559):

* `a ± b`: `v = fl(a ± b)`, `E = E_a + E_b + 2u|v|`;
* `a × b`: `v = fl(a b)`, `E = |a| E_b + |b| E_a + E_a E_b + 2u|v|`;
* `√a` for an exact value `a ≥ 0`: if `v_a > E_a`, `v = fl(√v_a)` and
  `E = E_a / v + 2u|v|` (from `|√a - √v_a| = |a - v_a| / (√a + √v_a) ≤ E_a / √v_a`); otherwise
  `a ≤ 2 E_a`, `v = fl(√max(v_a, 0))` and `E = √(2 E_a)`.

Here `2u|v|` bounds the rounding error `u |exact result|` of the operation, since
`|exact| ≤ |v| / (1 - u)`. Each bound is computed in floating point from nonnegative terms; the
result is multiplied by `κ = 1 + 2⁻⁴⁰`, which exceeds the at most six roundings `(1 - u)⁻⁶` of the
bound's own evaluation, and `η = 2⁻¹⁰⁰⁰` is added to cover underflow (absolute error at most
`2⁻¹⁰⁷⁴` per operation). Fused multiply-adds, if the C compiler forms them, remove roundings and
leave the bounds valid. A sign is taken from `v` only if `v` and `E` are finite and `|v| > E`;
then `x` has the sign of `v`. Non-finite values are never decided.
-/

namespace TDCSGCompute

/-- A double with a certified bound on its distance to an exact real value. -/
structure FE where
  /-- The computed value. -/
  v : Float
  /-- The error bound. -/
  e : Float
  deriving Inhabited

/-- The safety factor `κ = 1 + 2⁻⁴⁰` for evaluating bounds in floating point. -/
def feKappa : Float := 1 + (1.0 : Float).scaleB (-40)

/-- The underflow allowance `η = 2⁻¹⁰⁰⁰`. -/
def feEta : Float := (1.0 : Float).scaleB (-1000)

/-- Twice the unit roundoff. -/
def feTwoU : Float := (1.0 : Float).scaleB (-52)

namespace FE

/-- Sum. -/
@[inline] def add (a b : FE) : FE :=
  let v := a.v + b.v
  ⟨v, (a.e + b.e + feTwoU * v.abs) * feKappa + feEta⟩

/-- Difference. -/
@[inline] def sub (a b : FE) : FE :=
  let v := a.v - b.v
  ⟨v, (a.e + b.e + feTwoU * v.abs) * feKappa + feEta⟩

/-- Product. -/
@[inline] def mul (a b : FE) : FE :=
  let v := a.v * b.v
  ⟨v, (a.v.abs * b.e + b.v.abs * a.e + a.e * b.e + feTwoU * v.abs) * feKappa + feEta⟩

/-- Square root of a quantity whose exact value is known to be `≥ 0`. -/
@[inline] def sqrtNonneg (a : FE) : FE :=
  if a.v > a.e then
    let v := a.v.sqrt
    ⟨v, (a.e / v + feTwoU * v) * feKappa + feEta⟩
  else
    let v := (if a.v > 0 then a.v else 0).sqrt
    ⟨v, ((2 * a.e).sqrt + feTwoU * v) * feKappa + feEta⟩

/-- The certified sign (`some (-1)` or `some 1`), or `none` if undecided. -/
@[inline] def sign? (a : FE) : Option Int :=
  if a.v.isFinite && a.e.isFinite && a.v.abs > a.e then some (if a.v > 0 then 1 else -1)
  else none

end FE

/-- Float data of a radius for the filter. -/
structure FilterCtx where
  /-- The exact data. -/
  C : CircleCtx
  /-- `4 r̂²` with its certified error. -/
  rho4 : FE
  /-- The dot-product constant `(φ(n) + 2) u`. -/
  gam : Float

/-- Set up the filter for a radius. -/
def FilterCtx.make (C : CircleCtx) : FilterCtx :=
  let T := DiskTest.make C.F C.r2
  { C, rho4 := ⟨4 * T.r2F, 4 * T.r2E⟩, gam := filterGamma C.F }

/-- The filtered direction vector of a point. -/
structure PointF where
  /-- `V_x`. -/
  x : FE
  /-- `V_y`. -/
  y : FE
  /-- Whether the inputs were small enough for the filter. -/
  ok : Bool
  deriving Inhabited

/-- The filtered direction vector of the point named by `s` on the circle about `c`. The symbol
must be valid (the exact value `4ρ - N` is then positive). -/
def FilterCtx.point (FC : FilterCtx) (c : Elem) (s : Sym) : PointF :=
  let F := FC.C.F
  let d := F.sub s.e c
  let fd := filterData F d
  let δ := F.trigErr
  let dx : FE := ⟨fd.x, fl2 * (FC.gam * fd.ax + δ * fd.s1)⟩
  let dy : FE := ⟨fd.y, fl2 * (FC.gam * fd.ay + δ * fd.s1)⟩
  let N := (dx.mul dx).add (dy.mul dy)
  let sN := N.sqrtNonneg
  let sG := (FC.rho4.sub N).sqrtNonneg
  let t1 := dx.mul sN
  let t2 := dy.mul sG
  let t3 := dy.mul sN
  let t4 := dx.mul sG
  if s.plus then { x := t1.sub t2, y := t3.add t4, ok := !fd.big }
  else { x := t1.add t2, y := t3.sub t4, ok := !fd.big }

/-- The certified half of a point (`some true` for the lower half), or `none` if undecided. -/
def PointF.lower? (p : PointF) : Option Bool :=
  if !p.ok then none else
  match p.y.sign? with
  | some s => some (s < 0)
  | none => none

/-- The certified sign of the cross product of two points of one circle, or `none`. -/
def PointF.cross? (p q : PointF) : Option Int :=
  if !p.ok || !q.ok then none else ((p.x.mul q.y).sub (p.y.mul q.x)).sign?

end TDCSGCompute
