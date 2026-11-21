/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Field

/-!
# Certified membership in the closed disks

The squared radius is an exact element `r² = num / den` of `ℚ(ζ_n)⁺`, with `num ∈ ℤ[ζ_n]⁺` and a
positive integer `den`. A point `z ∈ ℤ[ζ_n]` lies in the left disk `|z + 1| ≤ r` (respectively the
right disk `|z - 1| ≤ r`) exactly when `Δ = r² - |w|² ≥ 0` for `w = z + 1` (respectively `z - 1`).
Every decision below is a certified decision of the sign of `Δ`; no floating-point comparison is
trusted without an error bound.

## Floating-point filter

Let `u = 2⁻⁵³` be the unit roundoff, `τ_i = cos (2πi/n)`, `υ_i = sin (2πi/n)`, and let `t_i`, `s_i`
be the doubles `cosF[i]`, `sinF[i]` with `|t_i - τ_i|, |s_i - υ_i| ≤ δ` (`δ = trigErr`, certified in
`TDCSGCompute.Field` from the exact bit patterns). The filter is used only when every coefficient
satisfies `|c_i| < 2⁵³`, so each `c_i` converts to a double exactly.

1. `X̂ = fl(∑ c_i t_i ± 1)` is a recursive dot product of `d + 1` terms, so by the standard bound
   (Higham, *Accuracy and Stability of Numerical Algorithms*, (3.5))
   `|X̂ - (∑ c_i t_i ± 1)| ≤ γ_{d+1} (∑ |c_i| |t_i| + 1)`, `γ_k = k u / (1 - k u)`. Together with
   `|∑ c_i (t_i - τ_i)| ≤ δ ∑ |c_i|` this bounds `|X̂ - Re w|` by
   `e_X = 2 ((d + 2) u (AX + 1) + δ S₁)` where `AX = fl(∑ |c_i| |t_i|)`, `S₁ = fl(∑ |c_i|)`. The
   factor `2` absorbs `1 / (1 - k u)`, the rounding of `AX` and `S₁` (relative error at most
   `γ_d`), and the rounding in evaluating `e_X` itself; it requires only `d u ≪ 1`. The same holds
   for `Ŷ = fl(∑ c_i s_i)` and `e_Y`.
2. `Q̂ = fl(fl(X̂²) + fl(Ŷ²))` satisfies `|Q̂ - (X̂² + Ŷ²)| ≤ γ₂ (X̂² + Ŷ²)` and
   `|X̂² - (Re w)²| ≤ e_X (2 |X̂| + e_X)`, likewise for `Y`. So
   `E_Q = 2 (3 u (X̂² + Ŷ²) + e_X (2 |X̂| + e_X) + e_Y (2 |Ŷ| + e_Y))` bounds `|Q̂ - |w|²|` with
   the same slack factor `2`.
3. `r̂²` is a double with `|r̂² - r²| ≤ ε_r`, certified like the tables (`Ball.toFloatCert`).
4. `Δ̂ = fl(r̂² - Q̂)` is a correctly rounded difference, so `sign Δ̂ = sign (r̂² - Q̂)` and
   `|r̂² - Q̂| ≥ |Δ̂| / (1 + u)`. If `|Δ̂| > B = 2 (ε_r + E_Q)` then `|r̂² - Q̂|` exceeds the total
   error `ε_r + |Q̂ - |w|²|`, so `sign Δ = sign Δ̂`.

Fused multiply-adds, if the C compiler introduces them, only remove roundings, and the bounds
above still hold. Non-finite intermediate values send the point to the exact path.

## Scaled disks

Points with a denominator, `z = w / M` with `w ∈ ℤ[ζ_n]` and an integer `M ≥ 1`, are handled in
the coordinate `w`: `|z ± 1| ≤ r` exactly when `|w ± M|² ≤ M² r²`. So `DiskTest.make F (M² r²)`
with `side = ±M` decides membership of `z`. The filter bound above holds with `|side|` in place of
`1` in `e_X` (the term `± side` is one more exactly representable summand), and is used only when
`|M| < 2⁵³`.

## Exact path

When the filter does not decide, `D = num - den * |w|²` is computed exactly in `ℤ[ζ_n]` (`normSq`),
`D = 0` is tested exactly (unique representation), and otherwise its sign is decided by
`CycField.signReal`, whose correctness argument is in `TDCSGCompute.Field`. `D = 0` means `z` lies
on the boundary circle, which belongs to the closed disk.
-/

namespace TDCSGCompute

/-- An exact squared radius `num / den`, with `num ∈ ℤ[ζ_n]⁺` and `den > 0`. -/
structure RadiusSq where
  /-- The numerator, a real element of `ℤ[ζ_n]`. -/
  num : Elem
  /-- The positive integer denominator. -/
  den : Nat
  deriving Inhabited, BEq

/-- Precomputed data for membership tests at a fixed squared radius. -/
structure DiskTest where
  /-- The ring. -/
  F : CycField
  /-- The squared radius. -/
  r2 : RadiusSq
  /-- A double near `r²`. -/
  r2F : Float
  /-- A certified bound on `|r2F - r²|`. -/
  r2E : Float
  /-- The constant `(d + 2) u` of the filter. -/
  gam : Float

/-- The unit roundoff of double precision, `2⁻⁵³`. -/
def unitRoundoff : Float := (1.0 : Float).scaleB (-53)

/-- The constant `(d + 2) u` of the filter. -/
def filterGamma (F : CycField) : Float := (F.deg.toFloat + 2) * unitRoundoff

/-- Set up membership tests for `r²`. -/
def DiskTest.make (F : CycField) (r2 : RadiusSq) : DiskTest :=
  let b := (F.realBall r2.num F.basePrec).divNat r2.den
  let (f, e) := Ball.toFloatCert F.basePrec b
  { F, r2, r2F := f, r2E := e, gam := filterGamma F }

/-- Membership tests for points `w / M` at squared radius `r²`: the disks of radius `M r` about
`∓M` in the coordinate `w` (use `side = ±M`). -/
def DiskTest.makeScaled (F : CycField) (r2 : RadiusSq) (M : Nat) : DiskTest :=
  DiskTest.make F { num := F.smul ((M * M : Nat) : Int) r2.num, den := r2.den }

/-- The float approximations shared by both disks for one point. -/
structure FilterData where
  /-- `fl(∑ c_i t_i)`. -/
  x : Float
  /-- `fl(∑ c_i s_i)`. -/
  y : Float
  /-- `fl(∑ |c_i| |t_i|)`. -/
  ax : Float
  /-- `fl(∑ |c_i| |s_i|)`. -/
  ay : Float
  /-- `fl(∑ |c_i|)`. -/
  s1 : Float
  /-- Whether some coefficient is too large for the filter. -/
  big : Bool

/-- The loop of `filterData`, written as a recursion with unboxed accumulators. -/
def filterLoop (cosF sinF : FloatArray) (z : Elem) (i : Nat) (x y ax ay s1 : Float)
    (big : Bool) : FilterData :=
  if h : i < z.size then
    let c := z[i]
    if c == 0 then filterLoop cosF sinF z (i + 1) x y ax ay s1 big else
    let big := big || (c.natAbs >>> 53) != 0
    let cf := (Int64.ofInt c).toFloat
    let t := cosF[i]!
    let s := sinF[i]!
    let ca := cf.abs
    filterLoop cosF sinF z (i + 1) (x + cf * t) (y + cf * s) (ax + ca * t.abs) (ay + ca * s.abs)
      (s1 + ca) big
  else { x, y, ax, ay, s1, big }
termination_by z.size - i

/-- Compute the float data of the filter for a point `z`. -/
@[inline] def filterData (F : CycField) (z : Elem) : FilterData :=
  filterLoop F.cosF F.sinF z 0 fl0 fl0 fl0 fl0 fl0 false

/-- Float approximation `Q̂` of `|z + side|²` (`side = 1` for the left disk, `-1` for the right
disk; `±M` for the scaled disks below) with a certified error bound `E_Q`, as in the module
docstring (with `|side|` in place of `1` in `e_X`). -/
@[inline] def filterNormSq (F : CycField) (gam : Float) (fd : FilterData) (side : Float) :
    Float × Float :=
  let u := unitRoundoff
  let δ := F.trigErr
  let xw := fd.x + side
  let ex := fl2 * (gam * (fd.ax + side.abs) + δ * fd.s1)
  let ey := fl2 * (gam * fd.ay + δ * fd.s1)
  let q := xw * xw + fd.y * fd.y
  let eq := fl2 * (fl3 * u * q + ex * (fl2 * xw.abs + ex) + ey * (fl2 * fd.y.abs + ey))
  (q, eq)

/-- Outcome of one membership decision. -/
inductive Decision where
  /-- Decided by the floating-point filter. -/
  | filter (inside : Bool)
  /-- Decided exactly, the point being strictly inside or outside. -/
  | exact (inside : Bool)
  /-- The point lies exactly on the boundary circle (inside the closed disk). -/
  | boundary
  /-- The sign could not be certified (ruled out by the argument in `CycField.signReal`). -/
  | failure
  deriving Inhabited, BEq, Repr

/-- Whether a decision puts the point in the closed disk. -/
def Decision.inside : Decision → Bool
  | .filter b => b
  | .exact b => b
  | .boundary => true
  | .failure => false

/-- Exact sign of `r² - |z + side|²` (`side = ±1`), returned as a decision. -/
def DiskTest.exactDecide (T : DiskTest) (z : Elem) (side : Int) : Decision :=
  let F := T.F
  let w := F.addInt z side
  let dE := F.sub T.r2.num (F.smul T.r2.den (F.normSq w))
  match F.signReal dE with
  | some 0 => .boundary
  | some s => .exact (s > 0)
  | none => .failure

/-- Decide `|z + side| ≤ r` from precomputed filter data. -/
@[inline] def DiskTest.decideWith (T : DiskTest) (fd : FilterData) (z : Elem) (side : Int) :
    Decision :=
  if fd.big || (side.natAbs >>> 53) != 0 then T.exactDecide z side else
  let (q, eq) := filterNormSq T.F T.gam fd (Float.ofInt side)
  let dlt := T.r2F - q
  let bnd := fl2 * (T.r2E + eq)
  if dlt.isFinite && bnd.isFinite && dlt.abs > bnd then .filter (dlt > fl0)
  else T.exactDecide z side

/-- Decide membership of `z` in the left disk (`side = 1`) or the right disk (`side = -1`). -/
def DiskTest.decide (T : DiskTest) (z : Elem) (side : Int) : Decision :=
  T.decideWith (filterData T.F z) z side

end TDCSGCompute
