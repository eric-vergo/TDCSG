/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/

/-!
# Fixed-point ball arithmetic

A `Ball` is a pair `(mid, rad)` of an integer and a natural number. At a precision `p`, which the
caller keeps fixed, it stands for the closed interval `[(mid - rad) / 2 ^ p, (mid + rad) / 2 ^ p]`.
Every operation returns a ball that contains the exact result of the operation applied to any
points of its argument balls. That is the only invariant the rest of the engine relies on.

## Why each operation is an enclosure

Write `S = 2 ^ p` and let `x = (A + α) / S`, `y = (B + β) / S` with `|α| ≤ ra`, `|β| ≤ rb`.

* `add`, `sub`, `neg`, `mulInt`: exact on the midpoints; the radii add (or scale by `|k|`).
* `mul`: `x * y * S = A * B / S + (A * β + B * α + α * β) / S`. The midpoint is `⌊A * B / S⌋`,
  which is off by less than `1`, and the second term is at most `e / S ≤ ⌊e / S⌋ + 1` with
  `e = |A| * rb + |B| * ra + ra * rb`. So the radius `⌊e / S⌋ + 2` suffices.
* `divNat k` (for `k > 0`): the midpoint `A / k` (integer division) is off by less than `1`, and
  `ra / k ≤ ⌊ra / k⌋ + 1`, so the radius `⌊ra / k⌋ + 2` suffices.
* `rescale`: dropping `s` bits is a division by `2 ^ s`, as for `divNat`.

## Series

* `atanInv p m` sums `arctan (1 / m) = ∑ (-1) ^ j / ((2j + 1) m ^ (2j + 1))` until the running power
  `1 / m ^ (2j + 1)` is enclosed in a ball of a few units. The terms decrease and alternate, so the
  remainder is at most the first omitted term, which is at most the bound of that ball.
* `pi p` uses Machin's formula `π = 16 arctan (1/5) - 4 arctan (1/239)`.
* `cos p x` and `sin p x` sum the Taylor series. For `|x| ≤ 4` the term ratio `x² / ((2j+1)(2j+2))`
  (respectively `x² / ((2j+2)(2j+3))`) is below `1` from `j = 2` (respectively `j = 1`) on, so once
  at least that many terms are summed the remainder is alternating with decreasing terms and is
  bounded by the last summed term. The loop stops once that term is a few units in size, and adds
  its bound to the radius.
-/

namespace TDCSGCompute

/-- The ball `[(mid - rad) / 2 ^ p, (mid + rad) / 2 ^ p]`, for a precision `p` fixed by the
caller. -/
structure Ball where
  /-- The midpoint, scaled by `2 ^ p`. -/
  mid : Int
  /-- The radius, scaled by `2 ^ p`. -/
  rad : Nat
  deriving Inhabited, Repr

namespace Ball

/-- The exact ball for the integer `k` at precision `p`. -/
def ofInt (p : Nat) (k : Int) : Ball := ⟨k * ((2 ^ p : Nat) : Int), 0⟩

/-- Enclosure of a sum. -/
def add (a b : Ball) : Ball := ⟨a.mid + b.mid, a.rad + b.rad⟩

/-- Enclosure of a difference. -/
def sub (a b : Ball) : Ball := ⟨a.mid - b.mid, a.rad + b.rad⟩

/-- Enclosure of a negation. -/
def neg (a : Ball) : Ball := ⟨-a.mid, a.rad⟩

/-- Enclosure of a product with an integer. -/
def mulInt (a : Ball) (k : Int) : Ball := ⟨a.mid * k, a.rad * k.natAbs⟩

/-- Enclosure of a product, at precision `p`. -/
def mul (p : Nat) (a b : Ball) : Ball :=
  let e := a.mid.natAbs * b.rad + b.mid.natAbs * a.rad + a.rad * b.rad
  ⟨(a.mid * b.mid) >>> p, (e >>> p) + 2⟩

/-- Enclosure of a quotient by a positive natural number `k`. -/
def divNat (a : Ball) (k : Nat) : Ball := ⟨a.mid / (k : Int), a.rad / k + 2⟩

/-- The same ball at precision `p - s`, obtained by dropping `s` bits. -/
def rescale (a : Ball) (s : Nat) : Ball := ⟨a.mid >>> s, (a.rad >>> s) + 2⟩

/-- An upper bound for the absolute value of every point of the ball, scaled by `2 ^ p`. -/
def bound (a : Ball) : Nat := a.mid.natAbs + a.rad

/-- `1` if the ball lies in `(0, ∞)`, `-1` if it lies in `(-∞, 0)`, and `0` otherwise. -/
def sign (a : Ball) : Int :=
  if a.mid > (a.rad : Int) then 1 else if a.mid < -(a.rad : Int) then -1 else 0

/-- Whether the rational `num / den` (with `den > 0`) lies in the ball at precision `p`. -/
def containsRat (p : Nat) (a : Ball) (num : Int) (den : Nat) : Bool :=
  let v := num * ((2 ^ p : Nat) : Int)
  (a.mid - a.rad) * den ≤ v && v ≤ (a.mid + a.rad) * den

/-- Enclosure of `arctan (1 / m)` at precision `p`, for `m ≥ 2`. -/
def atanInv (p m : Nat) : Ball := Id.run do
  let m2 := m * m
  let mut t : Ball := (ofInt p 1).divNat m
  let mut s : Ball := ⟨0, 0⟩
  let mut j := 0
  while t.mid.natAbs > t.rad + 4 do
    let term := t.divNat (2 * j + 1)
    s := if j % 2 == 0 then s.add term else s.sub term
    t := t.divNat m2
    j := j + 1
  return ⟨s.mid, s.rad + t.bound⟩

/-- Enclosure of `π` at precision `p`, by Machin's formula. -/
def pi (p : Nat) : Ball :=
  ((atanInv p 5).mulInt 16).sub ((atanInv p 239).mulInt 4)

/-- Enclosure of `cos x` at precision `p`, for a ball `x` contained in `[-4, 4]`. -/
def cos (p : Nat) (x : Ball) : Ball := Id.run do
  let x2 := mul p x x
  let mut term := ofInt p 1
  let mut s := term
  let mut j := 0
  while j < 2 || term.mid.natAbs > term.rad + 4 do
    term := ((mul p term x2).divNat ((2 * j + 1) * (2 * j + 2))).neg
    s := s.add term
    j := j + 1
  return ⟨s.mid, s.rad + term.bound⟩

/-- Enclosure of `sin x` at precision `p`, for a ball `x` contained in `[-4, 4]`. -/
def sin (p : Nat) (x : Ball) : Ball := Id.run do
  let x2 := mul p x x
  let mut term := x
  let mut s := term
  let mut j := 0
  while j < 1 || term.mid.natAbs > term.rad + 4 do
    term := ((mul p term x2).divNat ((2 * j + 2) * (2 * j + 3))).neg
    s := s.add term
    j := j + 1
  return ⟨s.mid, s.rad + term.bound⟩

/-- Number of guard bits used internally by `trigTable`. -/
def guardBits : Nat := 32

/-- Enclosures at precision `p` of `cos (2πk/n)` and `sin (2πk/n)` for `0 ≤ k < n`. The angle is
first reduced to `2πk'/n` with `k' = min k (n - k)`, which lies in `[0, π]`. -/
def trigTable (p n : Nat) : Array Ball × Array Ball := Id.run do
  let q := p + guardBits
  let piB := pi q
  let mut cs : Array Ball := Array.emptyWithCapacity n
  let mut ss : Array Ball := Array.emptyWithCapacity n
  for k in [0:n] do
    let k' := min k (n - k)
    let x := (piB.mulInt (2 * k' : Nat)).divNat n
    let c := (cos q x).rescale guardBits
    let s := (sin q x).rescale guardBits
    cs := cs.push c
    ss := ss.push (if k' == k then s else s.neg)
  return (cs, ss)

/-- The exact rational value `(-1) ^ s * m * 2 ^ e` of a finite `Float`, as `(signedMantissa, e)`.
Returns `none` for infinities and NaN. -/
def floatExact (f : Float) : Option (Int × Int) :=
  let bits := f.toBits
  let neg := (bits >>> 63) == 1
  let ex := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if ex == 0x7FF then none
  else
    let (m, e) : Nat × Int := if ex == 0 then (frac, -1074) else (frac + 2 ^ 52, (ex : Int) - 1075)
    some (if neg then -(m : Int) else (m : Int), e)

/-- A `Float` close to the ball's midpoint together with a power of two `err` such that every point
of the ball (at precision `p ≥ 64`) is within `err` of it. The bound is computed exactly from the
bit pattern of the float, so it does not depend on how the conversion rounds. -/
def toFloatCert (p : Nat) (a : Ball) : Float × Float := Id.run do
  let s := p - 60
  let f := (Float.ofInt (a.mid >>> s)).scaleB ((s : Int) - p)
  match floatExact f with
  | none => return (f, (1.0 : Float) / 0.0)
  | some (m, e) =>
    -- Work at scale `2 ^ (p + K)` with `K ≥ 0` large enough that `f` is an integer there.
    let K : Nat := if e + p < 0 then (-(e + p)).toNat else 0
    let fScaled : Int := m * ((2 ^ (e + p + K).toNat : Nat) : Int)
    let midScaled : Int := a.mid * ((2 ^ K : Nat) : Int)
    let D : Nat := (fScaled - midScaled).natAbs + a.rad * 2 ^ K
    if D == 0 then return (f, 0.0)
    -- `D ≤ 2 ^ L` with `L = log2 D + 1`, so the error is at most `2 ^ (L - p - K)`.
    let L : Nat := D.log2 + 1
    return (f, (1.0 : Float).scaleB ((L : Int) - p - K))

/-- Decimal scientific notation for the midpoint of a ball at precision `p`, with `digits`
significant digits (the caller is responsible for the radius being small enough). -/
def sciString (p : Nat) (a : Ball) (digits : Nat := 12) : String := Id.run do
  let m := a.mid
  if m == 0 then return "0"
  let neg := m < 0
  let am := m.natAbs
  let S := 2 ^ p
  -- Find `e` with `10 ^ e ≤ am / S < 10 ^ (e + 1)`.
  let mut e : Int := 0
  -- Coarse estimate from bit lengths, then adjust.
  e := (((am.log2 : Int) - p) * 30103) / 100000
  let le (e : Int) : Bool :=
    -- `10 ^ e ≤ am / S`
    if e ≥ 0 then 10 ^ e.toNat * S ≤ am else S ≤ am * 10 ^ (-e).toNat
  for _ in [0:8] do
    if !(le e) then e := e - 1
  for _ in [0:8] do
    if le (e + 1) then e := e + 1
  -- Scaled integer `round (am / S * 10 ^ (digits - 1 - e))`.
  let sh : Int := (digits : Int) - 1 - e
  let (num, den) : Nat × Nat :=
    if sh ≥ 0 then (am * 10 ^ sh.toNat, S) else (am, S * 10 ^ (-sh).toNat)
  let mut q := (2 * num + den) / (2 * den)
  let mut e' := e
  if q ≥ 10 ^ digits then
    q := q / 10
    e' := e + 1
  let ds := toString q
  let body := if ds.length ≤ 1 then ds else
    String.ofList [ds.front] ++ "." ++ (ds.drop 1).toString
  let sgn := if neg then "-" else ""
  return s!"{sgn}{body}e{e'}"

end Ball

end TDCSGCompute
