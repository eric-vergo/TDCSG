/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Disk

/-!
# Parsing radii, points and real elements

Squared radii and other real elements of `ℚ(ζ_n)⁺` are written as a base, optionally followed by
`+q` or `-q` for a rational `q`:

* `touch`: `g(n)² = |2 - ζ|² = 5 - 2 (ζ + ζ⁻¹) = 5 - 4 cos (2π/n)`;
* `closed`: the closed form of `r_c(n)²` for `n ∈ {5, 8, 10, 12}`: `3 + φ`, `10 - 5√2`, `4 - φ`,
  `40 - 22√3`;
* `r1`: the second threshold `25 - 20 cos θ - 16 cos 2θ + 16 cos 3θ - 4 cos 4θ` (`θ = 2π/n`) of the
  `n ≡ 4 (mod 8)` family;
* `ra`: the analytic radius `r_A² = sec² (π/n) = 4 / (2 + 2 cos (2π/n))`;
* `fund`: the fundamental unit `φ`, `1 + √2`, `φ`, `2 + √3` of `ℚ(ζ_n)⁺` for `n = 5, 8, 10, 12`;
* `re:b0,b1,…`: `b0 + ∑_{k ≥ 1} b_k (ζ ^ k + ζ ^ (-k))` with rational `b_k`;
* `pow:c0,c1,…`: `∑ c_i ζ ^ i` with rational `c_i` (it must be real);
* a rational `q`, written `7`, `-3/4`, `1.0362` or `2.5e-7`.

Points are `0`, `pow:c0,c1,…` (integers), `zeta:k` (`ζ ^ k`), `a0` (`a 0 = ζ⁻¹ - 1`) or `b0`
(`b 0 = 1 - ζ⁻¹`).
-/

namespace TDCSGCompute

/-- Parse a rational number: an integer, `p/q`, or a decimal with optional exponent. -/
def parseRat (s : String) : Option Rat := do
  let s := s.trimAscii.toString
  let s := if s.startsWith "+" then (s.drop 1).toString else s
  if s.isEmpty then none
  match s.splitOn "/" with
  | [a, b] =>
    let p ← a.toInt?
    let q ← b.toNat?
    if q == 0 then none
    return (p : Rat) / (q : Rat)
  | [a] =>
    let (neg, body) := if a.startsWith "-" then (true, (a.drop 1).toString)
      else if a.startsWith "+" then (false, (a.drop 1).toString) else (false, a)
    let (mant, ex) ← match (body.replace "E" "e").splitOn "e" with
      | [m] => some (m, (0 : Int))
      | [m, e] => do let e ← e.toInt?; some (m, e)
      | _ => none
    let (ip, fp) ← match mant.splitOn "." with
      | [i] => some (i, "")
      | [i, f] => some (i, f)
      | _ => none
    if ip.isEmpty && fp.isEmpty then none
    let digits := ip ++ fp
    let m ← (if digits.isEmpty then some 0 else digits.toNat?)
    let e10 : Int := ex - fp.length
    let v : Rat := if e10 ≥ 0 then ((m * 10 ^ e10.toNat : Nat) : Rat)
      else (m : Rat) / ((10 ^ (-e10).toNat : Nat) : Rat)
    return if neg then -v else v
  | _ => none

/-- A real element `num / den` of `ℚ(ζ_n)⁺` (the same data as a squared radius). -/
abbrev RealQ := RadiusSq

namespace RealQ

/-- Remove common factors of the numerator coefficients and the denominator. -/
def normalize (x : RealQ) : RealQ :=
  let g := x.num.foldl (fun g c ↦ Nat.gcd g c.natAbs) x.den
  if g ≤ 1 then x else { num := x.num.map (· / (g : Int)), den := x.den / g }

/-- The rational `q` as a real element. -/
def ofRat (F : CycField) (q : Rat) : RealQ := { num := F.ofInt q.num, den := q.den }

/-- An integral real element. -/
def ofElem (x : Elem) : RealQ := { num := x, den := 1 }

/-- Sum with a rational. -/
def addRat (F : CycField) (x : RealQ) (q : Rat) : RealQ :=
  normalize { num := F.addInt (F.smul q.den x.num) (q.num * x.den), den := x.den * q.den }

/-- Product of two real elements. -/
def mul (F : CycField) (x y : RealQ) : RealQ :=
  normalize { num := F.mul x.num y.num, den := x.den * y.den }

/-- Exact comparison of two real elements. -/
def compare (F : CycField) (x y : RealQ) : Option Ordering :=
  F.compareReal (F.smul y.den x.num) (F.smul x.den y.num)

end RealQ

/-- Elements from rational coefficient vectors, `num / den` with a common denominator. -/
def commonDen (qs : Array Rat) : Nat × Array Int :=
  let den := qs.foldl (fun l q ↦ Nat.lcm l q.den) 1
  (den, qs.map fun q ↦ q.num * ((den / q.den : Nat) : Int))

/-- `ζ ^ k + ζ ^ (-k)` coefficients `b`, as an element, for small hand-written forms. -/
def realOf (F : CycField) (b : List Int) : Elem := F.ofRealBasis b.toArray

/-- The named real elements. -/
def namedReal (F : CycField) (name : String) : Except String RealQ :=
  let n := F.n
  match name with
  | "touch" => .ok (.ofElem (realOf F [5, -2]))
  | "closed" =>
    match n with
    | 5 => .ok (.ofElem (realOf F [3, 0, -1]))    -- 3 + φ, φ = -(ζ² + ζ³)
    | 10 => .ok (.ofElem (realOf F [4, -1]))      -- 4 - φ, φ = ζ + ζ⁻¹
    | 8 => .ok (.ofElem (realOf F [10, -5]))      -- 10 - 5√2, √2 = ζ + ζ⁻¹
    | 12 => .ok (.ofElem (realOf F [40, -22]))    -- 40 - 22√3, √3 = ζ + ζ⁻¹
    | _ => .error s!"no closed form of r_c² is known for n = {n}"
  | "r1" => .ok (.ofElem (realOf F [25, -10, -8, 8, -2]))
  | "ra" =>
    -- r_A² = sec² (π/n) = 4 / (2 + θ_1)
    match F.normAdj (realOf F [2, 1]) with
    | some (adj, N) =>
      let num := F.smul (if N < 0 then -4 else 4) adj
      .ok (RealQ.normalize { num, den := N.natAbs })
    | none => .error "norm computation failed"
  | "fund" =>
    match n with
    | 5 => .ok (.ofElem (realOf F [0, 0, -1]))    -- φ = -(ζ² + ζ³)
    | 10 => .ok (.ofElem (realOf F [0, 1]))       -- φ
    | 8 => .ok (.ofElem (realOf F [1, 1]))        -- 1 + √2
    | 12 => .ok (.ofElem (realOf F [2, 1]))       -- 2 + √3
    | _ => .error s!"no fundamental unit is built in for n = {n}"
  | _ => .error s!"unknown name {name}"

/-- Parse a comma-separated list of rationals. -/
def parseRatList (s : String) : Except String (Array Rat) :=
  (s.splitOn ",").toArray.mapM fun t ↦
    match parseRat t with
    | some q => .ok q
    | none => .error s!"cannot parse the rational {t}"

/-- Parse a real element of `ℚ(ζ_n)⁺` (see the module docstring). -/
def parseReal (F : CycField) (spec : String) : Except String RealQ := do
  let spec := spec.trimAscii.toString
  if spec.startsWith "re:" then
    let qs ← parseRatList (spec.drop 3).toString
    let (den, b) := commonDen qs
    return RealQ.normalize { num := F.ofRealBasis b, den }
  if spec.startsWith "pow:" then
    let qs ← parseRatList (spec.drop 4).toString
    if qs.size > F.deg then throw s!"at most {F.deg} power-basis coefficients for n = {F.n}"
    let (den, c) := commonDen qs
    let num := F.reducePoly c
    if !F.isReal num then throw "the element is not real"
    return RealQ.normalize { num, den }
  for name in ["touch", "closed", "r1", "fund", "ra"] do
    if spec.startsWith name then
      let base ← namedReal F name
      let rest := (spec.drop name.length).toString
      if rest.isEmpty then return base
      match parseRat rest with
      | some q => return base.addRat F q
      | none => throw s!"cannot parse the offset {rest}"
  match parseRat spec with
  | some q => return RealQ.ofRat F q
  | none => throw s!"cannot parse the real element {spec}"

/-- Parse a squared radius given either as `--r2 SPEC` or as a rational radius `--r Q`. -/
def parseRadiusSq (F : CycField) (r2 : Option String) (r : Option String) :
    Except String RadiusSq := do
  match r2, r with
  | some s, none => parseReal F s
  | none, some s =>
    match parseRat s with
    | some q => return RealQ.ofRat F (q * q)
    | none => throw s!"cannot parse the radius {s}"
  | _, _ => throw "give exactly one of --r2 and --r"

/-- Parse a starting point. -/
def parsePoint (F : CycField) (spec : String) : Except String Elem := do
  let spec := spec.trimAscii.toString
  if spec == "0" then return F.zero
  if spec == "a0" then return F.addInt (F.zetaPow (-1)) (-1)
  if spec == "b0" then return F.addInt (F.neg (F.zetaPow (-1))) 1
  if spec.startsWith "zeta:" then
    match (spec.drop 5).toString.toInt? with
    | some k => return F.zetaPow k
    | none => throw s!"cannot parse {spec}"
  if spec.startsWith "pow:" then
    let cs ← ((spec.drop 4).toString.splitOn ",").toArray.mapM fun t ↦
      match t.trimAscii.toString.toInt? with
      | some c => Except.ok c
      | none => Except.error s!"cannot parse the integer {t}"
    return F.reducePoly cs
  throw s!"cannot parse the point {spec}"

/-- Parse a point of `ℚ(ζ_n)`: an integral point `P` (see `parsePoint`), `P/Q` with integral
points `P`, `Q ≠ 0`, or `necklace` (the triple point `(1 - ζ) / (1 + ζ) = -i tan (π/n)` of the
disks about `-1`, `1` and `a(1)` at `r = sec (π/n)`). Returns `(u, D)` with the point `u / D`,
`D ≥ 1`. -/
def parsePointQ (F : CycField) (spec : String) : Except String (Elem × Nat) := do
  let spec := spec.trimAscii.toString
  let spec := if spec == "necklace" then "pow:1,-1/pow:1,1" else spec
  match spec.splitOn "/" with
  | [p] => return (← parsePoint F p, 1)
  | [p, q] =>
    let u ← parsePoint F p
    let v ← parsePoint F q
    if F.isZero v then throw "division by zero"
    match F.normAdj v with
    | none => throw "norm computation failed"
    | some (adj, N) =>
      let num := F.mul u adj
      let num := if N < 0 then F.neg num else num
      let g := num.foldl (fun g c ↦ Nat.gcd g c.natAbs) N.natAbs
      return (num.map (· / (g : Int)), N.natAbs / g)
  | _ => throw s!"cannot parse the point {spec}"

/-- The real element `x` in the basis `1, θ_1, …` as text, with a readable form for the quadratic
real subfields (`n = 5, 8, 10, 12`). -/
def showReal (F : CycField) (x : RealQ) : String :=
  match F.toRealBasis x.num with
  | none => s!"pow:{x.num}"
  | some b =>
    let denS := if x.den == 1 then "" else s!" / {x.den}"
    let basis := ",".intercalate (b.toList.map toString)
    let pretty : String :=
      if b.size == 2 then
        match F.n with
        | 5 => s!"{b[0]! - b[1]!} + {b[1]!}φ"
        | 10 => s!"{b[0]!} + {b[1]!}φ"
        | 8 => s!"{b[0]!} + {b[1]!}√2"
        | 12 => s!"{b[0]!} + {b[1]!}√3"
        | _ => ""
      else ""
    let prettyS := if pretty.isEmpty then "" else s!" = ({pretty}){denS}"
    s!"re:{basis}{denS}{prettyS}"

end TDCSGCompute
