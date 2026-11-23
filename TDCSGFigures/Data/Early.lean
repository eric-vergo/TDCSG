/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean
import TDCSGCompute.Orbit
import TDCSGFigures.Data

/-!
# The exact objects of the figures of chapters 1, 2, 3 and 9

Every point is exact: an element of `ℤ[ζ₅]` (`PILean.Exact.Zeta5`), a pair of numbers of `ℚ(√d)`,
or an element of `ℤ[ζₙ]` of the orbit engine `TDCSGCompute` (`CycPt n`), drawn through its exact
coordinates. Every disk test is an exact comparison of a squared distance with a squared radius.

* The generators on `ℤ[ζ₅]`: `a z = -1 + ζ⁴ (z + 1)` turns the closed disk about `-1` clockwise
  through `72°`, `b z = 1 + ζ⁴ (z - 1)` the disk about `1` (`TDCSG.genA`, `TDCSG.genB`); a letter
  moves a point only when the point lies in the letter's closed disk. `Letter.act`, `trace`.
* The three words of chapter 3 on the pieces of the chord, letter by letter (`wordPath`).
* `AxisPoint`, a point of the plane with an exact real abscissa (a square root, say) and a rational
  ordinate, for the radius line.
* `CycPt n`, an element of `ℤ[ζₙ]` in the power basis of `TDCSGCompute.CycField.make n`, with a
  `PILean.Exact.PlanePoint` instance for `n = 8`, `10`, `12` from its exact coordinates in
  `ℚ(√2)`, `ℤ[ζ₅]` and `ℚ(√3)`; the critical points, radii and words of `n = 8, 10, 12`
  (`TDCSG.Eight`, `TDCSG.Ten`, `TDCSG.Twelve`), replayed by the engine with exact disk tests.

The `#guard` lines at the end recompute every instance the figures draw and stop the build if one
no longer has the property its caption states.
-/

namespace TDCSGFigures.Early

open PILean PILean.Exact TDCSGFigures

/-! ### The generators on `ℤ[ζ₅]` -/

/-- A letter of a word in the generators (`TDCSG.Letter`). -/
inductive Letter where
  /-- The left generator `a`. -/
  | a
  /-- Its inverse `a⁻¹`. -/
  | aInv
  /-- The right generator `b`. -/
  | b
  /-- Its inverse `b⁻¹`. -/
  | bInv
  deriving BEq, Inhabited, Repr

/-- The centre `-1` or `1` of the letter's disk. -/
def Letter.centre : Letter → Zeta5
  | .a | .aInv => leftCentre
  | .b | .bInv => rightCentre

/-- The turn of the letter: `ζ⁴ = e^{-2πi/5}` (clockwise) for a generator, `ζ` for an inverse. -/
def Letter.turn : Letter → Zeta5
  | .a | .b => zeta 4
  | .aInv | .bInv => zeta 1

/-- The letter as text. -/
def Letter.text : Letter → String
  | .a => "a" | .aInv => "a⁻¹" | .b => "b" | .bInv => "b⁻¹"

/-- Whether `z` lies in the letter's closed disk of squared radius `r2`, decided exactly. -/
def Letter.covers (l : Letter) (r2 : QSqrt5) (z : Zeta5) : Bool :=
  QSqrt.le (z - l.centre).normSq r2

/-- The letter's turn about its centre, applied whether or not `z` is in its disk. -/
def Letter.rotate (l : Letter) (z : Zeta5) : Zeta5 := l.centre + (z - l.centre) * l.turn

/-- The letter as a permutation of the plane at squared radius `r2` (`TDCSG.diskRotation`): the
turn on the closed disk, the identity outside it. -/
def Letter.act (l : Letter) (r2 : QSqrt5) (z : Zeta5) : Zeta5 :=
  if l.covers r2 z then l.rotate z else z

/-- Where `z` stands relative to the closed disk of squared radius `r2` about `c`, decided exactly:
on its boundary circle, inside or outside. -/
def exactSide (c : Zeta5) (r2 : QSqrt5) (z : Zeta5) : Plane.Incidence :=
  if (z - c).normSq == r2 then .on else if QSqrt.lt (z - c).normSq r2 then .inside else .outside

/-- The point item `it` of `z` with where `z` stands relative to the two closed disks of squared
radius `r2` about `∓1`, titled "the left circle" and "the right circle", and to their lens, titled
"the lens", decided exactly. -/
def recordSides (r2 : QSqrt5) (z : Zeta5) (it : Plane.Item) : Plane.Item :=
  let l := exactSide leftCentre r2 z
  let r := exactSide rightCentre r2 z
  let lens : Plane.Incidence := match l, r with
    | .inside, .inside => .inside
    | .outside, _ | _, .outside => .outside
    | _, _ => .on
  it |>.incident l "the left circle" |>.incident r "the right circle" |>.incident lens "the lens"

/-- The direction of `z` seen from `c`, in radians: for drawing an arc, never for a decision. -/
def angleFrom (c z : Zeta5) : Float :=
  let v := PlanePoint.toPoint z - PlanePoint.toPoint c
  Float.atan2 v.y v.x

/-- The points `z, w₁ z, w₂ w₁ z, …` met by `z` under the word `w`, letters applied from left to
right (`TDCSG.applyWord`). -/
def trace (r2 : QSqrt5) (w : List Letter) (z : Zeta5) : List Zeta5 :=
  w.foldl (fun acc l => acc ++ [l.act r2 (acc.getLast?.getD z)]) [z]

/-! ### Chapter 1: one disk turned, the identity outside -/

/-- The radius `10` of the disk `B` of chapter 1's first figure, about `0`. -/
def ballRadius : Rat := 10

/-- The point `p = 9`, just inside `B`. -/
def nearInside : Zeta5 := Zeta5.ofInt 9

/-- The point `q = 11`, just outside `B`. -/
def nearOutside : Zeta5 := Zeta5.ofInt 11

/-- The image `ĥ(p) = 9 ζ⁴` of `p` under the turn of `B` through `72°` clockwise about `0`. -/
def nearInsideImage : Zeta5 := nearInside * zeta 4

/-! ### Chapter 1: two disjoint disks -/

/-- The radius `r₁ = 4/5` of the left disk of the product figure. -/
def disjointLeft : Rat := 4 / 5

/-- The radius `r₂ = 7/10` of the right disk of the product figure. -/
def disjointRight : Rat := 7 / 10

/-- The point `x = -1 + φ⁻¹ ζ²` of the left disk (`φ⁻¹ = ζ + ζ⁴`), above `-1` and to its left. -/
def leftSample : Zeta5 := leftCentre + phiInv * zeta 2

/-- The point `y = 1 + φ⁻¹ ζ²` of the right disk, above `1` and to its left. -/
def rightSample : Zeta5 := rightCentre + phiInv * zeta 2

/-- `φ⁻¹ = (√5 - 1)/2`, the distance of `x` from `-1` and of `y` from `1`. -/
def phiInvReal : QSqrt5 := ⟨-1 / 2, 1 / 2⟩

/-- The point `ζ²` times the radius `10` of the disk `B`: the end of its drawn radius. -/
def ballSpoke : Zeta5 := Zeta5.ofInt 10 * zeta 2

/-! ### Chapter 2: the generators at radius `3/2` and `21/10` -/

/-- `(3/2)²`, the squared radius of the generator figure. -/
def r2ThreeHalves : QSqrt5 := rat (9 / 4)

/-- `(21/10)²`, the squared radius of the word stepper. -/
def r2Step : QSqrt5 := rat (441 / 100)

/-- `a(0) = -1 + ζ⁴`. -/
def aZero : Zeta5 := leftCentre + zeta 4

/-- The word `a b b a` of the stepper. -/
def stepWord : List Letter := [.a, .b, .b, .a]

/-- The points `z₀ = 0, z₁, …, z₄` of `0` under `a b b a` at radius `21/10`. -/
def stepPoints : List Zeta5 := trace r2Step stepWord origin

/-! ### Chapter 3: the three words on the chord -/

/-- `(1 - φ) E`, where the first piece ends and the second begins (`firstCut`). -/
def cutF : Zeta5 := firstCut

/-- `(3 - 2φ) E`, where the second piece ends and the third begins (`secondCut`). -/
def cutG : Zeta5 := secondCut

/-- The word `a⁻¹ a⁻¹ b⁻¹ a⁻¹ b⁻¹` (`TDCSG.Five.word₁`). -/
def word₁ : List Letter := [.aInv, .aInv, .bInv, .aInv, .bInv]

/-- The word `a b a b b` (`TDCSG.Five.word₂`). -/
def word₂ : List Letter := [.a, .b, .a, .b, .b]

/-- The word `a b a b⁻¹ a⁻¹ b⁻¹` (`TDCSG.Five.word₃`). -/
def word₃ : List Letter := [.a, .b, .a, .bInv, .aInv, .bInv]

/-- The word `i` and its piece `[p, q]` of the chord. -/
def wordPiece : Nat → List Letter × Zeta5 × Zeta5
  | 1 => (word₁, -chordEnd, cutF)
  | 2 => (word₂, cutF, cutG)
  | _ => (word₃, cutG, chordEnd)

/-- The images of the ends of the piece of word `i` after `0, 1, 2, …` letters, at the critical
radius. -/
def wordPath (i : Nat) : List (Zeta5 × Zeta5) :=
  let (w, p, q) := wordPiece i
  (trace threePlusPhi w p).zip (trace threePlusPhi w q)

/-- Whether, before every letter of word `i`, both current ends of its piece lie in the letter's
closed disk at the critical radius: the check of `TDCSG.Five.applyWord_chord`, which makes the
letter one rotation of the whole current segment. -/
def wordChecks (i : Nat) : Bool :=
  let (w, p, q) := wordPiece i
  let ends := (trace threePlusPhi w p).zip (trace threePlusPhi w q)
  (w.zip ends).all fun (l, x, y) => l.covers threePlusPhi x && l.covers threePlusPhi y

/-- The ends after the letter `k` of word `i` that lie on that letter's boundary circle, with the
side (`true` for the left circle): the disk tests that hold with equality. -/
def wordEqualities (i : Nat) : List (Nat × Zeta5 × Bool) :=
  let (w, p, q) := wordPiece i
  let ends := (trace threePlusPhi w p).zip (trace threePlusPhi w q)
  ((w.zip ends).zipIdx.flatMap fun ((l, x, y), k) =>
    [x, y].filterMap fun z =>
      if (z - l.centre).normSq == threePlusPhi then
        some (k, z, l.centre == leftCentre) else none)

/-- The orbit of `0` along the chord, `t₀ = 0, t₁, …, tₙ`, each with the word that applies to it
next (the piece of the chord holding `t_k E`): `(chordStep t_k).1`. -/
def chordRows (n : Nat) : Array (Nat × QSqrt5) :=
  (chordReturns n).map fun (_, t) => ((chordStep t).1, t)

/-- The pair `(m, n)` with `t = m + n φ`, for `t = a + b √5` (`√5 = 2φ - 1`). -/
def phiForm (t : QSqrt5) : Rat × Rat := (t.a - t.b, 2 * t.b)

/-- A natural number in subscript digits. -/
def subscript (k : Nat) : String :=
  String.ofList ((toString k).toList.map fun c => "₀₁₂₃₄₅₆₇₈₉".toList.getD (c.toNat - 48) c)

/-- `m + n φ` as text, `n φ` first: `14φ − 22`. -/
def phiText (t : QSqrt5) : String :=
  let (m, n) := phiForm t
  let num := fun (q : Rat) => if q.den == 1 then toString q.num else toString q
  let nPart := if n == 0 then "" else if n == 1 then "φ" else if n == -1 then "−φ"
    else s!"{num n}φ".replace "-" "−"
  if nPart.isEmpty then (num m).replace "-" "−"
  else if m == 0 then nPart
  else if m > 0 then s!"{nPart} + {num m}" else s!"{nPart} − {num (-m)}"

/-! ### The radius line -/

/-- A point of the plane with an exact real abscissa `x` and a rational ordinate `y`. -/
structure AxisPoint (β : Type) where
  /-- The abscissa. -/
  x : β
  /-- The ordinate. -/
  y : Rat

/-- An axis point is drawn from the balls of its abscissa and its rational ordinate. -/
instance {β : Type} [RealValue β] : PlanePoint (AxisPoint β) where
  re p k := RealValue.ball p.x k
  im p _ := ⟨p.y, 0⟩

/-- A real number of the radius line: a rational, or the square root of a number of `ℚ(√5)`. -/
inductive AxisValue where
  /-- A rational. -/
  | rat (q : Rat)
  /-- `√x`. -/
  | root (x : SqrtOf QSqrt5)

/-- The balls of a rational (radius 0) or of a square root. -/
instance : RealValue AxisValue where
  ball
    | .rat q, _ => ⟨q, 0⟩
    | .root x, k => RealValue.ball x k

/-- The point `(x, y)` of the radius line's picture. -/
def axisAt (x : AxisValue) (y : Rat) : AxisPoint AxisValue := ⟨x, y⟩

/-- The critical radius `R = √(3 + φ)` on the radius line. -/
def axisR : AxisValue := .root critical

/-! ### Other orders: points of `ℤ[ζₙ]` from the orbit engine -/

open TDCSGCompute

/-- An element of `ℤ[ζₙ]`, `ζ = e^{2πi/n}`, by its coefficients in the power basis
`1, ζ, …, ζ^{φ(n)-1}` of `CycField.make n`. -/
structure CycPt (n : Nat) where
  /-- The coefficients. -/
  c : Elem

/-- `ℤ[ζ₈]` with the engine's tables. -/
def field8 : CycField := CycField.make 8

/-- `ℤ[ζ₁₀]` with the engine's tables. -/
def field10 : CycField := CycField.make 10

/-- `ℤ[ζ₁₂]` with the engine's tables. -/
def field12 : CycField := CycField.make 12

/-- The complex number `(x, y)` of `ℚ(√d)` times `(u, v)`. -/
def cmul {d : Nat} (p q : QSqrt d × QSqrt d) : QSqrt d × QSqrt d :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

/-- `|p - q|²` for points of `ℚ(√d)²`. -/
def distSq {d : Nat} (p q : QSqrt d × QSqrt d) : QSqrt d :=
  let x := p.1 - q.1
  let y := p.2 - q.2
  x * x + y * y

/-- `c · (x, y)` for an integer `c`. -/
def zsmul {d : Nat} (c : Int) (p : QSqrt d × QSqrt d) : QSqrt d × QSqrt d :=
  (⟨c, 0⟩ * p.1, ⟨c, 0⟩ * p.2)

/-- The point `∑ cⱼ bⱼ` for the coordinates `bⱼ` of the basis. -/
def combine {d : Nat} (basis : Array (QSqrt d × QSqrt d)) (c : Elem) : QSqrt d × QSqrt d :=
  (c.zip basis).foldl (fun (s : QSqrt d × QSqrt d) (k, p) =>
    (s.1 + (zsmul k p).1, s.2 + (zsmul k p).2)) (⟨0, 0⟩, ⟨0, 0⟩)

/-- The coordinates of `1, ζ₈, ζ₈², ζ₈³` in `ℚ(√2)`: `ζ₈ = (√2/2, √2/2)`. -/
def basis8 : Array (QSqrt 2 × QSqrt 2) :=
  #[(⟨1, 0⟩, ⟨0, 0⟩), (⟨0, 1 / 2⟩, ⟨0, 1 / 2⟩), (⟨0, 0⟩, ⟨1, 0⟩), (⟨0, -1 / 2⟩, ⟨0, 1 / 2⟩)]

/-- The coordinates of `1, ζ₁₂, ζ₁₂², ζ₁₂³` in `ℚ(√3)`: `ζ₁₂ = (√3/2, 1/2)`. -/
def basis12 : Array (QSqrt 3 × QSqrt 3) :=
  #[(⟨1, 0⟩, ⟨0, 0⟩), (⟨0, 1 / 2⟩, ⟨1 / 2, 0⟩), (⟨1 / 2, 0⟩, ⟨0, 1 / 2⟩), (⟨0, 0⟩, ⟨1, 0⟩)]

/-- The exact coordinates of an element of `ℤ[ζ₈]`. -/
def CycPt.coords8 (p : CycPt 8) : QSqrt 2 × QSqrt 2 := combine basis8 p.c

/-- The exact coordinates of an element of `ℤ[ζ₁₂]`. -/
def CycPt.coords12 (p : CycPt 12) : QSqrt 3 × QSqrt 3 := combine basis12 p.c

/-- An element of `ℤ[ζ₁₀]` as an element of `ℤ[ζ₅]`: `ζ₁₀ = -ζ₅³`. -/
def CycPt.toZeta5 (p : CycPt 10) : Zeta5 :=
  Zeta5.reduce <| (p.c.zipIdx.foldl (fun (s : Array Int) (k, j) =>
    let sgn : Int := if j % 2 == 0 then 1 else -1
    s.modify ((3 * j) % 5) (· + sgn * k)) #[0, 0, 0, 0, 0])

/-- An element of `ℤ[ζ₅]` as an element of `ℤ[ζ₁₀]`: `ζ₅ = ζ₁₀²`. -/
def ofZeta5 (z : Zeta5) : CycPt 10 :=
  ⟨(List.range 4).foldl (fun s j => field10.add s
    (field10.smul (z.coeff j) field10.pows[2 * j]!)) field10.zero⟩

/-- An element of `ℤ[ζ₈]` is drawn at its exact coordinates in `ℚ(√2)`. -/
instance : PlanePoint (CycPt 8) where
  re p k := QSqrt.ball p.coords8.1 k
  im p k := QSqrt.ball p.coords8.2 k

/-- An element of `ℤ[ζ₁₀]` is drawn as the element of `ℤ[ζ₅]` it is. -/
instance : PlanePoint (CycPt 10) where
  re p k := PlanePoint.re p.toZeta5 k
  im p k := PlanePoint.im p.toZeta5 k

/-- An element of `ℤ[ζ₁₂]` is drawn at its exact coordinates in `ℚ(√3)`. -/
instance : PlanePoint (CycPt 12) where
  re p k := QSqrt.ball p.coords12.1 k
  im p k := QSqrt.ball p.coords12.2 k

/-- The letter `l` applied by the engine at squared radius `r2`: its rotation (`CycField.rotCW`,
clockwise, for `a` and `b`; `rotCCW` for the inverses) when the exact disk test
(`DiskTest.exactDecide`) puts the point in the letter's closed disk; `none` when the test is not
decided. -/
def engineAct (F : CycField) (r2 : TDCSGCompute.RadiusSq) (l : Letter) (z : Elem) : Option Elem :=
  let T := DiskTest.make F r2
  let side : Int := match l with | .a | .aInv => 1 | .b | .bInv => -1
  match T.exactDecide z side with
  | .exact false => some z
  | .exact true | .boundary =>
    some <| match l with
      | .a | .b => F.rotCW z side
      | .aInv | .bInv => F.rotCCW z side
  | _ => none

/-- Whether every letter of `w`, applied by the engine from `z`, finds the point in its closed
disk, and the point reached. -/
def engineWord (F : CycField) (r2 : TDCSGCompute.RadiusSq) (w : List Letter) (z : Elem) :
    Option (Bool × Elem) :=
  w.foldlM (fun (ok, z) l => do
    let side : Int := match l with | .a | .aInv => 1 | .b | .bInv => -1
    let inside := match (DiskTest.make F r2).exactDecide z side with
      | .exact true | .boundary => true
      | _ => false
    let z' ← engineAct F r2 l z
    return (ok && inside, z')) (true, z)

/-- Where `p` stands relative to the closed disk of squared radius `r2` about `c`, for points of
`ℚ(√d)²`, decided exactly. -/
def sideQ {d : Nat} [QSqrt.NonSquare d] (c p : QSqrt d × QSqrt d) (r2 : QSqrt d) :
    Plane.Incidence :=
  let s := distSq p c
  if s == r2 then .on else if QSqrt.lt s r2 then .inside else .outside

/-- The incidence with the lens of a point that stands `l` to the left and `r` to the right
disk. -/
def lensSide : Plane.Incidence → Plane.Incidence → Plane.Incidence
  | .inside, .inside => .inside
  | .outside, _ | _, .outside => .outside
  | _, _ => .on

/-- The item `it` of a point that stands `l` to the left and `r` to the right disk, recording it
and its place relative to the lens. -/
def recordLR (l r : Plane.Incidence) (it : Plane.Item) : Plane.Item :=
  it |>.incident l "the left circle" |>.incident r "the right circle"
    |>.incident (lensSide l r) "the lens"

/-! ### Order 8 -/

/-- `√2 = ζ₈ - ζ₈³`. -/
def sqrt2 : Elem := #[0, 1, 0, -1]

/-- The squared radius `10 - 5√2` of order 8 (`TDCSG.CriticalRadius.criticalRadius_eight_le`). -/
def r2Eight : TDCSGCompute.RadiusSq := ⟨#[10, -5, 0, 5], 1⟩

/-- The radius `√(10 - 5√2)`. -/
def radiusEight : SqrtOf (QSqrt 2) := ⟨⟨10, -5⟩⟩

/-- The critical point `p* = 1 - 2ζ + ζ² - ζ³` of order 8 (`TDCSG.Eight.pStar`). -/
def pStar8 : CycPt 8 := ⟨#[1, -2, 1, -1]⟩

/-- The seed word `b b a b` of order 8 (`TDCSG.Eight.seed`). -/
def seed8 : List Letter := [.b, .b, .a, .b]

/-- The point `q_k = p* + 4 i (√2 - 1)^(k+1)` of the orbit of `p*`
(`TDCSG.Eight.mem_orbit_pStar_pow`). -/
def orbit8 (k : Nat) : CycPt 8 :=
  let e := field8.sub sqrt2 field8.one
  let pw := (List.range (k + 1)).foldl (fun s _ => field8.mul s e) field8.one
  ⟨field8.add pStar8.c (field8.smul 4 (field8.mul field8.pows[2]! pw))⟩

/-- The point `q₀ = p* + 4 (√2 - 1) i = 1 + 2ζ - 3ζ² + 3ζ³` (`orbit8 0`). -/
def q8₀ : CycPt 8 := ⟨#[1, 2, -3, 3]⟩

/-- The point `q₁ = p* + 4 (√2 - 1)² i = 1 - 10ζ + 13ζ² - 9ζ³` (`orbit8 1`). -/
def q8₁ : CycPt 8 := ⟨#[1, -10, 13, -9]⟩

/-- The integer `k` in `ℤ[ζ₈]`: the centres `∓1`. -/
def centre8 (k : Int) : CycPt 8 := ⟨#[k, 0, 0, 0]⟩

/-! ### Order 12 -/

/-- `√3 = ζ₁₂ + ζ₁₂⁻¹ = 2ζ₁₂ - ζ₁₂³`. -/
def sqrt3 : Elem := #[0, 2, 0, -1]

/-- The squared radius `40 - 22√3` of order 12 (`TDCSG.CriticalRadius.criticalRadius_twelve_le`). -/
def r2Twelve : TDCSGCompute.RadiusSq := ⟨#[40, -44, 0, 22], 1⟩

/-- The radius `√(40 - 22√3)`. -/
def radiusTwelve : SqrtOf (QSqrt 3) := ⟨⟨40, -22⟩⟩

/-- The critical point `p* = -2ζ + 4ζ² - 3ζ³` of order 12 (`TDCSG.Twelve.pStar`). -/
def pStar12 : CycPt 12 := ⟨#[0, -2, 4, -3]⟩

/-- The direction `V = ζ⁵ + ζ⁶ = -1 - ζ + ζ³` of the chord of order 12 (`TDCSG.Twelve.chordDir`). -/
def chordDir12 : Elem := #[-1, -1, 0, 1]

/-- The seed word `b a b b a a` of order 12 (`TDCSG.Twelve.seed`). -/
def seed12 : List Letter := [.b, .a, .b, .b, .a, .a]

/-- The point `q₀ = p* + (14 - 8√3) V = p* + 2 (2 - √3)² V` of the orbit of `p*`
(`TDCSG.Twelve.applyWord_seed`), `2 - 4ζ² + 3ζ³`. -/
def orbit12 : CycPt 12 := ⟨#[2, 0, -4, 3]⟩

/-- The mirror image `p̄*` of `p*` in the real axis, on the left circle as well: the end of the
drawn radius of order 12. -/
def pStar12Conj : CycPt 12 := ⟨#[4, -2, -4, 5]⟩

/-- The integer `k` in `ℤ[ζ₁₂]`: the centres `∓1`. -/
def centre12 (k : Int) : CycPt 12 := ⟨#[k, 0, 0, 0]⟩

/-! ### Order 10 -/

/-- The squared radius `4 - φ = 4 + ζ₅² + ζ₅³` of order 10, in `ℤ[ζ₁₀]`
(`TDCSG.CriticalRadius.criticalRadius_ten_le`). -/
def r2Ten : TDCSGCompute.RadiusSq := ⟨(ofZeta5 ⟨#[4, 0, 1, 1]⟩).c, 1⟩

/-- `4 - φ` in `ℚ(√5)`. -/
def fourMinusPhi : QSqrt5 := ⟨7 / 2, -1 / 2⟩

/-- The radius `√(4 - φ)`. -/
def radiusTen : SqrtOf QSqrt5 := ⟨fourMinusPhi⟩

/-- The direction `u = ζ₅²` of the chord of order 10 (`TDCSG.Ten.dirU`). -/
def dirU : Zeta5 := zeta 2

/-- The end `W = √5 u = 2ζ + ζ² + 2ζ³` of the chord of order 10 (`TDCSG.Ten.pointW`). -/
def pointW : Zeta5 := ⟨#[0, 2, 1, 2]⟩

/-- The cut `-φ⁻¹ u` between the pieces of the first and the second word of order 10. -/
def cutTen₁ : Zeta5 := -(phiInv * dirU)

/-- The cut `u` between the pieces of the second and the third word of order 10. -/
def cutTen₂ : Zeta5 := dirU

/-- The integer `k` in `ℤ[ζ₁₀]`: the centres `∓1`. -/
def centre10 (k : Int) : CycPt 10 := ⟨#[k, 0, 0, 0]⟩

/-- `W = -1 - ζ₁₀ + ζ₁₀² + ζ₁₀³` in `ℤ[ζ₁₀]` (`ofZeta5 pointW`). -/
def w10 : CycPt 10 := ⟨#[-1, -1, 1, 1]⟩

/-- `-W` in `ℤ[ζ₁₀]`. -/
def negW10 : CycPt 10 := ⟨#[1, 1, -1, -1]⟩

/-- The cut `-φ⁻¹ u = ζ₁₀ - ζ₁₀²` in `ℤ[ζ₁₀]` (`ofZeta5 cutTen₁`). -/
def cut10₁ : CycPt 10 := ⟨#[0, 1, -1, 0]⟩

/-- The cut `u = -1 + ζ₁₀ - ζ₁₀² + ζ₁₀³` in `ℤ[ζ₁₀]` (`ofZeta5 cutTen₂`). -/
def cut10₂ : CycPt 10 := ⟨#[-1, 1, -1, 1]⟩

/-- `0` in `ℤ[ζ₁₀]`. -/
def zero10 : CycPt 10 := ⟨#[0, 0, 0, 0]⟩

/-- The words of order 10 (`TDCSG.Ten.word₁`, `word₂`, `word₃`). -/
def wordsTen : List (List Letter) :=
  [[.b, .b, .aInv, .bInv], [.a, .b, .aInv, .aInv], [.a, .a, .a, .bInv, .bInv, .bInv]]

/-- The pieces `[-W, -φ⁻¹ u]`, `[-φ⁻¹ u, u]`, `[u, W]` of order 10, with the ends of their images:
the first two move by `2φ⁻¹ u`, the third by `-2φ u`. -/
def piecesTen : List ((Zeta5 × Zeta5) × (Zeta5 × Zeta5)) :=
  let shift₁ := (phiInv + phiInv) * dirU
  let shift₃ := -((phiInv + Zeta5.ofInt 1 + phiInv + Zeta5.ofInt 1) * dirU)
  [((-pointW, cutTen₁), (-pointW + shift₁, cutTen₁ + shift₁)),
   ((cutTen₁, cutTen₂), (cutTen₁ + shift₁, cutTen₂ + shift₁)),
   ((cutTen₂, pointW), (cutTen₂ + shift₃, pointW + shift₃))]

/-! ### The instances the figures show -/

-- The radius line: `2 < R < 3` (`4 < 3 + φ < 9`), so the ticks 0, 1, R, 3 are in this order.
#guard QSqrt.lt (rat 4) threePlusPhi && QSqrt.lt threePlusPhi (rat 9)

-- Chapter 1: `p = 9` is inside the disk of radius 10 about 0 and `q = 11` outside, 2 apart; the
-- turn moves `p` to `9ζ⁴` and fixes `q`, and then `|ĥ(p) - ĥ(q)|² = 301 - 99φ`, more than 100.
#guard QSqrt.lt nearInside.normSq (rat (ballRadius * ballRadius)) &&
  QSqrt.lt (rat (ballRadius * ballRadius)) nearOutside.normSq &&
  (nearInside - nearOutside).normSq == rat 4 && ballSpoke.normSq == rat 100 &&
  (nearInsideImage - nearOutside).normSq == rat 301 - phi * rat 99 &&
  QSqrt.lt (rat 100) (nearInsideImage - nearOutside).normSq

-- Chapter 1: the disks of radii 4/5 and 7/10 about ∓1 are disjoint (4/5 + 7/10 < 2); `x` lies in
-- the left one, `y` in the right one, each at distance `φ⁻¹` from its centre; `a` turns `x` to
-- `-1 + φ⁻¹ ζ` and fixes `y`, `b` turns `y` to `1 + φ⁻¹ ζ` and fixes `x`.
#guard disjointLeft + disjointRight < 2 &&
  (leftSample - leftCentre).normSq == phiInvReal * phiInvReal &&
  (rightSample - rightCentre).normSq == phiInvReal * phiInvReal &&
  Letter.a.act (rat (disjointLeft * disjointLeft)) leftSample == leftCentre + phiInv * zeta 1 &&
  Letter.a.act (rat (disjointLeft * disjointLeft)) rightSample == rightSample &&
  Letter.b.act (rat (disjointRight * disjointRight)) rightSample == rightCentre + phiInv * zeta 1 &&
  Letter.b.act (rat (disjointRight * disjointRight)) leftSample == leftSample &&
  QSqrt.lt (leftSample - leftCentre).normSq (rat (disjointLeft * disjointLeft)) &&
  QSqrt.lt (rightSample - rightCentre).normSq (rat (disjointRight * disjointRight))

-- Chapter 2: at radius 3/2, `0` is in both disks, `a(0) = -1 + ζ⁴` is in the left disk and
-- outside the right one (`|a(0) - 1|² = 7 - 2φ`).
#guard Letter.a.act r2ThreeHalves origin == aZero &&
  Letter.a.covers r2ThreeHalves origin && Letter.b.covers r2ThreeHalves origin &&
  Letter.a.covers r2ThreeHalves aZero && !Letter.b.covers r2ThreeHalves aZero &&
  (aZero - rightCentre).normSq == rat 7 - phi * rat 2

-- Chapter 2: at radius 21/10 the word `a b b a` moves `0` three times and leaves it fixed at the
-- last letter, the point being outside the left disk then; the five points are those listed.
#guard stepPoints.length == 5 &&
  stepPoints == [origin, aZero, rightCentre + (aZero - rightCentre) * zeta 4,
    rightCentre + (aZero - rightCentre) * zeta 3, rightCentre + (aZero - rightCentre) * zeta 3] &&
  ((stepWord.zip stepPoints).map fun (l, z) => l.covers r2Step z) == [true, true, true, false]

-- Chapter 3: before every letter both ends of each piece lie in the letter's closed disk at the
-- critical radius, and each word carries its piece onto the chord translated by `(2φ - 2) E`
-- (words 1, 2) or `(2φ - 4) E` (word 3).
#guard [1, 2, 3].all wordChecks &&
  (wordPath 1).getLast? == some (-chordEnd + (phiInv + phiInv) * chordEnd,
    cutF + (phiInv + phiInv) * chordEnd) &&
  (wordPath 2).getLast? == some (cutF + (phiInv + phiInv) * chordEnd,
    cutG + (phiInv + phiInv) * chordEnd) &&
  (wordPath 3).getLast? == some (cutG + (phiInv + phiInv) * chordEnd - Zeta5.ofInt 2 * chordEnd,
    chordEnd + (phiInv + phiInv) * chordEnd - Zeta5.ofInt 2 * chordEnd)

-- Chapter 3: the first 24 returns stay in `[-1, 1)`, each has the word of its piece, and they are
-- pairwise distinct; `t₁ = 2φ - 4`.
#guard (chordRows 24).size == 25 &&
  (chordRows 24).all (fun (w, t) => QSqrt.le (rat (-1)) t && QSqrt.lt t (rat 1) &&
    (if w == 1 then QSqrt.le t (rat 1 - phi) else if w == 2 then
      QSqrt.lt (rat 1 - phi) t && QSqrt.lt t (rat 3 - phi * rat 2)
      else QSqrt.le (rat 3 - phi * rat 2) t)) &&
  ((chordRows 24).map (phiForm ·.2)).toList.eraseDups.length == 25 &&
  phiText ((chordRows 24)[1]!.2) == "2φ − 4"

-- Chapter 3: the disk tests that hold with equality (an end on the boundary circle).
#guard (wordEqualities 1).map (·.1) == [2, 3] && (wordEqualities 2).map (·.1) == [1, 2] &&
  (wordEqualities 3).map (·.1) == [0, 1, 4, 5]

-- Order 8: the basis coordinates agree with the engine's `ζ₈` (multiplying by `ζ₈` is multiplying
-- the coordinates by `(√2/2, √2/2)`), `p* = (1 - √2/2, 1 - 3√2/2)` lies on the left circle of
-- squared radius `10 - 5√2` and inside the right disk (`6 - 3√2`), as the engine also decides,
-- and the seed word `b b a b`, every disk test holding, carries `p*` to `q₀ = p* + 4(√2 - 1) i`.
#guard (List.range 4).all (fun j =>
  let e : CycPt 8 := ⟨field8.pows[j]!⟩
  (CycPt.coords8 ⟨field8.mulZeta e.c⟩) == cmul (basis8[1]!) e.coords8) &&
  pStar8.coords8 == (⟨1, -1 / 2⟩, ⟨1, -3 / 2⟩) &&
  distSq pStar8.coords8 (centre8 (-1)).coords8 == ⟨10, -5⟩ &&
  distSq pStar8.coords8 (centre8 1).coords8 == ⟨6, -3⟩ &&
  QSqrt.lt (distSq pStar8.coords8 (centre8 1).coords8) ⟨10, -5⟩ &&
  (DiskTest.make field8 r2Eight).exactDecide pStar8.c 1 == .boundary &&
  (DiskTest.make field8 r2Eight).exactDecide pStar8.c (-1) == .exact true &&
  engineWord field8 r2Eight seed8 pStar8.c == some (true, (orbit8 0).c) &&
  (orbit8 0).coords8 == (⟨1, -1 / 2⟩, ⟨-3, 5 / 2⟩)

-- Order 8: the drawn points are the engine's: `q₀`, `q₁` are `orbit8 0`, `orbit8 1`, and the
-- centres are `∓1` of `ℤ[ζ₈]`.
#guard q8₀.c == (orbit8 0).c && q8₁.c == (orbit8 1).c && (centre8 (-1)).c == field8.ofInt (-1) &&
  (centre8 1).c == field8.ofInt 1

-- Order 12 and 10: the drawn points are the engine's.
#guard chordDir12 == field12.add field12.pows[5]! field12.pows[6]! &&
  orbit12.c == field12.add pStar12.c (field12.mul (field12.sub (field12.ofInt 14)
    (field12.smul 8 sqrt3)) chordDir12) &&
  pStar12Conj.c == field12.conj pStar12.c && (centre12 1).c == field12.ofInt 1 &&
  w10.c == (ofZeta5 pointW).c && negW10.c == (ofZeta5 (-pointW)).c &&
  cut10₁.c == (ofZeta5 cutTen₁).c && cut10₂.c == (ofZeta5 cutTen₂).c &&
  zero10.c == (ofZeta5 origin).c && (centre10 (-1)).c == field10.ofInt (-1)

-- Order 8: the points `q₀, q₁, q₂` lie on the vertical chord through `p*`, above it, at
-- `4(√2 - 1)^(k+1)`.
#guard [0, 1, 2].all fun k => (orbit8 k).coords8.1 == pStar8.coords8.1 &&
  QSqrt.lt pStar8.coords8.2 (orbit8 k).coords8.2

-- Order 12: the basis coordinates agree with the engine's `ζ₁₂`, `p* = (2 - √3, -4 + 2√3)` lies on
-- the left circle of squared radius `40 - 22√3` and inside the right disk (`32 - 18√3`), as the
-- engine also decides, `V = (-(1 + √3/2), 1/2)`, and the seed word `b a b b a a`, every disk test
-- holding, carries `p*` to `q₀ = p* + (14 - 8√3) V`.
#guard (List.range 4).all (fun j =>
  let e : CycPt 12 := ⟨field12.pows[j]!⟩
  (CycPt.coords12 ⟨field12.mulZeta e.c⟩) == cmul (basis12[1]!) e.coords12) &&
  pStar12.coords12 == (⟨2, -1⟩, ⟨-4, 2⟩) &&
  (CycPt.coords12 ⟨chordDir12⟩) == (⟨-1, -1 / 2⟩, ⟨1 / 2, 0⟩) &&
  distSq pStar12.coords12 (centre12 (-1)).coords12 == ⟨40, -22⟩ &&
  distSq pStar12.coords12 (centre12 1).coords12 == ⟨32, -18⟩ &&
  QSqrt.lt (distSq pStar12.coords12 (centre12 1).coords12) ⟨40, -22⟩ &&
  (DiskTest.make field12 r2Twelve).exactDecide pStar12.c 1 == .boundary &&
  (DiskTest.make field12 r2Twelve).exactDecide pStar12.c (-1) == .exact true &&
  engineWord field12 r2Twelve seed12 pStar12.c == some (true, orbit12.c) &&
  pStar12Conj.coords12 == (⟨2, -1⟩, ⟨4, -2⟩) &&
  distSq pStar12Conj.coords12 (centre12 (-1)).coords12 == ⟨40, -22⟩

-- Order 10: `ζ₁₀ = -ζ₅³` and back; `W = √5 u` lies on the left circle of squared radius `4 - φ`
-- and outside the right disk, `-W` on the right circle; the engine decides the same, and each of
-- the three words, every disk test holding, carries its piece to the image listed.
#guard (List.range 4).all (fun j => (ofZeta5 (zeta j)).toZeta5 == zeta j) &&
  (CycPt.toZeta5 ⟨field10.pows[1]!⟩) == -(zeta 3) &&
  (pointW - leftCentre).normSq == fourMinusPhi &&
  QSqrt.lt fourMinusPhi (pointW - rightCentre).normSq &&
  (-pointW - rightCentre).normSq == fourMinusPhi &&
  (pointW * pointW.conj) == Zeta5.ofInt 5 &&
  (DiskTest.make field10 r2Ten).exactDecide (ofZeta5 pointW).c 1 == .boundary &&
  (DiskTest.make field10 r2Ten).exactDecide (ofZeta5 (-pointW)).c (-1) == .boundary &&
  (wordsTen.zip piecesTen).all fun (w, (p, q), (p', q')) =>
    (engineWord field10 r2Ten w (ofZeta5 p).c).map (fun (ok, z) => ok && (CycPt.toZeta5 ⟨z⟩) == p')
        == some true &&
      (engineWord field10 r2Ten w (ofZeta5 q).c).map
        (fun (ok, z) => ok && (CycPt.toZeta5 ⟨z⟩) == q') == some true

end TDCSGFigures.Early
