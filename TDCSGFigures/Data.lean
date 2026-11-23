/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean
import TDCSGCompute.Orbit

/-!
# The exact objects the figures draw

Every number a figure decides with is exact: points of `ℤ[ζ₅]` (`PILean.Exact.Zeta5`, the
coefficients of `1, ζ, ζ², ζ³`), real numbers of `ℚ(√5)` (`PILean.Exact.QSqrt5`, `a + b √5`), and
the critical radius as the exact square root `R = √(3 + φ)`. Floating point enters only where
PILean converts a decided point to page coordinates.

* The chord: `ζ`, `E = ζ - ζ²`, the centres `∓1`, the crossing points `±(ζ - ζ⁴)` of the two
  circles of radius `R`, and the pieces of the three words, cut at `(1 - φ) E` and `(3 - 2φ) E`.
* The constants of Part II: `φ`, the level period `L = φ - 1/2`, the cut `κ = (1 + L) / 2` and the
  margin `η = (3 + φ - r²) / 16`.
* Integer labels `n = (n₀, …, n₄)`, their projection `P(n) = ∑ nⱼ ζʲ`, their weight, the window
  test `|P(n) - x| ≤ r/2` (`TDCSG.Five.InWindow`) and the good-level test
  (`TDCSG.Five.IsGoodLevel`), for rational window centres `x` and radii with `r² ∈ ℚ(√5)`.
* Orbits of the two generators, computed by the exact orbit engine `TDCSGCompute`: every disk
  decision is its exact sign test (`DiskTest.exactDecide`), so points on a boundary circle are
  recognised as such.

The `#guard` lines at the end recompute the instances the figures show and stop the build if one
of them no longer has the property its caption states.
-/

namespace TDCSGFigures

open PILean PILean.Exact

/-! ### The chord at the critical radius -/

/-- `ζʲ`, `ζ = exp(2πi/5)`. -/
def zeta (j : Nat) : Zeta5 := Zeta5.pow j

/-- The end `E = ζ - ζ²` of the critical chord (`TDCSG.Five.pointE`). -/
def chordEnd : Zeta5 := zeta 1 - zeta 2

/-- The upper crossing point `ζ - ζ⁴ = 2i sin 72°` of the two circles of radius `R`; the lower one
is its negative. -/
def crossing : Zeta5 := zeta 1 - zeta 4

/-- The centre `-1` of the left disk. -/
def leftCentre : Zeta5 := Zeta5.ofInt (-1)

/-- The centre `1` of the right disk. -/
def rightCentre : Zeta5 := Zeta5.ofInt 1

/-- The origin. -/
def origin : Zeta5 := Zeta5.zero

/-- The golden ratio `φ = (1 + √5) / 2`. -/
def phi : QSqrt5 := ⟨1 / 2, 1 / 2⟩

/-- `3 + φ`, the square of the critical radius. -/
def threePlusPhi : QSqrt5 := ⟨7 / 2, 1 / 2⟩

/-- The critical radius `R = √(3 + φ)`. -/
def critical : SqrtOf QSqrt5 := ⟨threePlusPhi⟩

/-- `φ⁻¹ = φ - 1 = ζ + ζ⁴`, real and between `0` and `1`. -/
def phiInv : Zeta5 := zeta 1 + zeta 4

/-- The cut `(1 - φ) E = -φ⁻¹ E` between the pieces of the first and the second word. -/
def firstCut : Zeta5 := -(phiInv * chordEnd)

/-- The cut `(3 - 2φ) E = -φ⁻³ E` between the pieces of the second and the third word. -/
def secondCut : Zeta5 := -(phiInv * phiInv * phiInv * chordEnd)

/-- A point on the left circle of radius `R`, to its upper left: `E` turned by `ζ²` about `-1`,
so `|spokeEnd + 1| = |E + 1| = R`. -/
def spokeEnd : Zeta5 := leftCentre + (chordEnd - leftCentre) * zeta 2

/-! ### The constants of Part II -/

/-- The rational `q` in `ℚ(√5)`. -/
def rat (q : Rat) : QSqrt5 := ⟨q, 0⟩

/-- The period `L = φ - 1/2 = √5 / 2` of the level phases. -/
def period : QSqrt5 := phi - rat (1 / 2)

/-- The cut `κ = (1 + L) / 2 = (2φ + 1) / 4` of the lens estimate. -/
def kappa : QSqrt5 := (rat 1 + period) * rat (1 / 2)

/-- The margin `η = (3 + φ - r²) / 16` at the squared radius `r2`. -/
def margin (r2 : QSqrt5) : QSqrt5 := (threePlusPhi - r2) * rat (1 / 16)

/-- The phase step `1 + φ/2` between consecutive levels. -/
def slope : QSqrt5 := rat 1 + phi * rat (1 / 2)

/-! ### Integer labels -/

/-- An integer label `n = (n₀, …, n₄)` (`TDCSG.Five.Label`). -/
abbrev Label := Array Int

/-- The projection `P(n) = ∑ⱼ nⱼ ζʲ`. -/
def proj (n : Label) : Zeta5 := Zeta5.reduce n

/-- The weight `∑ⱼ nⱼ`. -/
def weight (n : Label) : Int := n.foldl (· + ·) 0

/-- `n + k eⱼ`. -/
def shift (n : Label) (j : Nat) (k : Int) : Label := n.modify j (· + k)

/-- The label `0`. -/
def zeroLabel : Label := #[0, 0, 0, 0, 0]

/-- `TDCSG.Five.InWindow` for a rational real window centre `x`: `|P(n) - x|² ≤ r²/4`, decided
exactly in `ℚ(√5)` as `|q P(n) - p|² ≤ q² r²/4` for `x = p/q`. -/
def inWindow (r2 : QSqrt5) (x : Rat) (n : Label) : Bool :=
  let q : Int := x.den
  let w := Zeta5.ofInt q * proj n - Zeta5.ofInt x.num
  QSqrt.le w.normSq (r2 * rat (((q * q : Int) : Rat) / 4))

/-- The floor of a real number of `ℚ(√5)`, from balls of increasing precision; `none` if no
precision up to 4096 bits decides it (an irrational number is decided at some precision). -/
def floorQ (t : QSqrt5) : Option Int := Id.run do
  if t.b == 0 then return some t.a.floor
  for k in [64, 128, 256, 512, 1024, 2048, 4096] do
    let b := QSqrt.ball t k
    if b.lo.floor == b.hi.floor then return some b.lo.floor
  return none

/-- The phase `(1 + φ/2) m + 1/2 - Re(x ζ⁻ʲ)` of level `m` of coordinate `j`, for a real
window centre `x` (so `Re(x ζ⁻ʲ) = x Re ζʲ`). -/
def phase (x : Rat) (j : Nat) (m : Int) : QSqrt5 :=
  slope * rat m + rat (1 / 2) - rat x * (zeta j).realPart

/-- `TDCSG.Five.IsGoodLevel`, decided exactly: the phase is farther than `L/2 - η` from every
point of `L ℤ`. The nearest points of `L ℤ` are `L k` and `L (k + 1)` with `k = ⌊phase / L⌋`;
`none` if that floor is not decided. -/
def isGoodLevel (r2 : QSqrt5) (x : Rat) (j : Nat) (m : Int) : Option Bool := do
  let a := phase x j m
  -- `1 / L = 2 / √5 = (2/5) √5`.
  let k ← floorQ (a * ⟨0, 2 / 5⟩)
  let bound := period * rat (1 / 2) - margin r2
  let below := a - period * rat k
  let above := period * rat (k + 1) - a
  return QSqrt.lt bound below && QSqrt.lt bound above

/-- The labels reachable from `0` in the centre graph (`TDCSG.Five.centerGraph`) at squared radius
`r2` and window centre `x`, found by a search of at most `fuel` labels; `none` if the search did
not finish. Weight-zero labels gain `eⱼ`, weight-one labels lose it. -/
def component (r2 : QSqrt5) (x : Rat) (fuel : Nat := 256) : Option (Array Label) := Id.run do
  let mut seen : Array Label := #[zeroLabel]
  let mut todo : List Label := [zeroLabel]
  for _ in [0:fuel] do
    match todo with
    | [] => return some seen
    | n :: rest =>
      todo := rest
      let sign : Int := if weight n == 0 then 1 else -1
      for j in [0:5] do
        let m := shift n j sign
        if inWindow r2 x n && inWindow r2 x m && !seen.contains m then
          seen := seen.push m
          todo := m :: todo
  return if todo.isEmpty then some seen else none

/-! ### The three words on the chord -/

/-- The word applied at the parameter `t` of the point `tE` and the parameter it moves the point
to (`TDCSG.Five.word₁`, `word₂`, `word₃`): the first two add `2φ - 2`, the third adds `2φ - 4`. -/
def chordStep (t : QSqrt5) : Nat × QSqrt5 :=
  if QSqrt.le t (rat 1 - phi) then (1, t + phi * rat 2 - rat 2)
  else if QSqrt.lt t (rat 3 - phi * rat 2) then (2, t + phi * rat 2 - rat 2)
  else (3, t + phi * rat 2 - rat 4)

/-- The parameters `t₀ = 0, t₁, …, tₖ` of the first `k` returns of the orbit of zero to the
chord, with the word applied before each. -/
def chordReturns (k : Nat) : Array (Nat × QSqrt5) := Id.run do
  let mut out : Array (Nat × QSqrt5) := #[(0, rat 0)]
  let mut t := rat 0
  for _ in [0:k] do
    let (w, t') := chordStep t
    out := out.push (w, t')
    t := t'
  return out

/-! ### Orbits computed by the exact engine -/

open TDCSGCompute in
/-- `ℤ[ζ₅]` with the tables of the orbit engine. -/
def field : CycField := CycField.make 5

/-- A squared radius for the orbit engine and for the figures: `r² = num` with `num ∈ ℚ(√5)`
given in the power basis of `ℤ[ζ₅]` over the integer denominator `den`. -/
structure RadiusSq where
  /-- The numerator, a real element of `ℤ[ζ₅]` (coefficients of `1, ζ, ζ², ζ³`). -/
  num : Array Int
  /-- The positive denominator. -/
  den : Nat

/-- The squared radius `(p/q)²` of a rational radius. -/
def RadiusSq.ofRat (r : Rat) : RadiusSq := ⟨#[r.num * r.num, 0, 0, 0], r.den * r.den⟩

/-- The squared critical radius `3 + φ = 3 - ζ² - ζ³`. -/
def RadiusSq.critical : RadiusSq := ⟨#[3, 0, -1, -1], 1⟩

/-- The squared radius in `ℚ(√5)`. -/
def RadiusSq.value (r2 : RadiusSq) : QSqrt5 := (Zeta5.reduce r2.num).realPart * rat (1 / (r2.den : Rat))

/-- Where a point stands relative to a closed disk, as the engine decides it. -/
inductive Side where
  /-- Strictly inside. -/
  | inside
  /-- On the boundary circle. -/
  | on
  /-- Strictly outside. -/
  | outside
  deriving BEq, Inhabited, Repr

/-- The side in PILean's terms, for a recorded incidence. -/
def Side.incidence : Side → Plane.Incidence
  | .inside => .inside
  | .on => .on
  | .outside => .outside

/-- Where a point stands relative to the lens, the intersection of two closed disks, given where
it stands relative to each: inside both is inside, outside either is outside, and otherwise it is
on the lens's boundary. -/
def Side.lens : Side → Side → Side
  | .inside, .inside => .inside
  | .outside, _ | _, .outside => .outside
  | _, _ => .on

/-- An orbit point with where it stands relative to the left and the right disk. -/
structure OrbitPoint where
  /-- The point. -/
  z : Zeta5
  /-- Relative to the left disk. -/
  left : Side
  /-- Relative to the right disk. -/
  right : Side

/-- An orbit, breadth first from its starting point, and whether it was exhausted (otherwise the
search stopped at its cap). -/
structure Orbit where
  /-- The points in the order the search found them. -/
  points : Array OrbitPoint
  /-- Whether the orbit is finite and every point of it is listed. -/
  complete : Bool

open TDCSGCompute in
/-- The exact side of `z` relative to the disk about `-side` (`side = 1` the left disk). -/
def sideOf (T : DiskTest) (z : Elem) (side : Int) : Except String Side :=
  match T.exactDecide z side with
  | .exact true => .ok .inside
  | .exact false => .ok .outside
  | .boundary => .ok .on
  | _ => .error s!"the disk test of {z} was not decided"

open TDCSGCompute in
/-- Where `z` stands relative to the left and the right closed disk of squared radius `r2`, by the
engine's exact sign tests. -/
def sides (r2 : RadiusSq) (z : Zeta5) : Except String (Side × Side) := do
  let T := DiskTest.make field ⟨r2.num, r2.den⟩
  let w : Elem := Zeta5.normalForm z.c
  return (← sideOf T w 1, ← sideOf T w (-1))

open TDCSGCompute in
/-- The orbit of `start` under the two generators at squared radius `r2`, breadth first, by the
engine's exact disk decisions, stopped after `cap` points. -/
def orbit (r2 : RadiusSq) (start : Zeta5 := origin) (cap : Nat := 4000) : Except String Orbit := do
  let F := field
  let T := DiskTest.make F ⟨r2.num, r2.den⟩
  let start : Elem := Zeta5.normalForm start.c
  let mut set := PointSet.empty F.deg 2
  match set.insert start with
  | .added s => set := s
  | _ => throw "the starting point does not fit the store"
  let mut out : Array OrbitPoint := #[]
  let mut head := 0
  while head < set.size && head < cap do
    let z := set.get head
    let l ← sideOf T z 1
    let r ← sideOf T z (-1)
    out := out.push ⟨⟨z⟩, l, r⟩
    let imgs := (if l != .outside then #[F.rotCW z 1, F.rotCCW z 1] else #[]) ++
      (if r != .outside then #[F.rotCW z (-1), F.rotCCW z (-1)] else #[])
    for w in imgs do
      match set.insert w with
      | .added s | .present s => set := s
      | .overflow _ => throw s!"coefficient overflow at {w}"
    head := head + 1
  return { points := out, complete := head == set.size }

/-! ### The instances the figures show -/

-- The window at `r = 1.95`, `x = 1/2` holds exactly the unit steps `1`, `ζ`, `ζ⁴`.
#guard (List.range 5).filter (fun j => inWindow (rat (39 / 20 * (39 / 20))) (1 / 2)
  (shift zeroLabel j 1)) == [0, 1, 4]

-- At `r = 1.8`, `x = 0.87`, the good levels of coordinate `0` in `[-13, 9]` are `-10`, `-2`, `3`.
#guard ((List.range 23).map (fun i : Nat => (i : Int) - 13)).filter
  (fun m => isGoodLevel (rat (81 / 25)) (87 / 100) 0 m == some true) == [-10, -2, 3]

-- The terminal crossing at `r = 2.12`, `x = 0.472`: `n = (4, -3, 1, 1, -3)` has weight zero and
-- sits at the good level `n₀ = 4`; `n` and `n + e₀` are in the window, so are the other
-- neighbours `n + e_k` of `n`, and no other neighbour `n + e₀ - e_k` of `n + e₀` is.
#guard
  let r2 := rat (53 / 25 * (53 / 25))
  let x : Rat := 472 / 1000
  let n : Label := #[4, -3, 1, 1, -3]
  let leaf := shift n 0 1
  weight n == 0 && isGoodLevel r2 x 0 4 == some true && inWindow r2 x n && inWindow r2 x leaf &&
    [1, 2, 3, 4].all (fun k => inWindow r2 x (shift n k 1)) &&
    [1, 2, 3, 4].all (fun k => !inWindow r2 x (shift leaf k (-1)))

-- The component of `0` in the centre graph at `r = 1.95`, `x = 1/2` has 18 labels.
#guard (component (rat (39 / 20 * (39 / 20))) (1 / 2)).map (·.size) == some 18

-- The first three returns of the orbit of zero to the chord stay in `[-1, 1)` and apply the words
-- 3, 1 and 3 (`t₁ = 2φ - 4`, `t₂ = 4φ - 6`, `t₃ = 6φ - 10`).
#guard (chordReturns 3).map (·.1) == #[0, 3, 1, 3] &&
  (chordReturns 3).all fun (_, t) => QSqrt.le (rat (-1)) t && QSqrt.lt t (rat 1)

-- The orbit of `0` has 9 points at `r = 3/2`, 71 at `r = 2`, 801 at `r = 21/10`.
#guard [(3 / 2 : Rat), 2, 21 / 10].map (fun r =>
  match orbit (RadiusSq.ofRat r) origin 100000 with
  | .ok o => (o.points.size, o.complete)
  | .error _ => (0, false)) == [(9, true), (71, true), (801, true)]

end TDCSGFigures
