/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.Data.Early
import TDCSGFigures.Data.PartTwo

/-!
# The two frames of an orbit, for any radius and word

Chapter 4 follows a word applied to a starting point `z` in two frames at once: the two disks
halved by `w ↦ (w + 1)/2` (centres `0` and `1`, radius `r/2`, the point `(y + 1)/2` moving), and the
moving frame of the proof (`TDCSG.Five.Framed`), in which the window of radius `r/2` about
`x = (z + 1)/2` stays fixed and the left and right centres `P(n)` and `P(n + eⱼ)` move. This
module computes the states of both frames exactly, for any squared radius `r² ∈ ℚ(√5)`, any
starting point of `ℤ[ζ₅]` and any word in `a`, `b`, `a⁻¹`, `b⁻¹`.

* `State`, `State.applyAt`, `statesFor`: the point `y`, the label `n` of the left centre, the
  direction index `j` (the right centre is `n + eⱼ`) and whether the last letter acted. A letter
  acts when `y` lies in its closed disk (`Early.Letter.covers`), and then:
  - `a` keeps `n` and raises `j` by one; `a⁻¹` keeps `n` and lowers `j` by one;
  - `b` keeps the right label `n + eⱼ` and raises `j`, so the left label becomes
    `n + eⱼ - eⱼ₊₁`; `b⁻¹` keeps it and lowers `j`, so the left label becomes `n + eⱼ - eⱼ₋₁`.
  A letter that does not act changes only `acted`.
* `State.framedFrom`: the framing equation `2 (x - P(n)) = ζʲ (y + 1)`, as
  `(z + 1) - 2 P(n) = ζʲ (y + 1)` in `ℤ[ζ₅]`.
* `State.stepHolds`: the geometry of one step, checked exactly in `ℤ[ζ₅]` (the general
  statements are `TDCSG.Five.framePicture_genA_genB`, `TDCSG.Five.framePicture_symm`,
  `TDCSG.Five.two_mul_sub_proj_genA`, `TDCSG.Five.two_mul_sub_proj_genB` and their forms for
  the inverses and for a letter that does not act, `TDCSG.Five.halved_genA`, `halved_genB`).
* `stepReports`, `wordReport`: for each letter of a word, whether it acts and the exact margin
  `(r/2)² - |P - x|²` of the centre of its disk against the window, with decimals for reading;
  `wordExtent`: how far the orbit reaches in either frame, and whether it closes.

`wordSummary` collects, from one computation of the states, what the pins of a word state: the
figure's word is pinned in `TDCSGFigures.Lift`, other words in `TDCSGTests.FrameWords`.
-/

namespace TDCSGFigures.Lift

open PILean PILean.Exact TDCSGFigures TDCSGFigures.Early

/-! ### States of the two frames -/

/-- One state of an orbit in both frames: the point `y`, its framing label `n` and direction index
`j`, and whether the letter that led to it acted. -/
structure State where
  /-- The point. -/
  y : Zeta5
  /-- The framing label, of weight zero: the label of the current left centre. -/
  n : Label
  /-- The direction index, in `0, …, 4`: the current right centre is `n + eⱼ`. -/
  j : Nat
  /-- Whether the letter that led here acted (`true` at the start). -/
  acted : Bool := true

/-- The state at the start of an orbit of `z`: `y = z`, `n = 0`, `j = 0`
(`TDCSG.Five.framed_self`). -/
def State.start (z : Zeta5 := origin) : State := ⟨z, zeroLabel, 0, true⟩

/-- The label `n + eⱼ` of the current right centre. -/
def State.rightLabel (s : State) : Label := shift s.n s.j 1

/-- The current left centre `P(n)` in the moving frame. -/
def State.leftCentre (s : State) : Zeta5 := proj s.n

/-- The current right centre `P(n + eⱼ)` in the moving frame. -/
def State.rightCentre (s : State) : Zeta5 := proj s.rightLabel

/-- The label of the centre of the letter's disk: the left label `n` for `a` and `a⁻¹`, the right
label `n + eⱼ` for `b` and `b⁻¹`. -/
def State.labelOf (s : State) : Letter → Label
  | .a | .aInv => s.n
  | .b | .bInv => s.rightLabel

/-- The direction index after a turn by the letter: one up for `a` and `b`, one down for their
inverses, modulo `5`. -/
def _root_.TDCSGFigures.Early.Letter.nextIndex (l : Letter) (j : Nat) : Nat :=
  match l with
  | .a | .b => (j + 1) % 5
  | .aInv | .bInv => (j + 4) % 5

/-- The letter `l` applied to a state at squared radius `r2`, as `TDCSG.Five.Framed.genA` and
`genB` update the frame. If `y` lies in the letter's closed disk, `y` turns about the disk's centre
(`Early.Letter.rotate`) and the direction index moves (`Letter.nextIndex`); `a` and `a⁻¹` keep the
left label `n`, `b` and `b⁻¹` keep the right label `n + eⱼ`, so that the left label becomes
`n + eⱼ - eⱼ'` for the new index `j'`. Otherwise only `acted` becomes `false`. -/
def State.applyAt (r2 : QSqrt5) (l : Letter) (s : State) : State :=
  if l.covers r2 s.y then
    let j' := l.nextIndex s.j
    match l with
    | .a | .aInv => { y := l.rotate s.y, n := s.n, j := j' }
    | .b | .bInv => { y := l.rotate s.y, n := shift s.rightLabel j' (-1), j := j' }
  else { s with acted := false }

/-- The states after `0, 1, …, |w|` letters of `w` applied to `z` at squared radius `r2`. -/
def statesFor (r2 : QSqrt5) (w : List Letter) (z : Zeta5 := origin) : List State :=
  w.scanl (fun s l => s.applyAt r2 l) (State.start z)

/-! ### The equations of the frames -/

/-- The framing equation `2 (x - P(n)) = ζʲ (y + 1)` of `TDCSG.Five.Framed` for `x = (z + 1)/2`,
as `(z + 1) - 2 P(n) = ζʲ (y + 1)`, checked exactly in `ℤ[ζ₅]`. -/
def State.framedFrom (z : Zeta5) (s : State) : Bool :=
  z + Zeta5.ofInt 1 - Zeta5.ofInt 2 * proj s.n == zeta s.j * (s.y + Zeta5.ofInt 1)

/-- `4 |P - x|² = |2P - (z + 1)|²` for the centre of label `m` and the window centre
`x = (z + 1)/2`, exact. -/
def windowDistSq4 (z : Zeta5) (m : Label) : QSqrt5 :=
  (Zeta5.ofInt 2 * proj m - (z + Zeta5.ofInt 1)).normSq

/-- `TDCSG.Five.InWindow` for the window about `x = (z + 1)/2`: `|2P(m) - (z + 1)|² ≤ r²`, that is
`|P(m) - x| ≤ r/2`, decided exactly. -/
def inWindowFrom (r2 : QSqrt5) (z : Zeta5) (m : Label) : Bool :=
  QSqrt.le (windowDistSq4 z m) r2

/-- The margin `(r/2)² - |P(m) - x|²` of the centre of label `m` against the window about
`x = (z + 1)/2`: positive inside, zero on the circle, negative outside. -/
def windowMargin (r2 : QSqrt5) (z : Zeta5) (m : Label) : QSqrt5 :=
  (r2 - windowDistSq4 z m) * rat (1 / 4)

/-- The geometry of one step from `s` to `t = s.applyAt r2 l`, for an orbit of `z`, checked
exactly in `ℤ[ζ₅]`:
* the letter acts exactly when the centre of its disk lies in the window, and
  `|y - c|² = 4 |P - x|²` for that disk's centre `c` and that centre `P`;
* if it acts, the centre of its disk stays, and the other centre turns about it by `ζ` (`a`, `b`)
  or `ζ⁴` (`a⁻¹`, `b⁻¹`); the halved point `(y + 1)/2` turns about the halved centre (`0` for the
  left disk, `1` for the right) by `ζ⁴` (`a`, `b`) or `ζ` (`a⁻¹`, `b⁻¹`);
* if it does not act, `y`, `n` and `j` are unchanged;
* both states satisfy the framing equation (`State.framedFrom`). -/
def State.stepHolds (r2 : QSqrt5) (z : Zeta5) (l : Letter) (s : State) : Bool :=
  let t := s.applyAt r2 l
  let m := s.labelOf l
  let acts := l.covers r2 s.y
  -- The turn of the other centre: `ζ` for a generator, `ζ⁴` for an inverse.
  let turn := match l with | .a | .b => zeta 1 | .aInv | .bInv => zeta 4
  -- The halved centre `(c + 1)/2` of the letter's disk, doubled: `c + 1`.
  let c1 := l.centre + Zeta5.ofInt 1
  let geometry :=
    if !acts then t.y == s.y && t.n == s.n && t.j == s.j && !t.acted
    else
      t.acted && t.labelOf l == m &&
      (match l with
        | .a | .aInv => t.rightCentre - proj m == turn * (s.rightCentre - proj m)
        | .b | .bInv => t.leftCentre - proj m == turn * (s.leftCentre - proj m)) &&
      t.y + Zeta5.ofInt 1 - c1 == l.turn * (s.y + Zeta5.ofInt 1 - c1)
  acts == inWindowFrom r2 z m && (s.y - l.centre).normSq == windowDistSq4 z m && geometry &&
    s.framedFrom z && t.framedFrom z

/-- Whether every step of `w` has the geometry of `State.stepHolds`, for the states `ss` of `w`
from `z` at squared radius `r2`. -/
def stepsHoldOf (r2 : QSqrt5) (z : Zeta5) (w : List Letter) (ss : List State) : Bool :=
  (w.zip ss).all fun (l, s) => s.stepHolds r2 z l

/-- Whether every step of `w` from `z` at squared radius `r2` has the geometry of
`State.stepHolds`. -/
def stepsHold (r2 : QSqrt5) (w : List Letter) (z : Zeta5 := origin) : Bool :=
  stepsHoldOf r2 z w (statesFor r2 w z)

/-- The letters of `w` that act from `z` at squared radius `r2`, in order. -/
def actPattern (r2 : QSqrt5) (w : List Letter) (z : Zeta5 := origin) : List Bool :=
  (statesFor r2 w z).tail.map (·.acted)

/-- The positions (from `1`) of the letters that do not act, read from the states of a word. -/
def idleOf (ss : List State) : List Nat :=
  ((ss.tail.map (·.acted)).zipIdx 1).filterMap fun (b, k) => if b then none else some k

/-- The positions (from `1`) of the letters of `w` that do not act. -/
def idlePositions (r2 : QSqrt5) (w : List Letter) (z : Zeta5 := origin) : List Nat :=
  idleOf (statesFor r2 w z)

/-- Whether the last of the states `ss` has the label, the direction index (modulo `5`) and the
point of the first, so both frames show the starting picture again. -/
def closesOf (ss : List State) : Bool :=
  match ss.head?, ss.getLast? with
  | some s, some t => t.y == s.y && t.n == s.n && t.j % 5 == s.j % 5
  | _, _ => false

/-- Whether the orbit of `z` under `w` at squared radius `r2` returns to its start
(`closesOf`). -/
def closes (r2 : QSqrt5) (w : List Letter) (z : Zeta5 := origin) : Bool :=
  closesOf (statesFor r2 w z)

/-! ### Reports for choosing words -/

/-- What one letter does to a state: the letter, whether it acts, the label of the centre of its
disk, that centre's exact margin `(r/2)² - |P - x|²` against the window and where it stands. -/
structure StepReport where
  /-- The position of the letter in the word, from `1`. -/
  pos : Nat
  /-- The letter. -/
  letter : Letter
  /-- Whether it acts. -/
  acts : Bool
  /-- The label of the centre of its disk. -/
  label : Label
  /-- `(r/2)² - |P - x|²`, exact. -/
  margin : QSqrt5
  /-- Where the centre stands relative to the closed window. -/
  side : Side

/-- Where a margin puts a centre: inside when positive, on the circle when zero, outside when
negative, decided exactly. -/
def sideOfMargin (m : QSqrt5) : Side :=
  if m == rat 0 then .on else if QSqrt.lt (rat 0) m then .inside else .outside

/-- The report of each letter of `w` applied to `z` at squared radius `r2`. -/
def stepReports (r2 : QSqrt5) (w : List Letter) (z : Zeta5 := origin) : List StepReport :=
  ((w.zip (statesFor r2 w z)).zipIdx 1).map fun ((l, s), k) =>
    let m := s.labelOf l
    let g := windowMargin r2 z m
    { pos := k, letter := l, acts := l.covers r2 s.y, label := m, margin := g,
      side := sideOfMargin g }

/-- An exact number `a + b √5` of `ℚ(√5)` as text, with true minus signs: `−879/1600 + √5/4`. -/
def qText (q : QSqrt5) : String :=
  let num := fun (x : Rat) => (toString x).replace "-" ""
  let root : String :=
    if q.b.num.natAbs == 1 && q.b.den == 1 then "√5"
    else if q.b.num.natAbs == 1 then s!"√5/{q.b.den}" else s!"{num q.b} √5"
  if q.b == 0 then (toString q.a).replace "-" "−"
  else if q.a == 0 then (if q.b < 0 then "−" else "") ++ root
  else s!"{(toString q.a).replace "-" "−"} {if q.b < 0 then "−" else "+"} {root}"

/-- One line of a report: position, letter, acts or idle, the centre's label, where it stands, the
exact margin with its decimal, and the decimal distance `|P - x|` against `r/2`. -/
def StepReport.text (r2 : QSqrt5) (s : StepReport) : String :=
  let side := match s.side with
    | .inside => "inside" | .on => "on the circle" | .outside => "outside"
  let dist : SqrtOf QSqrt5 := ⟨r2 * rat (1 / 4) - s.margin⟩
  let half : SqrtOf QSqrt5 := ⟨r2 * rat (1 / 4)⟩
  s!"{s.pos} {s.letter.text} {if s.acts then "acts" else "idle"}: centre {labelText s.label} " ++
    s!"{side}, (r/2)² − |P − x|² = {qText s.margin} ≈ {decimalText s.margin 5}, " ++
    s!"|P − x| ≈ {decimalText dist 5} against r/2 ≈ {decimalText half 5}"
where
  /-- The integer vector of a label, as text. -/
  labelText (n : Label) : String :=
    "(" ++ ", ".intercalate (n.toList.map fun k => if k < 0 then s!"−{-k}" else toString k) ++ ")"

/-- How far an orbit reaches in each frame: the largest `|(y + 1)/2|²` of the halved point (its
squared distance from the halved left centre `0`), the largest `|P - x|²` of any left or right
centre from the window centre, both exact, and whether the orbit closes (`closes`). -/
structure Extent where
  /-- The largest squared distance of the halved point from `0`. -/
  halvedSq : QSqrt5
  /-- The largest squared distance of a centre from `x`. -/
  centreSq : QSqrt5
  /-- Whether the orbit returns to its start. -/
  closed : Bool

/-- The larger of two numbers of `ℚ(√5)`, exact. -/
def qMax (p q : QSqrt5) : QSqrt5 := if QSqrt.lt p q then q else p

/-- The extent of the states `ss` of an orbit of `z`. -/
def extentOf (z : Zeta5) (ss : List State) : Extent :=
  { halvedSq := ss.foldl (fun m s => qMax m ((s.y + Zeta5.ofInt 1).normSq * rat (1 / 4))) (rat 0)
    centreSq := ss.foldl (fun m s => qMax (qMax m (windowDistSq4 z s.n * rat (1 / 4)))
      (windowDistSq4 z s.rightLabel * rat (1 / 4))) (rat 0)
    closed := closesOf ss }

/-- The extent of the orbit of `z` under `w` at squared radius `r2`. -/
def wordExtent (r2 : QSqrt5) (w : List Letter) (z : Zeta5 := origin) : Extent :=
  extentOf z (statesFor r2 w z)

/-- The word as text, `a b a⁻¹ …`. -/
def wordText (w : List Letter) : String := " ".intercalate (w.map Letter.text)

/-- The report of `w` applied to `z` at squared radius `r2`: one line per letter
(`StepReport.text`), then the idle positions, the extents in both frames with decimals of the
distances, whether the orbit closes and whether every step has the geometry of
`State.stepHolds`. -/
def wordReport (r2 : QSqrt5) (w : List Letter) (z : Zeta5 := origin) : String :=
  let e := wordExtent r2 w z
  let lines := (stepReports r2 w z).map (·.text r2)
  let dec := fun (q : QSqrt5) => decimalText (⟨q⟩ : SqrtOf QSqrt5) 4
  "\n".intercalate <| [s!"word {wordText w}:"] ++ lines ++ [
    s!"idle letters at {idlePositions r2 w z}; " ++
    s!"largest |(y + 1)/2| ≈ {dec e.halvedSq} (squared {qText e.halvedSq}); " ++
    s!"largest |P − x| ≈ {dec e.centreSq} (squared {qText e.centreSq}); " ++
    s!"closes: {e.closed}; steps hold: {stepsHold r2 w z}"]

/-- A word written in the letters `a`, `b`, `A = a⁻¹`, `B = b⁻¹`; other characters are skipped. -/
def parseWord (s : String) : List Letter :=
  s.toList.filterMap fun
    | 'a' => some .a | 'b' => some .b | 'A' => some .aInv | 'B' => some .bInv | _ => none

/-- The inverse of a word: its letters inverted, in the reverse order. -/
def inverseWord (w : List Letter) : List Letter :=
  w.reverse.map fun
    | .a => .aInv | .aInv => .a | .b => .bInv | .bInv => .b

/-! ### One summary per word -/

/-- What the pins of a word state: the idle positions, whether every step has the geometry of
`State.stepHolds`, whether the orbit closes, and its squared extents in both frames
(`wordExtent`). -/
structure WordSummary where
  /-- The positions (from `1`) of the letters that do not act. -/
  idle : List Nat
  /-- Whether every step has the geometry of `State.stepHolds`. -/
  stepsHold : Bool
  /-- Whether the orbit returns to its start. -/
  closes : Bool
  /-- The largest `|(y + 1)/2|²`. -/
  halvedSq : QSqrt5
  /-- The largest `|P - x|²` of a left or right centre. -/
  centreSq : QSqrt5
  deriving DecidableEq

/-- The summary of `w` applied to `z` at squared radius `r2`, from one computation of the states:
it equals `⟨idlePositions r2 w z, stepsHold r2 w z, closes r2 w z, (wordExtent r2 w z).halvedSq,
(wordExtent r2 w z).centreSq⟩`. -/
def wordSummary (r2 : QSqrt5) (w : List Letter) (z : Zeta5 := origin) : WordSummary :=
  let ss := statesFor r2 w z
  let e := extentOf z ss
  { idle := idleOf ss, stepsHold := stepsHoldOf r2 z w ss, closes := e.closed,
    halvedSq := e.halvedSq, centreSq := e.centreSq }

end TDCSGFigures.Lift
