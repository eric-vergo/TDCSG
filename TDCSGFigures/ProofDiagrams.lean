/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI Codex
-/
import TDCSGFigures.Chord
import TDCSGFigures.Confinement
import TDCSGFigures.Parts
import TDCSGFigures.Data.Moves

/-!
# The interval exchange, coordinate barriers, and the threshold

* `exchangedIntervals`: an animation of the interval exchange of one return: copies of the three
  pieces of `[-1, 1)` slide one by one, each by the exact move of its word, from the row before
  the return to the row after. Its last key frame is the figure of the two rows
  (`exchangedIntervalsFinal`), which keeps its linked theorem; every slide is checked exactly
  (`intervalArrives`).
* `coordinateBox`: the coordinate ranges of the component of `0` at `r = 1.95`, `x = 1/2`.
* `radiusThreshold`: both halves of the classification of the radius.
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- Endpoints before and after the word, in chord coordinates. -/
def returnInterval (i : Nat) (after : Bool) : QSqrt5 × QSqrt5 :=
  let shift := if !after then rat 0 else phi * rat 2 - rat (if i == 3 then 4 else 2)
  (pieceEnds[i - 1]! + shift, pieceEnds[i]! + shift)

/-- The height of the row before (`1/2`) or after (`0`) the return. -/
def intervalRowY (after : Bool) : QSqrt5 := rat (if after then (0 : Rat) else 1 / 2)

/-- One piece of an interval row with its word number; the row after the return is made of the
actors `"after-<i>"` and `"after-label-<i>"`. -/
def intervalBand (i : Nat) (after : Bool) : Array Item :=
  let (a, b) := returnInterval i after
  let y := intervalRowY after
  let tag := fun (it : Item) (id : String) => if after then it.withId id else it
  #[tag (Plane.Exact.segment (a, y) (b, y) |>.width 5 |>.role (pieceRole i)
      |>.named s!"piece {i}, {if after then "after" else "before"} the word") s!"after-{i}",
    tag (Plane.Exact.label (toString i) ((a + b) * rat (1 / 2), y) .above |>.role (pieceRole i))
      s!"after-label-{i}"]

/-- The names of the rows and the ends of the interval. -/
def intervalNames : Array Item := #[
  Plane.Exact.label "before" ((-5 / 4 : Rat), (1 / 2 : Rat)) .left,
  Plane.Exact.label "after" ((-5 / 4 : Rat), (0 : Rat)) .left,
  Plane.Exact.label "−1" ((-1 : Rat), (0 : Rat)) .below,
  Plane.Exact.label "1" ((1 : Rat), (0 : Rat)) .below]

/-- The figure of the three pieces on a common scale before and after their words, the last key
frame of `exchangedIntervals`. -/
def exchangedIntervalsFinal : Plane.Figure where
  width := figureWidth
  padding := 18
  style := houseStyle
  checks := .fail
  items := ([false, true].toArray.flatMap fun after =>
    #[1, 2, 3].flatMap fun i => intervalBand i after) ++ intervalNames
  info := { title := "The three pieces before and after one return" }

/-- The copy of piece `i` that slides (actor `"piece-<i>"`): at the row before the return until
its word has moved it, at its place in the row after from then on. -/
def intervalCopy (i : Nat) (moved : Bool) : Item :=
  let (a, b) := returnInterval i moved
  let y := intervalRowY moved
  Plane.Exact.segment (a, y) (b, y) |>.width 5 |>.role (pieceRole i)
    |>.named s!"a copy of piece {i}, moved by word {i}" |>.withId s!"piece-{i}"

/-- The items of key `k ≤ 3` of `exchangedIntervals`: the row before the return, the copies of the
pieces, the first `k` of them moved by their words, and the names. -/
def intervalKeyItems (k : Nat) : Array Item :=
  (#[1, 2, 3].flatMap fun i => intervalBand i false) ++
    #[1, 2, 3].map (fun i => intervalCopy i (decide (i ≤ k))) ++ intervalNames

/-- The captions of the keys of `exchangedIntervals`. -/
def intervalCaptions : Array String := #[
  "The three pieces of [−1, 1) before one return, in the order 1, 2, 3 (top row). The word of \
    each piece moves it along the chord.",
  "Word 1 moves piece 1, −1 ≤ t ≤ 1 − φ, by 2φ − 2 to the right.",
  "Word 2 moves piece 2, 1 − φ < t < 3 − 2φ, by 2φ − 2 to the right, beside the image of piece \
    1.",
  "Word 3 moves piece 3, 3 − 2φ ≤ t < 1, by 2φ − 4 to the left, to the left end of the \
    interval.",
  "After one return the pieces read 3, 1, 2 on the same interval. Joined into a circle of \
    circumference two, the three moves are one rotation by 2φ − 2 = 2/φ."]

/-- Key `k` of `exchangedIntervals`: the items `intervalKeyItems k` in the frame of
`exchangedIntervalsFinal` for `k ≤ 3`, the figure `exchangedIntervalsFinal` after. -/
def intervalKey (k : Nat) : Plane.Figure :=
  if 3 < k then exchangedIntervalsFinal
  else { exchangedIntervalsFinal with items := intervalKeyItems k,
                                      info := { title := intervalCaptions.getD k "" } }

/-- The slide of piece `i`: from its place in the row before the return to its place in the row
after, `(s, -1/2)` with `s` the move of its word. -/
def intervalSlide (i : Nat) : QSqrt5 × QSqrt5 :=
  ((returnInterval i true).1 - (returnInterval i false).1, intervalRowY true - intervalRowY false)

/-- The declared moves of step `k` of `exchangedIntervals`: piece `k + 1` slides for `k < 3`;
then the copies vanish while the row after the return appears. -/
def intervalMoves (k : Nat) : List (String × ExactMove (QSqrt5 × QSqrt5)) :=
  if k < 3 then [(s!"piece-{k + 1}", .slide (intervalSlide (k + 1)))]
  else [1, 2, 3].flatMap fun i =>
    [(s!"piece-{i}", .vanish), (s!"after-{i}", .appear), (s!"after-label-{i}", .appear)]

/-- The exact anchors of the actors of key `k` of `exchangedIntervals`: the ends of the copies up
to key `3`, the ends of the pieces of the row after and the points of their labels at key `4`. -/
def intervalActors (k : Nat) : List (ExactActor (QSqrt5 × QSqrt5)) :=
  if k ≤ 3 then
    [1, 2, 3].map fun i =>
      let moved := decide (i ≤ k)
      let (a, b) := returnInterval i moved
      ⟨s!"piece-{i}", [(a, intervalRowY moved), (b, intervalRowY moved)]⟩
  else
    [1, 2, 3].flatMap fun i =>
      let (a, b) := returnInterval i true
      [⟨s!"after-{i}", [(a, intervalRowY true), (b, intervalRowY true)]⟩,
        ⟨s!"after-label-{i}", [((a + b) * rat (1 / 2), intervalRowY true)]⟩]

/-- Whether every declared move of `exchangedIntervals` carries the actors of one key onto those
of the next, exactly in `ℚ(√5)²`. -/
def intervalArrives : Bool := allArrive 4 intervalMoves intervalActors

/-- The duration of a slide of a piece: as long as a turn, since a piece crosses half the
picture. -/
def intervalSlideDuration : Rat := motionPacing.turn

/-- The interval exchange of one return: copies of the three pieces of [−1, 1) slide one by one,
each by the move of its word, from the row before the return to the row after, where they read
3, 1, 2. The last key frame is the figure of the two rows, `exchangedIntervalsFinal`. -/
@[figure]
def exchangedIntervals : MotionPanels where
  panels := #[{ motion := { keys := ((List.range 5).map intervalKey).toArray,
                            steps := ((List.range 4).map fun k =>
                              exactStep (intervalMoves k)).toArray } }]
  captions := intervalCaptions
  pacing := motionPacing
  timing := ((List.range 4).map fun k =>
    moveTiming (intervalMoves k) intervalSlideDuration).toArray
  info := { title := "The three pieces before and after one return"
            description := "Two rows over the interval from −1 to 1: the three pieces of the \
              chord before one return, in the order 1, 2, 3, and below them the row after. A \
              copy of each piece slides from the upper row to its place in the lower one, moved \
              by its word: pieces 1 and 2 by 2φ − 2 to the right, piece 3 by 2φ − 4 to the \
              left. After the return the pieces read 3, 1, 2." }
  checks := .fail
  poster := 4
  width := figureWidth
  narrowWidth := some narrowWidth

/-- A row displays one coordinate with its two good levels and the values reached from zero. -/
def coordinateRow (j : Nat) : Array Item := Id.run do
  let (some lo, some hi) := Confinement.nearestWalls j | return #[]
  let y : Rat := -2 * (j : Rat)
  let p := fun (k : Int) => ((k : Rat), y)
  let values := ((Confinement.compLabels.map (·[j]!)).eraseDups).mergeSort
  let rowName := s!"the good-level interval of coordinate {j}"
  return #[Plane.Exact.segment (p lo) (p hi) |>.faint |>.named rowName,
    Plane.Exact.label s!"n{Confinement.sub j}" ((-9 : Rat), y) .left,
    Plane.Exact.point (p lo) |>.role goodRole |>.marker .ring |>.named s!"lower good level {lo}",
    Plane.Exact.point (p hi) |>.role goodRole |>.marker .ring |>.named s!"upper good level {hi}",
    Plane.Exact.label (Confinement.intText lo) (p lo) .above |>.role goodRole,
    Plane.Exact.label (toString hi) (p hi) .above |>.role goodRole] ++
    values.toArray.map fun k => Plane.Exact.point (p k) |>.role leftRole |>.size 3
      |>.named s!"reachable value {k} of coordinate {j}" |>.incident .on rowName

/-- Five coordinate ranges of the same component at r = 1.95 and x = 1/2. -/
@[figure]
def coordinateBox : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 18
  style := partTwoStyle
  checks := .fail
  items := (Array.range 5).flatMap coordinateRow
  info := { title := "Five pairs of barriers enclose the reachable labels" }

/-- Both halves of the radius classification shown with equal weight. -/
@[figure]
def radiusThreshold : Plane.Figure :=
  { radiusLineInfinite with
    items := radiusLineItems true true
    info := { title := "Finite below R and infinite from R onward" } }

end TDCSGFigures
