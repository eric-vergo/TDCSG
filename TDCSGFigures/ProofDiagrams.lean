/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI Codex
-/
import TDCSGFigures.Chord
import TDCSGFigures.Confinement
import TDCSGFigures.Parts

/-! # The interval exchange, coordinate barriers, and the threshold -/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- Endpoints before and after the word, in chord coordinates. -/
def returnInterval (i : Nat) (after : Bool) : QSqrt5 × QSqrt5 :=
  let shift := if !after then rat 0 else phi * rat 2 - rat (if i == 3 then 4 else 2)
  (pieceEnds[i - 1]! + shift, pieceEnds[i]! + shift)

/-- One piece of an interval row with its word number. -/
def intervalBand (i : Nat) (after : Bool) : Array Item :=
  let (a, b) := returnInterval i after
  let y := rat (if after then (0 : Rat) else 1 / 2)
  #[Plane.Exact.segment (a, y) (b, y) |>.width 5 |>.role (pieceRole i)
      |>.named s!"piece {i}, {if after then "after" else "before"} the word",
    Plane.Exact.label (toString i) ((a + b) * rat (1 / 2), y) .above |>.role (pieceRole i)]

/-- The three pieces on a common scale before and after their words. -/
@[figure]
def exchangedIntervals : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 18
  style := houseStyle
  checks := .fail
  items := ([false, true].toArray.flatMap fun after =>
    #[1, 2, 3].flatMap fun i => intervalBand i after) ++ #[
    Plane.Exact.label "before" ((-5 / 4 : Rat), (1 / 2 : Rat)) .left,
    Plane.Exact.label "after" ((-5 / 4 : Rat), (0 : Rat)) .left,
    Plane.Exact.label "−1" ((-1 : Rat), (0 : Rat)) .below,
    Plane.Exact.label "1" ((1 : Rat), (0 : Rat)) .below]
  info := { title := "The three pieces before and after one return" }

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
