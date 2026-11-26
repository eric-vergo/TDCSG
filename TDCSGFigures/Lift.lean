/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.Frames
import TDCSGFigures.Style

/-!
# The figures of chapter 4, the lift to integer labels

* `unitSteps`: the window `|w - x| ≤ r/2` at `x = 1/2`, `r = 1.95`, the five unit steps from the
  current left centre `0` to the projections `ζʲ = P(eⱼ)` of the labels `eⱼ`, and which of them end
  in the window (`1`, `ζ`, `ζ⁴`), decided exactly in `ℚ(√5)` (`unitSteps_spec`).
* The frame pair (`TDCSGFigures.Lift.framePair`, in `TDCSGFigures.FramePairMotion`) follows the
  word `word`, `a a b a b a a b b a b b`, applied to the point `0` at `r = 1.95`, in two frames at
  once; this module holds its data: the word, the states `statesFor radiusSq word` and the pin
  `wordSummary_word` (the letters `3`, `5` and `10` do not act).
-/

namespace TDCSGFigures.Lift

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-! ### The data -/

/-- The radius `r = 39/20 = 1.95` of both figures. -/
def radius : Rat := 39 / 20

/-- `r²`, in `ℚ(√5)`. -/
def radiusSq : QSqrt5 := rat (radius * radius)

/-- The half radius `r/2 = 39/40`, the radius of the window. -/
def halfRadius : Rat := 39 / 40

/-- The window centre `x = 1/2`, the image of the starting point `z = 0`. -/
def centreX : Rat := 1 / 2

/-- The window centre as a point. -/
def centrePoint : Rat × Rat := (1 / 2, 0)

/-- A point of the window's circle: `x + (r/2) (3/5, -4/5)`, rational. -/
def rimPoint : Rat × Rat := (1 / 2 + 39 / 40 * (3 / 5), -(39 / 40 * (4 / 5)))

/-- The label `eⱼ`. -/
def basisLabel (j : Nat) : Label := shift zeroLabel j 1

/-- The labels `e₀, …, e₄` that lie in the window, decided exactly (`inWindow`). -/
def activeSteps : List Nat :=
  (List.range 5).filter fun j => inWindow radiusSq centreX (basisLabel j)

/-! ### The window and the five unit steps -/

/-- The name of `ζʲ`. -/
def zetaName (j : Nat) : String := #["1", "ζ", "ζ²", "ζ³", "ζ⁴"].getD j ""

/-- The name of the label `eⱼ`. -/
def basisName (j : Nat) : String := #["e₀", "e₁", "e₂", "e₃", "e₄"].getD j ""

/-- The window: the closed disk of radius `r/2` about `x`. -/
def window : Item :=
  Plane.Exact.disk centrePoint halfRadius |>.role windowRole |>.fillOpacity 0.07
    |>.named "the window" |>.describedBy "the closed disk |w − x| ≤ r/2, x = 1/2, r = 1.95"
    |>.declRef `TDCSG.Five.InWindow

/-- A step from `0` to `ζʲ` that ends in the window: solid, in the colour of right centres. -/
def activeStep (j : Nat) : Item :=
  Plane.Exact.segment origin (zeta j) |>.role rightRole |>.width 2.5
    |>.named s!"the step from 0 to {zetaName j} = P({basisName j}), ending in the window"
    |>.declRef `TDCSG.Five.Label.proj_basis

/-- A step from `0` to `ζʲ` that ends outside the window: dashed, faint. -/
def inactiveStep (j : Nat) : Item :=
  Plane.Exact.segment origin (zeta j) |>.faint |>.dashed
    |>.named s!"the step from 0 to {zetaName j} = P({basisName j}), ending outside the window"
    |>.declRef `TDCSG.Five.Label.proj_basis

/-- The end `ζʲ = P(eⱼ)` of a step inside the window: a filled marker. -/
def activeEnd (j : Nat) : Item :=
  Plane.Exact.point (zeta j) |>.role rightRole |>.size 5
    |>.named s!"P({basisName j}) = {zetaName j}, label {basisName j}, weight 1"
    |>.incident .inside "the window"

/-- The end `ζʲ = P(eⱼ)` of a step outside the window: an open ring. -/
def inactiveEnd (j : Nat) : Item :=
  Plane.Exact.point (zeta j) |>.faint |>.marker .ring |>.size 5
    |>.named s!"P({basisName j}) = {zetaName j}, label {basisName j}, weight 1"
    |>.incident .outside "the window"

/-- The label of the end of step `j`, naming the label `eⱼ` and its projection. -/
def endLabel (j : Nat) (active : Bool) : Item :=
  let it := Plane.Exact.label s!"{basisName j} ↦ {zetaName j}" (zeta j) .auto
  if active then it.role rightRole else it.faint

/-- The window, the radius `r/2`, the five unit steps from the left centre `0` and their ends,
`0` and the window centre `x`, all labelled. -/
@[figure]
def unitSteps : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := partTwoStyle
  checks := .fail
  items := #[
    window,
    Plane.Exact.segment centrePoint rimPoint |>.role windowRole |>.width 1.5 |>.dashed
      |>.named "a radius r/2 = 0.975 of the window",
    Plane.Exact.labelBeside "r/2 = 0.975" centrePoint rimPoint |>.role windowRole,
    activeStep 0, activeStep 1, inactiveStep 2, inactiveStep 3, activeStep 4,
    activeEnd 0, activeEnd 1, inactiveEnd 2, inactiveEnd 3, activeEnd 4,
    Plane.Exact.point origin |>.role leftRole |>.size 5
      |>.named "the current left center P(0) = 0, label 0, weight 0"
      |>.incident .inside "the window",
    Plane.Exact.point centrePoint |>.role windowRole |>.marker .cross
      |>.named "the window center x = 1/2" |>.incident .inside "the window"
      |>.incident .on "the step from 0 to 1 = P(e₀), ending in the window",
    endLabel 0 true, endLabel 1 true, endLabel 2 false, endLabel 3 false, endLabel 4 true,
    Plane.Exact.label "0" origin .auto |>.role leftRole,
    Plane.Exact.label "x = 1/2" centrePoint .auto |>.role windowRole,
    Plane.Exact.label "window |w − x| ≤ r/2" ((6 / 5 : Rat), (-11 / 10 : Rat)) |>.role windowRole]
  info := { title := "The five unit steps from the left center 0 and the window at x = 1/2" }

/-! ### The word of the frame pair -/

/-- The letters applied to `z = 0`, in order: `a a b a b a a b b a b b`. -/
def word : List Early.Letter := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b]

/-- The states after `0, 1, …, 12` letters, starting from `y = 0`, `n = 0`, `j = 0`
(`TDCSG.Five.framed_self`). -/
def states : List State := statesFor radiusSq word

/-- The framing equation `2 (x - P(n)) = ζʲ (y + 1)` at `x = 1/2`, that is
`1 - 2 P(n) = ζʲ (y + 1)`, checked exactly in `ℤ[ζ₅]` (`State.framedFrom`). -/
def State.framed (s : State) : Bool := s.framedFrom origin

/-- The word of the frame pair at `r = 1.95` from `z = 0`: the letters `3`, `5` and `10` do not
act, every step has the geometry of `State.stepHolds`, the orbit does not close, and it reaches
`|(y + 1)/2|² = |P - x|² = 3/2 + √5/4` (about `1.43²`), the squared distance of each idle letter's
centre from `x`. -/
theorem wordSummary_word :
    wordSummary radiusSq word = ⟨[3, 5, 10], true, false, ⟨3 / 2, 1 / 4⟩, ⟨3 / 2, 1 / 4⟩⟩ := by
  decide +kernel

/-- The halved image `(y + 1)/2` of a point. -/
def halved (y : Zeta5) : ZetaFrac := ⟨y + Zeta5.ofInt 1, 2⟩

/-- Where a squared distance `d2` stands relative to the squared radius `r2`. -/
def sideOfSq (d2 r2 : QSqrt5) : Side :=
  if d2 == r2 then .on else if QSqrt.lt d2 r2 then .inside else .outside

/-- `|P(n) - x|²` in the halved scale (so compared with `(r/2)²`). -/
def windowDistSq (p : Zeta5) : QSqrt5 :=
  (ZetaFrac.ofZeta p - ⟨Zeta5.ofInt 1, 2⟩).normSq

/-- `(r/2)²`. -/
def halfRadiusSq : QSqrt5 := rat (halfRadius * halfRadius)

end TDCSGFigures.Lift
