/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.PartTwo
import TDCSGFigures.Style

/-!
# The figures of chapter 4, the lift to integer labels

* `unitSteps`: the window `|w - x| ≤ r/2` at `x = 1/2`, `r = 1.95`, the five unit steps from the
  current left centre `0` to the projections `ζʲ = P(eⱼ)` of the labels `eⱼ`, and which of them end
  in the window (`1`, `ζ`, `ζ⁴`), decided exactly in `ℚ(√5)` (`unitSteps_spec`).
* `changeOfFrame`: a stepper through the letters `a, b, a, b` applied to the point `0` at
  `r = 1.95`. Each step shows, side by side, the two disks in the halved starting frame
  `w ↦ (w + 1)/2` (centres `0` and `1`, radius `r/2`, the point `(y + 1)/2` moving) and the moving
  frame of the chapter's proof (the window about `x = 1/2` fixed, the left and right centres
  `P(n)` and `P(n + eⱼ)` moving by unit steps). The framing equation `2 (x - P(n)) = ζʲ (y + 1)`
  of `TDCSG.Five.Framed` holds exactly at every step (`changeOfFrame_spec`).
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

/-! ### The change of frame -/

/-- The letters applied to `z = 0`, in order. -/
def word : List Char := ['a', 'b', 'a', 'b']

/-- The left disk `|w + 1| ≤ r` holds `y`: `|y + 1|² ≤ r²`, exactly. -/
def inLeft (y : Zeta5) : Bool := QSqrt.le (y + Zeta5.ofInt 1).normSq radiusSq

/-- The right disk `|w - 1| ≤ r` holds `y`. -/
def inRight (y : Zeta5) : Bool := QSqrt.le (y - Zeta5.ofInt 1).normSq radiusSq

/-- One state of the orbit: the point `y`, its framing label `n` and direction `j`, and whether the
letter that led to it acted. -/
structure State where
  /-- The point. -/
  y : Zeta5
  /-- The framing label, of weight zero: the current left centre. -/
  n : Label
  /-- The direction index: the current right centre is `n + eⱼ`. -/
  j : Nat
  /-- Whether the letter that led here acted (`true` at the start). -/
  acted : Bool := true

/-- The letter `c` applied to a state, as `TDCSG.Five.Framed.genA` and `genB` update the frame:
`a` turns `y` clockwise by `2π/5` about `-1` when `y` is in the left disk and raises `j`; `b` turns
it about `1` when it is in the right disk, raises `j` and moves the left centre to
`n + eⱼ - eⱼ₊₁`. -/
def State.apply (s : State) (c : Char) : State :=
  if c == 'a' then
    if inLeft s.y then
      { y := (s.y + Zeta5.ofInt 1) * zeta 4 - Zeta5.ofInt 1, n := s.n, j := (s.j + 1) % 5 }
    else { s with acted := false }
  else
    if inRight s.y then
      { y := (s.y - Zeta5.ofInt 1) * zeta 4 + Zeta5.ofInt 1,
        n := shift (shift s.n s.j 1) ((s.j + 1) % 5) (-1), j := (s.j + 1) % 5 }
    else { s with acted := false }

/-- The states after `0, 1, …, 4` letters, starting from `y = 0`, `n = 0`, `j = 0`
(`TDCSG.Five.framed_self`). -/
def states : List State :=
  word.foldl (fun acc c => acc ++ [(acc.getLast?.getD ⟨origin, zeroLabel, 0, true⟩).apply c])
    [⟨origin, zeroLabel, 0, true⟩]

/-- The framing equation `2 (x - P(n)) = ζʲ (y + 1)` at `x = 1/2`, that is
`1 - 2 P(n) = ζʲ (y + 1)`, checked exactly in `ℤ[ζ₅]`. -/
def State.framed (s : State) : Bool :=
  Zeta5.ofInt 1 - Zeta5.ofInt 2 * proj s.n == zeta s.j * (s.y + Zeta5.ofInt 1)

/-- The rational shift of the moving frame's picture to the right of the halved frame's. -/
def shiftX : Rat := 3

/-- The halved image `(y + 1)/2` of a point. -/
def halved (y : Zeta5) : ZetaFrac := ⟨y + Zeta5.ofInt 1, 2⟩

/-- A point of the moving frame, drawn shifted by `shiftX`. -/
def moved (p : Zeta5) : ZetaFrac := (ZetaFrac.ofZeta p).shiftRe shiftX

/-- The window centre of the moving frame, drawn shifted. -/
def movedX : Rat × Rat := (centreX + shiftX, 0)

/-- Where a squared distance `d2` stands relative to the squared radius `r2`. -/
def sideOfSq (d2 r2 : QSqrt5) : Side :=
  if d2 == r2 then .on else if QSqrt.lt d2 r2 then .inside else .outside

/-- `|P(n) - x|²` in the halved scale (so compared with `(r/2)²`). -/
def windowDistSq (p : Zeta5) : QSqrt5 :=
  (ZetaFrac.ofZeta p - ⟨Zeta5.ofInt 1, 2⟩).normSq

/-- `(r/2)²`. -/
def halfRadiusSq : QSqrt5 := rat (halfRadius * halfRadius)

/-- The integer vector of a label, as text. -/
def labelText (n : Label) : String :=
  "(" ++ ", ".intercalate (n.toList.map fun k => if k < 0 then s!"−{-k}" else toString k) ++ ")"

/-- The letter that led to step `k` and whether it acted, as text. -/
def stepCaption (k : Nat) (s : State) : String :=
  if k == 0 then "the start: y = z = 0, n = 0, j = 0"
  else
    let c := (word.getD (k - 1) 'a')
    let centre := if c == 'a' then "−1" else "+1"
    if s.acted then s!"{c} turns y about {centre}: n = {labelText s.n}, j = {s.j}"
    else s!"{c} does not act"

/-- The halved disks: the closed disk of radius `r/2` about `0` (the left disk, halved) and about
`1` (the right disk, halved), outlined. -/
def halvedDisks : Array Item := #[
  Plane.Exact.disk origin halfRadius |>.noFill |>.role leftRole |>.named "the left disk, halved"
    |>.describedBy "the closed disk |w + 1| ≤ r about −1, drawn as |w′| ≤ r/2 about 0",
  Plane.Exact.disk rightCentre halfRadius |>.noFill |>.role rightRole
    |>.named "the right disk, halved"
    |>.describedBy "the closed disk |w − 1| ≤ r about 1, drawn as |w′ − 1| ≤ r/2 about 1",
  Plane.Exact.point origin |>.role leftRole |>.named "the left center −1, halved to 0"
    |>.incident .inside "the left disk, halved" |>.incident .outside "the right disk, halved",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the right center 1, halved to 1"
    |>.incident .outside "the left disk, halved" |>.incident .inside "the right disk, halved",
  Plane.Exact.label "0" origin .left |>.role leftRole,
  Plane.Exact.label "1" rightCentre .right |>.role rightRole,
  Plane.Exact.label "the two disks, halved" ((1 / 2 : Rat), (27 / 20 : Rat)),
  Plane.Exact.label "the moving frame" ((centreX + shiftX : Rat), (27 / 20 : Rat)),
  Plane.Exact.label "grey: earlier points" ((1 / 2 : Rat), (-6 / 5 : Rat)) |>.faint,
  Plane.Exact.label "grey: earlier centers" ((centreX + shiftX : Rat), (-6 / 5 : Rat)) |>.faint]

/-- A point of the halved frame with where it stands relative to both halved disks, decided
exactly. -/
def halvedPoint (y : Zeta5) (it : Item) : Item :=
  let p := halved y
  let l := sideOfSq (p - ZetaFrac.ofZeta origin).normSq halfRadiusSq
  let r := sideOfSq (p - ZetaFrac.ofZeta rightCentre).normSq halfRadiusSq
  it |>.incident l.incidence "the left disk, halved"
    |>.incident r.incidence "the right disk, halved"

/-- A centre of the moving frame with where it stands relative to the window, decided exactly. -/
def movedCentre (p : Zeta5) (it : Item) : Item :=
  it |>.incident (sideOfSq (windowDistSq p) halfRadiusSq).incidence "the window"

/-- The frame after `k` letters: the two halved disks with the current point `(y + 1)/2` and the
earlier ones, and the moving frame with the fixed window, the current left and right centres
`P(n)` and `P(n + eⱼ)`, the edge between them when both are in the window, and the earlier
centres. -/
def frame (k : Nat) : Plane.Figure :=
  let ss := states.take (k + 1)
  let s := ss.getLast?.getD ⟨origin, zeroLabel, 0, true⟩
  let earlier := ss.dropLast
  let right := shift s.n s.j 1
  let pl := proj s.n
  let pr := proj right
  let bothIn := inWindow radiusSq centreX s.n && inWindow radiusSq centreX right
  let trail : Array Item := (earlier.toArray.mapIdx fun i e =>
    halvedPoint e.y (Plane.Exact.point (halved e.y) |>.faint |>.size 3
      |>.named s!"the point after {i} letters"))
  let pastCentres : Array Item := (earlier.toArray.flatMap fun e =>
    #[proj e.n, proj (shift e.n e.j 1)]).foldl (fun acc p =>
      if p == pl || p == pr || acc.any (·.1 == p) then acc else acc.push (p, ())) #[]
    |>.mapIdx fun i (p, _) =>
      movedCentre p (Plane.Exact.point (moved p) |>.faint |>.size 3
        |>.named s!"an earlier center ({i + 1})")
  { width := figureWidth
    padding := 16
    style := partTwoStyle
    checks := .fail
    items := halvedDisks ++ trail ++ #[
      halvedPoint s.y (Plane.Exact.point (halved s.y) |>.size 5
        |>.named s!"the current point (y + 1)/2 after {k} letters"),
      Plane.Exact.label "(y + 1)/2" (halved s.y) .auto,
      Plane.Exact.disk movedX halfRadius |>.role windowRole |>.fillOpacity 0.07
        |>.named "the window" |>.describedBy "the closed disk |w − x| ≤ r/2 about x = 1/2"
        |>.declRef `TDCSG.Five.InWindow] ++
      (if bothIn then #[Plane.Exact.segment (moved pl) (moved pr) |>.width 2.5
        |>.named s!"the edge from {labelText s.n} to {labelText right} of the center graph"
        |>.declRef `TDCSG.Five.centerGraph] else #[]) ++ pastCentres ++ #[
      let it := Plane.Exact.point movedX |>.role windowRole |>.marker .cross
        |>.named "the window center x = 1/2, fixed" |>.incident .inside "the window"
      -- At the start the edge from `0` to `e₀` runs along the real axis through `x = 1/2`.
      if bothIn && pl == origin && pr == rightCentre then it.incident .on
        s!"the edge from {labelText s.n} to {labelText right} of the center graph" else it,
      Plane.Exact.label "x = 1/2" movedX .auto |>.role windowRole,
      movedCentre pl (Plane.Exact.point (moved pl) |>.role leftRole |>.size 5
        |>.named s!"the left center P(n), n = {labelText s.n}, weight 0"
        |>.declRef `TDCSG.Five.Label.proj),
      movedCentre pr (Plane.Exact.point (moved pr) |>.role rightRole |>.size 5
        |>.named s!"the right center P(n + e{s.j}), n + e{s.j} = {labelText right}, weight 1"),
      Plane.Exact.label "P(n)" (moved pl) .auto |>.role leftRole,
      Plane.Exact.label s!"P(n + e{["₀", "₁", "₂", "₃", "₄"].getD s.j ""})" (moved pr) .auto
        |>.role rightRole]
    info := { title := stepCaption k s } }

/-- The steps of `changeOfFrame`, with their captions. -/
def frames : Array (String × Plane.Figure) :=
  (List.range (word.length + 1)).toArray.map fun k =>
    (stepCaption k (states.getD k ⟨origin, zeroLabel, 0, true⟩), frame k)

/-- The letters `a, b, a, b` applied to `0` at `r = 1.95`, step by step: on the left the two disks
in the halved starting frame with the moving point `(y + 1)/2`; on the right the moving frame, with
the window about `x = 1/2` fixed and the left and right centres `P(n)`, `P(n + eⱼ)` moving by unit
steps. -/
@[figure]
def changeOfFrame : Explorer := Plane.stepper frames

end TDCSGFigures.Lift

namespace TDCSGFigures.Lift

open PILean PILean.Plane PILean.Exact TDCSGFigures

end TDCSGFigures.Lift
