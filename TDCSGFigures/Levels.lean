/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.PartTwo
import TDCSGFigures.Style
import TDCSGFigures.Data.Moves

/-!
# The figures of chapter 6, good levels

* `levelPhases`: a plot of the phase of each level `m = -13, …, 9` of coordinate `0` at `r = 1.8`,
  `x = 0.87`, reduced modulo `L = φ - 1/2` to `[-L/2, L/2]` and drawn in units of `L`, with the good
  bands `|phase| > L/2 - η`, the good levels `-10`, `-2`, `3` decided exactly
  (`TDCSGFigures.isGoodLevel`), the walls `lo = -10` and `hi = 3` the confinement proof can use
  and the gap `|m| ≤ 2` between its two search ranges.
* `levelWinding`: an illustration beside `levelPhases`, two panels on one clock: the reduced phases
  of the same levels as points of a circle of circumference `L`, a hand turning from each level to
  the next by a rational within `2⁻⁶²` of `φ - 1` of a turn, and along the levels at their exact
  phases (`stripAt`), a ring sliding exactly from each to the next (`stripArrives`).
* `terminalCrossingFinal`: the crossing at `r = 2.12`, `x = 0.472`, `n = (4, -3, 1, 1, -3)`: the
  window, the edge from `n` to the leaf `n + e₀` across the good level `n₀ = 4`, the other
  neighbours `n + eₖ` of `n` in the window, the candidates `n + e₀ - eₖ` outside it, and the
  half-plane `Re w ≥ Re x + κ - η` beyond the cut, which holds the leaf.
* `terminalCrossing`: an animation of two panels on one clock, the crossing above and the
  neighbourhood of the leaf enlarged below. A circle walks from `n` along the thick edge to a point
  of it just inside the enlarged box, then on to the leaf, across the cut in the enlarged panel;
  the leaf's candidates appear outside the window; the circle walks back to `n` and goes. Its last
  keys are `terminalCrossingFinal` and `terminalZoom` (with ids, `zoomIds`); every slide of the
  circle is checked exactly (`crossArrives`, `zoomArrives`).
* `terminalZoom`: the same near the leaf, enlarged with a scale bar of length `0.005`: the leaf
  lies `0.0046` beyond the cut and `0.0041` inside the window's edge, both below a pixel in
  `terminalCrossingFinal`.
-/

namespace TDCSGFigures.Levels

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-! ### The phases of the levels -/

/-- `r² = 1.8² = 81/25`. -/
def plotRadiusSq : QSqrt5 := rat (81 / 25)

/-- The window centre `x = 0.87`. -/
def plotX : Rat := 87 / 100

/-- The levels drawn: `-13, …, 9`. -/
def levels : List Int := (List.range 23).map fun (i : Nat) => (i : Int) - 13

/-- `1/L = 2/√5 = (2/5) √5`. -/
def invPeriod : QSqrt5 := ⟨0, 2 / 5⟩

/-- The phase of level `m` in units of `L`, reduced to `[-1/2, 1/2)`: `t - ⌊t + 1/2⌋` for
`t = phase / L`, exact in `ℚ(√5)`; `none` if the floor is not decided. -/
def reducedPhase (m : Int) : Option QSqrt5 := do
  let t := phase plotX 0 m * invPeriod
  let k ← floorQ (t + rat (1 / 2))
  return t - rat k

/-- The rational within `2⁻⁶⁴` of the reduced phase at which its marker is drawn (`0` if it is
not decided; `levelPhases_spec` states it is decided for every level drawn). -/
def phaseAt (m : Int) : Rat := ((reducedPhase m).map fun q => (QSqrt.ball q 64).centre).getD 0

/-- `η / L` at `r = 1.8`, the width of each good band in units of `L`. -/
def bandWidth : QSqrt5 := margin plotRadiusSq * invPeriod

/-- Whether level `m` is good, decided exactly (`TDCSG.Five.IsGoodLevel`). -/
def good (m : Int) : Bool := isGoodLevel plotRadiusSq plotX 0 m == some true

/-- The walls the confinement proof can use here: the good levels `lo ≤ -3` and `hi ≥ 3` nearest
the gap `|m| ≤ 2`. -/
def walls : List Int := [-10, 3]

/-- The levels that are not good. -/
def notGood : List Int := levels.filter fun m => !good m

/-- The good levels in the gap `|m| ≤ 2` between the two search ranges. -/
def goodInGap : List Int := levels.filter fun m => good m && m.natAbs ≤ 2

/-- A level with its reduced phase, as an exact sample. -/
def sample (m : Int) : Rat × Rat := (m, phaseAt m)

/-- The top of the lower good band and the bottom of the upper one, as drawn. -/
def bandEdge : Float := RealValue.toFloat (rat (1 / 2) - bandWidth)

/-- The colour of the levels that are not good: a mid grey that reads on the light and on the dark
page and is none of the style's colours (a plot's dark twin restyles only those). -/
def notGoodGrey : Rgba := ⟨128, 128, 136, 255⟩

/-- The colour of the good levels: a bluish green beside the good role of the plane figures
(`goodRole`), readable on the light and on the dark page, and none of the style's colours. -/
def goodGreen : Rgba := ⟨0, 150, 110, 255⟩

/-- The phase of each level m = −13, …, 9 of coordinate 0 at r = 1.8, x = 0.87, reduced modulo
L, with the good bands, the good levels −10, −2, 3, the walls lo = −10 and hi = 3 and the gap
|m| ≤ 2 between the ranges where the proof looks for them. -/
@[figure]
def levelPhases : Plot.Figure where
  width := figureWidth
  height := 400
  title := "Phases of the levels of coordinate 0 at r = 1.8, x = 0.87"
  checks := .fail
  panels := #[{
    x := { label := "level m of the coordinate n₀", domain := some (-13.5, 9.5) }
    y := { label := "phase of m modulo L, in units of L", domain := some (-0.5, 0.5) }
    series := #[
      .scatterOfSamples "not good" (notGood.map sample) (some notGoodGrey) (radius := some 3),
      .scatterOfSamples "good" ((levels.filter good).map sample) (some goodGreen)
        (radius := some 6)]
    notes := #[
      .hband bandEdge 0.5 "good",
      .hband (-0.5) (-bandEdge) "good",
      .vband (-2.5) 2.5,
      .text ⟨-1.1, -0.2⟩ "|m| ≤ 2",
      .hline 0.5 "L/2",
      .hline (-0.5) "−L/2",
      .vline (-10),
      .vline 3,
      .text ⟨-9.8, 0.02⟩ "lo = −10",
      .text ⟨3.2, 0.02⟩ "hi = 3",
      .text ⟨-13.2, -0.2⟩ "lo is sought in m ≤ −3",
      .text ⟨3.4, -0.3⟩ "hi is sought in m ≥ 3"] }]

/-! ### The terminal crossing -/

/-- `r = 2.12 = 53/25`; `r/2 = 53/50`. -/
def crossRadius : Rat := 53 / 25

/-- `r²`. -/
def crossRadiusSq : QSqrt5 := rat (crossRadius * crossRadius)

/-- The window centre `x = 0.472 = 59/125`. -/
def crossX : Rat := 59 / 125

/-- The window centre as a point. -/
def crossXPoint : Rat × Rat := (crossX, 0)

/-- The label `n = (4, -3, 1, 1, -3)`, of weight zero, at the good level `n₀ = 4`. -/
def crossN : Label := #[4, -3, 1, 1, -3]

/-- The leaf `n + e₀`. -/
def leaf : Label := shift crossN 0 1

/-- The cut `Re x + κ - η` in the real direction `j = 0`. -/
def crossCut : QSqrt5 := rat crossX + kappa - margin crossRadiusSq

/-- A point of the window's circle: `x + (r/2) (-3/5, -4/5)`. -/
def crossRim : Rat × Rat := (crossX - 53 / 50 * (3 / 5), -(53 / 50 * (4 / 5)))

/-- The integer vector of a label, as text. -/
def labelText (n : Label) : String :=
  "(" ++ ", ".intercalate (n.toList.map fun k => if k < 0 then s!"−{-k}" else toString k) ++ ")"

/-- The subscript digit `k`. -/
def sub (k : Nat) : String := #["₀", "₁", "₂", "₃", "₄"].getD k ""

/-- The world box of `terminalCrossingFinal`. -/
def crossView : Box := ⟨-0.66, -1.35, 2.7, 1.35⟩

/-- The half-plane `Re w ≥ Re x + κ - η` as far as `crossView` shows it. -/
def crossHalfPlane : List (QSqrt5 × QSqrt5) :=
  [(crossCut, rat (-27 / 20)), (rat (27 / 10), rat (-27 / 20)), (rat (27 / 10), rat (27 / 20)),
    (crossCut, rat (27 / 20))]

/-- Where `P(m)` stands relative to the window, decided exactly. -/
def windowSide (m : Label) : Side :=
  if inWindow crossRadiusSq crossX m then
    -- on the circle exactly when `|P(m) - x|² = r²/4`
    let q := (crossX.den : Int)
    let w := Zeta5.ofInt q * proj m - Zeta5.ofInt crossX.num
    if w.normSq == crossRadiusSq * rat (((q * q : Int) : Rat) / 4) then .on else .inside
  else .outside

/-- The square around the leaf that `terminalZoom` enlarges. -/
def zoomBox : List (QSqrt5 × QSqrt5) :=
  let a := proj leaf |>.realPart
  let d := rat (1 / 20)
  [(a - d, rat 0 - d), (a + d, rat 0 - d), (a + d, d), (a - d, d)]

/-- The edge from `n` to its neighbour `n + eₖ`. -/
def neighbourEdge (k : Nat) : Item :=
  Plane.Exact.segment (proj crossN) (proj (shift crossN k 1)) |>.role rightRole |>.width 1.5
    |>.named s!"the edge from n to n + e{sub k}" |>.withId s!"nedge-{k}"

/-- The rejected step from the leaf `n + e₀` to its candidate `n + e₀ - eₖ`. -/
def rejectedStep (k : Nat) : Item :=
  Plane.Exact.segment (proj leaf) (proj (shift leaf k (-1))) |>.faint |>.width 1.5 |>.dashed
    |>.named s!"the rejected step from n + e₀ to n + e₀ − e{sub k}" |>.withId s!"reject-{k}"

/-- The neighbour `n + eₖ` of `n`, a square (weight one), recording where it stands relative to
the window. -/
def neighbourPoint (k : Nat) : Item :=
  Plane.Exact.point (proj (shift crossN k 1)) |>.role rightRole |>.marker .square
    |>.named s!"n + e{sub k} = {labelText (shift crossN k 1)}, weight 1, a neighbour of n"
    |>.incident (windowSide (shift crossN k 1)).incidence "the window" |>.withId s!"neighbour-{k}"

/-- Where the label of the neighbour `n + eₖ` stands: left of `n + e₁` and `n + e₄`, right of
`n + e₂`, above `n + e₃`, clear of the edges at each. -/
def neighbourPlace (k : Nat) : Placement × Float :=
  #[(.left, 10), (.right, 17), (.above, 15), (.left, 10)].getD (k - 1) (.above, 10)

/-- The label of the neighbour `n + eₖ`. -/
def neighbourLabel (k : Nat) : Item :=
  Plane.Exact.label s!"n + e{sub k}" (proj (shift crossN k 1)) (neighbourPlace k).1
    (some (neighbourPlace k).2) |>.role rightRole |>.withId s!"neighbour-label-{k}"

/-- The candidate `n + e₀ - eₖ` of the leaf, recording where it stands relative to the window. -/
def candidatePoint (k : Nat) : Item :=
  Plane.Exact.point (proj (shift leaf k (-1))) |>.faint |>.marker .ring
    |>.named s!"n + e₀ − e{sub k} = {labelText (shift leaf k (-1))}, weight 0, outside the window"
    |>.incident (windowSide (shift leaf k (-1))).incidence "the window" |>.withId s!"candidate-{k}"

/-- The label of the candidate `n + e₀ - eₖ`, placed `place`. -/
def candidateLabel (k : Nat) (place : Placement) : Item :=
  Plane.Exact.label s!"n + e₀ − e{sub k}" (proj (shift leaf k (-1))) place
    |>.withId s!"candidate-label-{k}"

/-- The figure of the crossing, the last key of `terminalCrossing`: the window, the half-plane
beyond the cut, the edge from `n` to the leaf `n + e₀` across the good level `n₀ = 4`, the four
other neighbours `n + eₖ` of `n` (inside the window) with their edges, and the four candidates
`n + e₀ - eₖ` of the leaf (outside it). Each item has an id, which the animation reads. -/
def terminalCrossingFinal : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  view := some crossView
  padding := 1
  style := partTwoStyle
  checks := .fail
  items := #[
    Plane.Exact.polygon crossHalfPlane |>.faint |>.filled |>.noOutline |>.fillOpacity 0.16
      |>.named "the half-plane Re w ≥ Re x + κ − η"
      |>.describedBy "beyond the cut of the lens estimate, turned to the direction j = 0"
      |>.declRef `TDCSG.Five.div_two_lt_norm_sub_of_le_re |>.withId "half-plane",
    Plane.Exact.disk crossXPoint (53 / 50 : Rat) |>.role windowRole |>.fillOpacity 0.07
      |>.named "the window" |>.describedBy "the closed disk |w − x| ≤ r/2, r = 2.12, x = 0.472"
      |>.declRef `TDCSG.Five.InWindow |>.withId "window",
    Plane.Exact.segment crossXPoint crossRim |>.role windowRole |>.width 1.5 |>.dashed
      |>.named "a radius r/2 = 1.06 of the window" |>.withId "radius",
    Plane.Exact.labelBeside "r/2" crossXPoint crossRim |>.role windowRole |>.withId "radius-label",
    neighbourEdge 1, neighbourEdge 2, neighbourEdge 3, neighbourEdge 4,
    rejectedStep 1, rejectedStep 2, rejectedStep 3, rejectedStep 4,
    Plane.Exact.segment (proj crossN) (proj leaf) |>.width 3.5
      |>.named "the edge from n to n + e₀: it raises n₀ from the good level 4 to 5"
      |>.declRef `TDCSG.Five.IsGoodLevel.leaf |>.withId "edge",
    Plane.Exact.polygon zoomBox |>.width 1 |>.named "the square enlarged in the next figure"
      |>.withId "zoom-box",
    neighbourPoint 1, neighbourLabel 1, neighbourPoint 2, neighbourLabel 2,
    neighbourPoint 3, neighbourLabel 3, neighbourPoint 4, neighbourLabel 4,
    candidatePoint 1, candidateLabel 1 .belowLeft, candidatePoint 2, candidateLabel 2 .below,
    candidatePoint 3, candidateLabel 3 .above, candidatePoint 4, candidateLabel 4 .aboveLeft,
    Plane.Exact.point (proj crossN) |>.role leftRole |>.size 5
      |>.named s!"n = {labelText crossN}, weight 0, P(n) = 7 − 4φ, at the good level n₀ = 4"
      |>.incident (windowSide crossN).incidence "the window" |>.withId "n",
    Plane.Exact.point (proj leaf) |>.role rightRole |>.marker .square |>.size 5
      |>.named s!"the leaf n + e₀ = {labelText leaf}, weight 1, P = 8 − 4φ"
      |>.incident (windowSide leaf).incidence "the window"
      |>.incident .inside "the half-plane Re w ≥ Re x + κ − η" |>.withId "leaf",
    Plane.Exact.label "n" (proj crossN) (.toward (Plane.deg 100)) (some 10) |>.role leftRole
      |>.italic |>.withId "name-n",
    Plane.Exact.label "n₀ = 4 → 5" ((rat (21 / 20), rat (2 / 25)) : QSqrt5 × QSqrt5)
      |>.withId "level-label",
    Plane.Exact.label "window" ((rat 0, rat (6 / 5)) : QSqrt5 × QSqrt5)
      |>.role windowRole |>.withId "window-label",
    Plane.Exact.label "Re w ≥ Re x + κ − η" ((crossCut, rat (5 / 4)) : QSqrt5 × QSqrt5) .right
      |>.size 12 |>.withId "cut-label"]
  info := { title := "A crossing at the good level n₀ = 4 ends in the leaf n + e₀" }

/-! ### The enlargement near the leaf -/

/-- The world box of `terminalZoom`: `[1.51, 1.542] × [-0.0065, 0.0065]`. -/
def zoomView : Box := ⟨1.51, -0.0065, 1.542, 0.0065⟩

/-- The leaf `P(n + e₀) = 8 - 4φ` as a point of `ℚ(√5)²`. -/
def leafQ : QSqrt5 × QSqrt5 := ((proj leaf).realPart, rat 0)

/-- The left end of the edge as the enlargement shows it. -/
def edgeStart : QSqrt5 × QSqrt5 := (rat (1511 / 1000), rat 0)

/-- The half angle, in radians, of the arc of the window's circle the enlargement draws: the
circle stays in the box for `|θ| ≤ 0.0055` (`sin θ · r/2 ≤ 0.0058`). -/
def arcHalfAngle : Float := 0.0059

/-- The neighbourhood of the leaf enlarged: the edge from `n` ending at the leaf `n + e₀`, the cut
`Re w = Re x + κ − η` (`0.0046` to its left), the window's circle (`0.0041` to its right) and a
scale bar of length `0.005`. -/
@[figure]
def terminalZoom : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  view := some zoomView
  padding := 1
  style := partTwoStyle
  checks := .fail
  items := #[
    Plane.Exact.polygon [(crossCut, rat (-13 / 2000)), (rat (1542 / 1000), rat (-13 / 2000)),
        (rat (1542 / 1000), rat (13 / 2000)), (crossCut, rat (13 / 2000))]
      |>.faint |>.filled |>.noOutline |>.fillOpacity 0.16
      |>.named "the half-plane Re w ≥ Re x + κ − η",
    Plane.Exact.arc crossXPoint (53 / 50 : Rat) (-arcHalfAngle) arcHalfAngle |>.role windowRole
      |>.named "the window's circle |w − x| = r/2",
    Plane.Exact.segment edgeStart leafQ |>.width 3.5 |>.named "the edge from n to n + e₀",
    Plane.Exact.segment ((rat (1516 / 1000), rat (-5 / 1000)) : QSqrt5 × QSqrt5)
        (rat (1521 / 1000), rat (-5 / 1000)) |>.width 2 |>.named "a scale bar of length 0.005",
    Plane.Exact.point leafQ |>.role rightRole |>.marker .square |>.size 6
      |>.named "the leaf n + e₀, P = 8 − 4φ ≈ 1.52786",
    Plane.Exact.label "n + e₀ (leaf)" leafQ .above |>.role rightRole,
    Plane.Exact.label "0.005" ((rat (15185 / 10000), rat (-5 / 1000)) : QSqrt5 × QSqrt5) .above,
    Plane.Exact.label "edge from n" ((rat (1518 / 1000), rat 0) : QSqrt5 × QSqrt5) .below,
    Plane.Exact.label "the cut" ((crossCut, rat (11 / 2000)) : QSqrt5 × QSqrt5) .left,
    Plane.Exact.label "Re w = Re x + κ − η" ((crossCut, rat (2 / 625)) : QSqrt5 × QSqrt5) .left
      |>.size 13,
    Plane.Exact.label "window edge" ((rat (15322 / 10000), rat (-1 / 200)) :
      QSqrt5 × QSqrt5) .right |>.role windowRole]
  info := { title := "Near the leaf, enlarged: the cut, the leaf and the window's edge" }

/-! ### The crossing walked -/

/-- `p - q` for numbers of `ℚ(ζ₅)` given over denominators, exact. -/
def zetaFracSub (p q : ZetaFrac) : ZetaFrac := ZetaFrac.add p ⟨-q.num, q.den⟩

/-- `P(n)`. -/
def nZ : ZetaFrac := ZetaFrac.ofZeta (proj crossN)

/-- `P(n + e₀)`, the leaf. -/
def leafZ : ZetaFrac := ZetaFrac.ofZeta (proj leaf)

/-- The point `(1.512, 0)` of the edge from `n` to the leaf, just inside the enlarged box. -/
def boxEntry : ZetaFrac := ⟨Zeta5.ofInt 1512, 1000⟩

/-- `boxEntry` in the coordinates of the enlarged panel: its real part, on the real axis. -/
def boxEntryQ : QSqrt5 × QSqrt5 := (boxEntry.realPart, rat 0)

/-- Where the walk is at key `k` of `terminalCrossing`, in the crossing: `n`, the point
`boxEntry`, the leaf (keys `2` and `3`), `n` again; after key `4` the circle is gone. -/
def walkAt (k : Nat) : List ZetaFrac :=
  match k with
  | 0 => [nZ] | 1 => [boxEntry] | 2 | 3 => [leafZ] | 4 => [nZ] | _ => []

/-- Where the walk is at key `k` in the enlarged panel: not yet at key `0`, `boxEntryQ` at key
`1`, the leaf at keys `2` and `3`, then gone. -/
def zoomWalkAt (k : Nat) : List (QSqrt5 × QSqrt5) :=
  match k with
  | 1 => [boxEntryQ] | 2 | 3 => [leafQ] | _ => []

/-- The radius of the circle that marks the walk in the crossing. -/
def walkerRadius : Rat := 1 / 16

/-- The radius of the circle that marks the walk in the enlarged panel. -/
def zoomWalkerRadius : Rat := 1 / 1800

/-- The circle about each point of `ps` that marks where the walk is (actor `walker`), of radius
`ρ`: one circle, or none when `ps` is empty. -/
def walkerItems {α : Type} [PlanePoint α] (ρ : Rat) (ps : List α) : Array Item :=
  (ps.map fun c => Plane.Exact.circle c ρ |>.width 2 |>.role leftRole
    |>.named "a circle about the point the walk has reached" |>.withId "walker").toArray

/-- The name `n` while the circle of the walk is about `n`: left of it and a little up, between the
edge to `n + e₂` and the drawn radius, clear of the circle and of the walk along the thick edge. -/
def earlyName : Item :=
  Plane.Exact.label "n" (proj crossN) (.toward (Plane.deg 168)) (some 16) |>.role leftRole
    |>.italic |>.withId "name-n-early"

/-- Whether key `k < 5` of the crossing draws the item `id` of `terminalCrossingFinal`: the
rejected steps, the candidates and their names from key `3`; not the words `n₀ = 4 → 5`, which the
circle would pass under on its way back and which appear at the last step; everything else at
every key. -/
def crossShows (k : Nat) (id : String) : Bool :=
  if id.startsWith "reject-" || id.startsWith "candidate-" then 3 ≤ k
  else id != "level-label"

/-- The items of key `k < 5` of the crossing: those of `terminalCrossingFinal` it shows
(`crossShows`), the name `n` as `earlyName`, and the circle about `walkAt k`. -/
def crossKeyItems (k : Nat) : Array Item :=
  (terminalCrossingFinal.items.filter fun it => crossShows k (it.actorId?.getD "")).map (fun it =>
    if it.actorId? == some "name-n" then earlyName else it) ++
  walkerItems walkerRadius (walkAt k)

/-- The ids of the items of `terminalZoom`, in its drawing order. -/
def zoomIds : Array String :=
  #["half-plane", "window-arc", "edge", "scale", "leaf", "leaf-label", "scale-label",
    "edge-label", "cut-name", "cut-label", "window-edge-label"]

/-- `terminalZoom` with each item given its id from `zoomIds`, the last key of the enlarged
panel. -/
def zoomFinal : Plane.Figure :=
  { terminalZoom with
    items := terminalZoom.items.mapIdx fun i it => it.withId (zoomIds.getD i "") }

/-- The name of the leaf in the enlarged panel while the circle of the walk may be about it: below
it and smaller, clear of the circle and of the window's edge. -/
def zoomEarlyName : Item :=
  Plane.Exact.label "n + e₀ (leaf)" leafQ .below (some 14) |>.size 12 |>.role rightRole
    |>.withId "leaf-label-early"

/-- The items of key `k < 5` of the enlarged panel: those of `zoomFinal`, the leaf's name as
`zoomEarlyName`, and the circle about `zoomWalkAt k`. -/
def zoomKeyItems (k : Nat) : Array Item :=
  zoomFinal.items.map (fun it =>
    if it.actorId? == some "leaf-label" then zoomEarlyName else it) ++
  walkerItems zoomWalkerRadius (zoomWalkAt k)

/-- Key `k` of the crossing: `crossKeyItems k` in the frame of `terminalCrossingFinal`, which is
key `5`. -/
def crossKey (k : Nat) : Plane.Figure :=
  if k < 5 then { terminalCrossingFinal with items := crossKeyItems k } else terminalCrossingFinal

/-- Key `k` of the enlarged panel: `zoomKeyItems k` in the frame of `zoomFinal`, which is key
`5`. -/
def zoomKey (k : Nat) : Plane.Figure :=
  if k < 5 then { zoomFinal with items := zoomKeyItems k } else zoomFinal

/-- The declared moves of the steps of the crossing: the circle slides from `n` to `boxEntry`, on
to the leaf, the candidates with their spokes and names appear, the circle slides back to `n`; at
the last step it goes, the name `n` takes its place in the figure and the words `n₀ = 4 → 5`
appear. -/
def crossMoves : Nat → List (String × ExactMove ZetaFrac)
  | 0 => [("walker", .slide (zetaFracSub boxEntry nZ))]
  | 1 => [("walker", .slide (zetaFracSub leafZ boxEntry))]
  | 2 => ([1, 2, 3, 4].map (s!"reject-{·}", .appear)) ++
      ([1, 2, 3, 4].flatMap fun k => [(s!"candidate-{k}", .appear),
        (s!"candidate-label-{k}", .appear)])
  | 3 => [("walker", .slide (zetaFracSub nZ leafZ))]
  | _ => [("walker", .vanish), ("name-n-early", .vanish), ("name-n", .appear),
      ("level-label", .appear)]

/-- The declared moves of the steps of the enlarged panel: the circle appears at `boxEntryQ`,
slides to the leaf, waits, goes; at the last step the leaf's name takes its place in the figure. -/
def zoomMoves : Nat → List (String × ExactMove (QSqrt5 × QSqrt5))
  | 0 => [("walker", .appear)]
  | 1 => [("walker", .slide (leafQ.1 - boxEntryQ.1, leafQ.2 - boxEntryQ.2))]
  | 2 => []
  | 3 => [("walker", .vanish)]
  | _ => [("leaf-label-early", .vanish), ("leaf-label", .appear)]

/-- The ids of the actors of key `k` of the crossing that come and go, without anchors. -/
def crossFadeIds (k : Nat) : List String :=
  (if 3 ≤ k then [1, 2, 3, 4].flatMap fun j =>
    [s!"reject-{j}", s!"candidate-{j}", s!"candidate-label-{j}"] else []) ++
  (if k < 5 then ["name-n-early"] else ["name-n", "level-label"])

/-- The exact actors of key `k` of the crossing: the circle at `walkAt k`, drawn there
(`crossKeyItems`), and the actors that come and go. -/
def crossActors (k : Nat) : List (ExactActor ZetaFrac) :=
  (if (walkAt k).isEmpty then [] else [⟨"walker", walkAt k⟩]) ++
    (crossFadeIds k).map fun id => ⟨id, []⟩

/-- The exact actors of key `k` of the enlarged panel: the circle at `zoomWalkAt k` and the
leaf's name. -/
def zoomActors (k : Nat) : List (ExactActor (QSqrt5 × QSqrt5)) :=
  (if (zoomWalkAt k).isEmpty then [] else [⟨"walker", zoomWalkAt k⟩]) ++
    [⟨if k < 5 then "leaf-label-early" else "leaf-label", []⟩]

/-- Whether every declared move of the crossing carries the actors of one key onto those of the
next, exactly in `ℚ(ζ₅)`. -/
def crossArrives : Bool := allArrive 5 crossMoves crossActors

/-- Whether every declared move of the enlarged panel carries the actors of one key onto those of
the next, exactly in `ℚ(√5)²`. -/
def zoomArrives : Bool := allArrive 5 zoomMoves zoomActors

/-- The captions of the keys of `terminalCrossing`. -/
def crossCaptions : Array String := #[
  "A crossing at a good level, at r = 2.12, x = 0.472: the label n = (4, −3, 1, 1, −3) has weight \
    zero and its coordinate n₀ = 4 is a good level. The circle starts at n; the thick edge leads \
    to n + e₀ and raises n₀ to 5.",
  "The walk follows the thick edge to the small square, which the lower panel shows enlarged.",
  "It reaches the leaf n + e₀: enlarged, the step ends between 0.0045 and 0.0046 beyond the cut \
    Re w = Re x + κ − η and between 0.0041 and 0.0042 inside the window's edge, both less than a \
    pixel in the upper panel.",
  "By the lens estimate the four other candidates n + e₀ − eₖ of the leaf lie outside the window \
    (open rings at the ends of dashed spokes): n + e₀ has no neighbor but n.",
  "So the only step from the leaf leads back along the same edge to n, at level 4.",
  "The crossing: n with its four neighbors n + eₖ inside the window, the thick edge to the leaf \
    n + e₀ in the shaded half-plane, and the leaf's four candidates outside the window. Below, the \
    neighborhood of the leaf enlarged, with a scale bar of length 0.005."]

/-- The crossing as a motion: the keys `crossKey k`, the steps made from `crossMoves`. -/
def crossMotion : Motion where
  keys := ((List.range 6).map crossKey).toArray
  steps := ((List.range 5).map (exactStep ∘ crossMoves)).toArray

/-- The enlarged panel as a motion: the keys `zoomKey k`, the steps made from `zoomMoves`. -/
def zoomMotion : Motion where
  keys := ((List.range 6).map zoomKey).toArray
  steps := ((List.range 5).map (exactStep ∘ zoomMoves)).toArray

/-- The timing of step `k`: a slide where either panel slides, a fade otherwise. -/
def crossTiming (k : Nat) : PanelTiming :=
  if k == 2 || k == 4 then { duration := some motionPacing.fade, easing := some .linear }
  else { duration := some motionPacing.slide, easing := some motionPacing.easing }

/-- A crossing at the good level n₀ = 4 at r = 2.12, x = 0.472, walked: a circle follows the thick
edge from n to the leaf n + e₀, which the lower panel shows enlarged, just beyond the cut and
inside the window's edge; the leaf's four other candidates appear outside the window and the walk
returns to n. The last key frames are the figure of the crossing, `terminalCrossingFinal`, and
`terminalZoom`. -/
@[figure]
def terminalCrossing : MotionPanels where
  panels := #[{ title := "The crossing", motion := crossMotion },
    { title := "Near the leaf, enlarged", motion := zoomMotion }]
  captions := crossCaptions
  pacing := { motionPacing with hold := 7 / 5 }
  timing := ((List.range 5).map crossTiming).toArray
  info := { title := "A crossing at the good level n₀ = 4 ends in the leaf n + e₀"
            description := "Two panels on one clock: the crossing at r = 2.12, x = 0.472, and \
              below it the neighborhood of the leaf n + e₀ enlarged. A circle walks from n along \
              the thick edge across the good level n₀ = 4 to the leaf, which the enlargement shows \
              just beyond the cut and inside the window's edge; the leaf's four other candidates \
              appear outside the window, and the walk returns to n. The key frames are exact; \
              between them the browser slides the circle along the edge and fades what comes and \
              goes." }
  checks := .fail
  poster := 5
  scale := .independent
  arrangement := .stacked
  width := figureWidth
  narrowWidth := some narrowWidth

/-! ### The phases winding round -/

/-- The reduced phase of level `m`, exact, in units of `L` (`0` if not decided; every level drawn
is decided). -/
def phaseQ (m : Int) : QSqrt5 := (reducedPhase m).getD (rat 0)

/-- The number of levels drawn: `23`, from `-13` to `9`. -/
def levelCount : Nat := levels.length

/-- The level of key `k` of `levelWinding`: `-13 + k`. -/
def levelAt (k : Nat) : Int := levels.getD k 0

/-- Whether each reduced phase is the one before plus `φ - 1` or minus `2 - φ`: the phase grows by
`(1 + φ/2) = φ L` from one level to the next, so by `φ` in units of `L`. Exact in `ℚ(√5)`. -/
def phaseStepsArePhi : Bool :=
  (List.range (levelCount - 1)).all fun k =>
    let d := phaseQ (levelAt (k + 1)) - phaseQ (levelAt k)
    d + rat 1 == phi || d + rat 2 == phi

/-- The fraction of a full turn at which level `m`'s point is drawn on the circle: its reduced
phase rounded to a rational (`phaseAt`). -/
def circleTurns (m : Int) : Rat := phaseAt m

/-- Whether every point drawn on the circle is within `2⁻⁶²` of a turn of its exact reduced
phase, exactly in `ℚ(√5)`. -/
def circleNearPhase : Bool :=
  levels.all fun m =>
    let e := rat (circleTurns m) - phaseQ m
    let tol := rat (1 / 2 ^ 62)
    QSqrt.lt e tol && QSqrt.lt (rat 0 - tol) e

/-- The turn of step `k` of the circle, as a fraction of a full turn counterclockwise: from the
point drawn for level `levelAt k` to the one drawn for the next, `circleTurns` of the next less
`circleTurns` of this one, plus one when that is negative. -/
def turnOf (k : Nat) : Rat :=
  let d := circleTurns (levelAt (k + 1)) - circleTurns (levelAt k)
  if d < 0 then d + 1 else d

/-- Whether every declared turn is within `2⁻⁶²` of `φ - 1`, exactly in `ℚ(√5)`. -/
def turnsNearPhi : Bool :=
  (List.range (levelCount - 1)).all fun k =>
    let e := rat (turnOf k) - (phi - rat 1)
    let tol := rat (1 / 2 ^ 62)
    QSqrt.lt e tol && QSqrt.lt (rat 0 - tol) e

/-- The look of a level's point: good levels (`good`, decided exactly) in the colour of the good
phases, the others faint. -/
def levelMark (m : Int) (it : Item) : Item :=
  if good m then it.role goodRole |>.size 6 else it.faint |>.size 3.5

/-- An integer with a true minus sign. -/
def intText (m : Int) : String := if m < 0 then s!"−{-m}" else toString m

/-- The name of a good level beside its point. -/
def goodName (m : Int) : String :=
  if m == -10 then "lo = −10" else if m == 3 then "hi = 3" else intText m

/-! #### On a circle -/

/-- `π`. -/
def pi : Float := Plane.deg 180

/-- The angle of the fraction `t` of a full turn on the circle, in radians: `0` at the bottom,
counterclockwise, `±1/2` at the top. -/
def angleOf (t : Float) : Float := -(pi / 2) + 2 * pi * t

/-- The angle of level `m`'s point: `angleOf (circleTurns m)`. -/
def levelAngle (m : Int) : Float := angleOf (Exact.toFloat (circleTurns m))

/-- The point of the circle at the angle `θ`, at the radius `ρ`. -/
def onCircle (θ ρ : Float) : Point := ⟨ρ * Float.cos θ, ρ * Float.sin θ⟩

/-- The half width of the good arc, in radians: `2π η/L`. -/
def goodHalfAngle : Float := 2 * pi * RealValue.toFloat bandWidth

/-- The radius of the hand, short of the circle. -/
def handLength : Float := 0.8

/-- The hand at level `m`'s angle, an arrow from the centre (actor `hand`). -/
def hand (m : Int) : Item :=
  Plane.arrow ⟨0, 0⟩ (onCircle (levelAngle m) handLength) |>.width 2 |>.role leftRole
    |>.named "the hand, at the phase of the level last reached" |>.withId "hand"

/-- The mark of the hand's sense of turning: a short counterclockwise arc ending on the hand
(actor `hand-sense`). -/
def handSense (m : Int) : Item :=
  let θ := levelAngle m
  Plane.angleMark ⟨0, 0⟩ (θ - 0.7) (θ - 0.12) (some 34) |>.role leftRole
    |>.named "the sense of the hand's turn, counterclockwise" |>.withId "hand-sense"

/-- The title of the circle. -/
def circleTitle : String := "the phases modulo L, a circle of circumference L"

/-- The title of the shaded arc of the good phases. -/
def arcTitle : String := "the good phases: farther than L/2 − η from L ℤ"

/-- The point of level `m` on the circle (actor `level-m`), recorded on it, and on the boundary of
the shaded arc when the level is good, outside it otherwise. -/
def circlePoint (m : Int) : Item :=
  levelMark m (Plane.point (onCircle (levelAngle m) 1)) |>.named s!"level {intText m}"
    |>.incident .on circleTitle |>.incident (if good m then .on else .outside) arcTitle
    |>.withId s!"level-{m}"

/-- The name of level `m` on the circle, outside it (actor `name-m`): a good level's above and to
the side of the circle its point is on, in the colour of the good phases; another's, smaller and
faint, straight out from its point. -/
def circleName (m : Int) : Item :=
  let p := onCircle (levelAngle m) 1
  if good m then
    Plane.label (goodName m) p (if p.x ≥ 0 then .aboveRight else .aboveLeft) |>.size 13
      |>.role goodRole |>.withId s!"name-{m}"
  else
    Plane.label (intText m) p (.toward (levelAngle m)) (some 6) |>.size 11 |>.faint
      |>.withId s!"name-{m}"

/-- The shaded arc of the good phases and the circle, drawn at every key. -/
def circleBase : Array Item := #[
  Plane.sector ⟨0, 0⟩ 1 (pi / 2 - goodHalfAngle) (pi / 2 + goodHalfAngle)
    |>.role goodRole |>.noOutline |>.fillOpacity 0.18 |>.named arcTitle,
  Plane.circle ⟨0, 0⟩ 1 |>.faint |>.width 1.5 |>.named circleTitle]

/-- Key `k` of the circle: the base, the points of the levels up to `levelAt k` with their names,
and the hand at `levelAt k` with its sense. -/
def circleKey (k : Nat) : Plane.Figure :=
  let ms := levels.take (k + 1)
  let m := levelAt k
  { width := figureWidth
    view := some ⟨-1.35, -1.3, 1.35, 1.35⟩
    padding := 1
    style := partTwoStyle
    checks := .fail
    items := circleBase ++ (ms.map circlePoint).toArray ++ #[hand m, handSense m] ++
      (ms.map circleName).toArray
    info := { title := "The phases of the levels on a circle of circumference L" } }

/-- The moves of step `k` of the circle: the hand and its mark turn by `turnOf k` of a full turn
about the centre, and the point of the next level appears with its name. -/
def circleMoves (k : Nat) : Array (String × Move) :=
  let m' := levelAt (k + 1)
  #[("hand", .turn ⟨0, 0⟩ (turnOf k)), ("hand-sense", .turn ⟨0, 0⟩ (turnOf k)),
    (s!"level-{m'}", .appear), (s!"name-{m'}", .appear)]

/-- The circle as a motion. -/
def circleMotion : Motion where
  keys := ((List.range levelCount).map circleKey).toArray
  steps := ((List.range (levelCount - 1)).map fun k =>
    ({ moves := circleMoves k } : MotionStep)).toArray

/-! #### Along the levels -/

/-- The height of a unit of `L` along the levels, in units of a level. -/
def unitHeight : QSqrt5 := rat 8

/-- The point of level `m` along the levels: `(m, s t)` with `t` its exact reduced phase and `s`
the height of a unit. -/
def stripAt (m : Int) : QSqrt5 × QSqrt5 := (rat m, unitHeight * phaseQ m)

/-- The left end of the strip, half a level before `-13`. -/
def stripLeft : QSqrt5 := rat (-27 / 2)

/-- The right end of the strip, half a level after `9`. -/
def stripRight : QSqrt5 := rat (19 / 2)

/-- The top of the strip, `s/2`. -/
def stripTop : QSqrt5 := unitHeight * rat (1 / 2)

/-- The bottom of the strip, `-s/2`. -/
def stripBottom : QSqrt5 := rat 0 - stripTop

/-- The edge of the upper good band, `s (1/2 - η/L)`. -/
def bandTop : QSqrt5 := unitHeight * (rat (1 / 2) - bandWidth)

/-- The rectangle from `(x₀, y₀)` to `(x₁, y₁)`. -/
def rect (x₀ y₀ x₁ y₁ : QSqrt5) : List (QSqrt5 × QSqrt5) := [(x₀, y₀), (x₁, y₀), (x₁, y₁), (x₀, y₁)]

/-- Where `y` stands relative to the band above `a`, decided exactly. -/
def above (a y : QSqrt5) : Incidence := if QSqrt.lt a y then .inside else .outside

/-- The point of level `m` along the levels (actor `level-m`), recording where it stands, decided
exactly: relative to the two good bands, inside the strip, and on the wall at `lo = -10` or
`hi = 3` when it is that level. -/
def stripPoint (m : Int) : Item :=
  let y := (stripAt m).2
  let it := levelMark m (Plane.Exact.point (stripAt m)) |>.named s!"level {intText m}"
    |>.incident (above bandTop y) "the upper good band"
    |>.incident (above y (rat 0 - bandTop)) "the lower good band"
    |>.incident (if QSqrt.lt stripBottom y && QSqrt.lt y stripTop then .inside else .outside)
      "the phases from −L/2 to L/2"
  let it := if m == -10 then it.incident .on "the wall lo = −10"
    else if m == 3 then it.incident .on "the wall hi = 3" else it
  it.withId s!"level-{m}"

/-- The radius of the ring that marks the level reached along the levels. -/
def tracerRadius : Rat := 9 / 20

/-- The ring about each point of `ps` (actor `tracer`). -/
def tracerItems (ps : List (QSqrt5 × QSqrt5)) : Array Item :=
  (ps.map fun c => Plane.Exact.circle c tracerRadius |>.width 2 |>.role leftRole
    |>.named "a ring about the level last reached" |>.withId "tracer").toArray

/-- The label at `(x, y)` along the levels. -/
def stripLabel (s : String) (x y : Rat) (place : Placement := .center) : Item :=
  Plane.Exact.label s ((rat x, rat y) : QSqrt5 × QSqrt5) place

/-- The items every key along the levels draws: the good bands, the gap `|m| ≤ 2`, the strip, the
walls `lo = -10` and `hi = 3` with their names, and the marks of the phases and of the levels. -/
def stripBase : Array Item := #[
  Plane.Exact.polygon (rect stripLeft bandTop stripRight stripTop) |>.role goodRole |>.filled
    |>.noOutline |>.fillOpacity 0.18 |>.named "the upper good band",
  Plane.Exact.polygon (rect stripLeft stripBottom stripRight (rat 0 - bandTop)) |>.role goodRole
    |>.filled |>.noOutline |>.fillOpacity 0.18 |>.named "the lower good band",
  Plane.Exact.polygon (rect (rat (-5 / 2)) stripBottom (rat (5 / 2)) stripTop) |>.faint |>.filled
    |>.noOutline |>.fillOpacity 0.12 |>.named "the gap |m| ≤ 2 between the search ranges",
  Plane.Exact.polygon (rect stripLeft stripBottom stripRight stripTop) |>.faint |>.width 1
    |>.named "the phases from −L/2 to L/2",
  Plane.Exact.segment ((rat (-10), stripBottom) : QSqrt5 × QSqrt5) (rat (-10), stripTop)
    |>.role goodRole |>.width 1.5 |>.dashed |>.named "the wall lo = −10",
  Plane.Exact.segment ((rat 3, stripBottom) : QSqrt5 × QSqrt5) (rat 3, stripTop)
    |>.role goodRole |>.width 1.5 |>.dashed |>.named "the wall hi = 3",
  stripLabel "lo = −10" (-10) (13 / 2) |>.role goodRole,
  stripLabel "hi = 3" 3 (13 / 2) |>.role goodRole,
  stripLabel "L/2" (-27 / 2) 4 .left,
  stripLabel "0" (-27 / 2) 0 .left,
  stripLabel "−L/2" (-27 / 2) (-4) .left,
  stripLabel "−13" (-13) (-9 / 2) .below,
  stripLabel "−5" (-5) (-9 / 2) .below,
  stripLabel "0" 0 (-9 / 2) .below,
  stripLabel "5" 5 (-9 / 2) .below,
  stripLabel "9" 9 (-9 / 2) .below]

/-- Where the ring is at key `k` along the levels: the point of `levelAt k`. -/
def tracerAt (k : Nat) : List (QSqrt5 × QSqrt5) := [stripAt (levelAt k)]

/-- Key `k` along the levels: the base, the points of the levels up to `levelAt k`, and the ring
about the last (`tracerAt k`). -/
def stripKey (k : Nat) : Plane.Figure :=
  let ms := levels.take (k + 1)
  { width := figureWidth
    padding := 1
    style := partTwoStyle
    checks := .fail
    items := stripBase ++ (ms.map stripPoint).toArray ++ tracerItems (tracerAt k)
    info := { title := "The phases of the levels, in units of L" } }

/-- The declared moves of step `k` along the levels: the ring slides by the exact vector from
level `levelAt k`'s point to the next one's, and the next point appears. -/
def stripMoves (k : Nat) : List (String × ExactMove (QSqrt5 × QSqrt5)) :=
  let p := stripAt (levelAt k)
  let q := stripAt (levelAt (k + 1))
  [("tracer", .slide (q.1 - p.1, q.2 - p.2)), (s!"level-{levelAt (k + 1)}", .appear)]

/-- The exact actors of key `k` along the levels: the ring at `tracerAt k` and the points of the
levels up to `levelAt k`, at `stripAt`, as drawn. -/
def stripActors (k : Nat) : List (ExactActor (QSqrt5 × QSqrt5)) :=
  [⟨"tracer", tracerAt k⟩] ++ (levels.take (k + 1)).map fun m => ⟨s!"level-{m}", [stripAt m]⟩

/-- Whether every slide of the ring lands exactly on the next level's point. -/
def stripArrives : Bool := allArrive (levelCount - 1) stripMoves stripActors

/-- The levels as a motion. -/
def stripMotion : Motion where
  keys := ((List.range levelCount).map stripKey).toArray
  steps := ((List.range (levelCount - 1)).map fun k => exactStep (stripMoves k)).toArray

/-! #### The loop -/

/-- The words for the standing of level `m`. -/
def standing (m : Int) : String :=
  if m == -10 then "good: its phase lies in the shaded part, and it is the wall lo"
  else if m == 3 then "good: its phase lies in the shaded part, and it is the wall hi"
  else if m == -2 then "good, in the gap |m| ≤ 2 between the two search ranges"
  else "not good"

/-- The caption of key `k` of `levelWinding`. -/
def windingCaption (k : Nat) : String :=
  let m := levelAt k
  if k == 0 then
    s!"The phase of each level m of coordinate 0 at r = 1.8, x = 0.87, reduced modulo \
      L = φ − 1/2, on a circle of circumference L (phase 0 at the bottom, ±L/2 at the top) and \
      along the levels in units of L. A level is good when its phase lies in the shaded part, \
      farther than L/2 − η from L ℤ; this is decided exactly. On the circle each point is drawn \
      at its phase rounded to a rational, within 2⁻⁶²; along the levels at its exact phase. \
      Level {intText m}: {standing m}."
  else if k + 1 == levelCount then
    s!"Level {intText m}: {standing m}. Of the levels −13 to 9 the good ones are −10, −2 and 3; \
      the walls are lo = −10 and hi = 3, and −2 lies in the gap between the search ranges."
  else
    s!"Level {intText m}: the phase grows by φ L, φ periods, and the hand turns by a rational \
      within 2⁻⁶² of φ − 1 of a turn; {standing m}."

/-- The phases of the levels −13 to 9 of coordinate 0 at r = 1.8, x = 0.87, reduced modulo L, on
a circle of circumference L and along the levels, arriving in order on one clock: a hand turns by
about φ − 1 of a turn from each level to the next, and the plot of `levelPhases` fills in. -/
@[figure illustration]
def levelWinding : MotionPanels where
  panels := #[{ title := "On a circle", motion := circleMotion },
    { title := "Along the levels", motion := stripMotion }]
  captions := ((List.range levelCount).map windingCaption).toArray
  pacing := { motionPacing with
    turn := 9 / 10, slide := 9 / 10, hold := 1 / 2, firstHold := 2, lastHold := 3 }
  timing := ((List.range (levelCount - 1)).map fun _ =>
    ({ duration := some (9 / 10), easing := some motionPacing.easing } : PanelTiming)).toArray
  info := { title := "The phases of the levels wind round"
            description := "The phases of the levels −13 to 9 of coordinate 0 at r = 1.8, \
              x = 0.87, reduced modulo L, on a circle of circumference L and along the levels, \
              arriving in order on one clock. On the circle a hand turns from each level's point \
              to the next one's by a rational within 2⁻⁶² of φ − 1 of a turn; the points are drawn \
              at their phases rounded to rationals. Along the levels the points are at their exact \
              phases and a ring slides exactly from each to the next. Which levels are good is \
              decided exactly; between the key frames the browser turns the hand and slides the \
              ring." }
  checks := .fail
  poster := levelCount - 1
  scale := .independent
  width := figureWidth
  narrowWidth := some narrowWidth
  shares := #[1, 1]

/-! ### The facts the figures show -/

-- The good levels among `-13, …, 9` at `r = 1.8`, `x = 0.87` are `-10`, `-2`, `3`; every
-- reduced phase is decided.
#guard levels.filter good == [-10, -2, 3] && levels.all fun m => (reducedPhase m).isSome

-- The leaf lies beyond the cut and inside the window; `P(n) = 7 - 4φ`, `P(n + e₀) = 8 - 4φ`.
#guard QSqrt.lt crossCut (proj leaf).realPart &&
  windowSide leaf == .inside && windowSide crossN == .inside &&
  (proj crossN).realPart == ⟨5, -2⟩ && (proj crossN).conj == proj crossN &&
  (proj leaf).realPart == ⟨6, -2⟩

end TDCSGFigures.Levels
