/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.PartTwo
import TDCSGFigures.Style

/-!
# The figures of chapter 6, good levels

* `levelPhases`: a plot of the phase of each level `m = -13, …, 9` of coordinate `0` at `r = 1.8`,
  `x = 0.87`, reduced modulo `L = φ - 1/2` to `[-L/2, L/2]` and drawn in units of `L`, with the good
  bands `|phase| > L/2 - η`, the good levels `-10`, `-2`, `3` decided exactly
  (`TDCSGFigures.isGoodLevel`), the walls `lo = -10` and `hi = 3` the confinement proof can use
  and the gap `|m| ≤ 2` between its two search ranges.
* `terminalCrossing`: the crossing at `r = 2.12`, `x = 0.472`, `n = (4, -3, 1, 1, -3)`: the window,
  the edge from `n` to the leaf `n + e₀` across the good level `n₀ = 4`, the other neighbours
  `n + eₖ` of `n` in the window, the candidates `n + e₀ - eₖ` outside it, and the half-plane
  `Re w ≥ Re x + κ - η` beyond the cut, which holds the leaf.
* `terminalZoom`: the same near the leaf, enlarged with a scale bar of length `0.005`: the leaf
  lies `0.0046` beyond the cut and `0.0041` inside the window's edge, both below a pixel in
  `terminalCrossing`.
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
      .scatterOfSamples "good, between the search ranges" (goodInGap.map sample)
        (radius := some 5),
      .scatterOfSamples "good: the walls lo = −10, hi = 3" (walls.map sample) (radius := some 6)]
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

/-- The world box of `terminalCrossing`. -/
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
    |>.named s!"the edge from n to n + e{sub k}"

/-- The rejected step from the leaf `n + e₀` to its candidate `n + e₀ - eₖ`. -/
def rejectedStep (k : Nat) : Item :=
  Plane.Exact.segment (proj leaf) (proj (shift leaf k (-1))) |>.faint |>.width 1.5 |>.dashed
    |>.named s!"the rejected step from n + e₀ to n + e₀ − e{sub k}"

/-- The neighbour `n + eₖ` of `n`, recording where it stands relative to the window. -/
def neighbourPoint (k : Nat) : Item :=
  Plane.Exact.point (proj (shift crossN k 1)) |>.role rightRole
    |>.named s!"n + e{sub k} = {labelText (shift crossN k 1)}, weight 1, a neighbour of n"
    |>.incident (windowSide (shift crossN k 1)).incidence "the window"

/-- The label of the neighbour `n + eₖ`. -/
def neighbourLabel (k : Nat) : Item :=
  Plane.Exact.label s!"n + e{sub k}" (proj (shift crossN k 1)) .auto |>.role rightRole

/-- The candidate `n + e₀ - eₖ` of the leaf, recording where it stands relative to the window. -/
def candidatePoint (k : Nat) : Item :=
  Plane.Exact.point (proj (shift leaf k (-1))) |>.faint |>.marker .ring
    |>.named s!"n + e₀ − e{sub k} = {labelText (shift leaf k (-1))}, weight 0, outside the window"
    |>.incident (windowSide (shift leaf k (-1))).incidence "the window"

/-- The label of the candidate `n + e₀ - eₖ`, placed `place`. -/
def candidateLabel (k : Nat) (place : Placement) : Item :=
  Plane.Exact.label s!"n + e₀ − e{sub k}" (proj (shift leaf k (-1))) place

/-- The window, the half-plane beyond the cut, the edge from `n` to the leaf `n + e₀` across the
good level `n₀ = 4`, the four other neighbours `n + eₖ` of `n` (inside the window) with their
edges, and the four candidates `n + e₀ - eₖ` of the leaf (outside it). -/
@[figure]
def terminalCrossing : Plane.Figure where
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
      |>.declRef `TDCSG.Five.div_two_lt_norm_sub_of_le_re,
    Plane.Exact.disk crossXPoint (53 / 50 : Rat) |>.role windowRole |>.fillOpacity 0.07
      |>.named "the window" |>.describedBy "the closed disk |w − x| ≤ r/2, r = 2.12, x = 0.472"
      |>.declRef `TDCSG.Five.InWindow,
    Plane.Exact.segment crossXPoint crossRim |>.role windowRole |>.width 1.5 |>.dashed
      |>.named "a radius r/2 = 1.06 of the window",
    Plane.Exact.labelBeside "r/2" crossXPoint crossRim |>.role windowRole,
    neighbourEdge 1, neighbourEdge 2, neighbourEdge 3, neighbourEdge 4,
    rejectedStep 1, rejectedStep 2, rejectedStep 3, rejectedStep 4,
    Plane.Exact.segment (proj crossN) (proj leaf) |>.width 3.5
      |>.named "the edge from n to n + e₀: it raises n₀ from the good level 4 to 5"
      |>.declRef `TDCSG.Five.IsGoodLevel.leaf,
    Plane.Exact.polygon zoomBox |>.width 1 |>.named "the square enlarged in the next figure",
    neighbourPoint 1, neighbourLabel 1, neighbourPoint 2, neighbourLabel 2,
    neighbourPoint 3, neighbourLabel 3, neighbourPoint 4, neighbourLabel 4,
    candidatePoint 1, candidateLabel 1 .belowLeft, candidatePoint 2, candidateLabel 2 .below,
    candidatePoint 3, candidateLabel 3 .above, candidatePoint 4, candidateLabel 4 .aboveLeft,
    Plane.Exact.point (proj crossN) |>.role leftRole |>.size 5
      |>.named s!"n = {labelText crossN}, weight 0, P(n) = 7 − 4φ, at the good level n₀ = 4"
      |>.incident (windowSide crossN).incidence "the window",
    Plane.Exact.point (proj leaf) |>.role rightRole |>.size 5
      |>.named s!"the leaf n + e₀ = {labelText leaf}, weight 1, P = 8 − 4φ"
      |>.incident (windowSide leaf).incidence "the window"
      |>.incident .inside "the half-plane Re w ≥ Re x + κ − η",
    Plane.Exact.label "n" (proj crossN) (.toward (Plane.deg 100)) (some 10) |>.role leftRole
      |>.italic,
    Plane.Exact.label "n₀ = 4 → 5" ((rat (21 / 20), rat (2 / 25)) : QSqrt5 × QSqrt5),
    Plane.Exact.label "window, x = 0.472" ((rat (-1 / 20), rat (5 / 4)) : QSqrt5 × QSqrt5)
      |>.role windowRole,
    Plane.Exact.label "Re w ≥ x + κ − η" ((rat (27 / 10), rat (-5 / 4)) : QSqrt5 × QSqrt5)
      .left |>.size 12]
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
    Plane.Exact.point leafQ |>.role rightRole |>.size 6
      |>.named "the leaf n + e₀, P = 8 − 4φ ≈ 1.52786",
    Plane.Exact.label "n + e₀ (leaf)" leafQ .above |>.role rightRole,
    Plane.Exact.label "0.005" ((rat (15185 / 10000), rat (-5 / 1000)) : QSqrt5 × QSqrt5) .above,
    Plane.Exact.label "edge from n" ((rat (1518 / 1000), rat 0) : QSqrt5 × QSqrt5) .below,
    Plane.Exact.label "cut" ((crossCut, rat (1 / 200)) : QSqrt5 × QSqrt5) .right,
    Plane.Exact.label "Re w = x + κ − η" ((crossCut, rat (1 / 200)) : QSqrt5 × QSqrt5) .left,
    Plane.Exact.label "window edge" ((rat (15322 / 10000), rat (-1 / 200)) :
      QSqrt5 × QSqrt5) .right |>.role windowRole]
  info := { title := "Near the leaf, enlarged: the cut, the leaf and the window's edge" }

/-! ### The facts the figures show -/

-- The good levels among `-13, …, 9` at `r = 1.8`, `x = 0.87` are `-10`, `-2`, `3`; every
-- reduced phase is decided.
#guard levels.filter good == [-10, -2, 3] && levels.all fun m => (reducedPhase m).isSome

-- The leaf lies beyond the cut and inside the window; `P(n) = 7 - 4φ`, `P(n + e₀) = 8 - 4φ`.
#guard QSqrt.lt crossCut (proj leaf).realPart &&
  windowSide leaf == .inside && windowSide crossN == .inside &&
  (proj crossN).realPart == ⟨5, -2⟩ && (proj crossN).conj == proj crossN &&
  (proj leaf).realPart == ⟨6, -2⟩

/-- What `levelPhases` plots, and why. Its one panel holds three series of markers, in this order:
the levels of `-13, …, 9` that are not good, the good levels in the gap `|m| ≤ 2` (`-2`), and the
walls `lo = -10`, `hi = 3`; each marker is at `(m, phaseAt m)`, the rational ball centre at
precision `64` of the exact reduced phase `t - ⌊t + 1/2⌋`, `t = phase/L` in `ℚ(√5)`, decided
for every level drawn. The good levels among them are exactly `-10`, `-2`, `3`, by the exact test
`isGoodLevel` (`TDCSG.Five.IsGoodLevel`); `-10` is the only good level from `-13` to `-3` and `3`
the only one from `3` to `9`, so they are the candidates for `lo` and `hi` in the range drawn, and
`-2` lies in the gap between the search ranges `m ≤ -3` and `m ≥ 3`. Not stated: the bands,
lines and texts (`notes`), the axes, the layout and the pixels. -/
theorem levelPhases_spec :
    levelPhases.panels.map (·.series) = #[#[
      .scatterOfSamples "not good" (notGood.map sample) (some notGoodGrey) (radius := some 3),
      .scatterOfSamples "good, between the search ranges" (goodInGap.map sample)
        (radius := some 5),
      .scatterOfSamples "good: the walls lo = −10, hi = 3" (walls.map sample)
        (radius := some 6)]] ∧
    levels = (List.range 23).map (fun (i : Nat) => (i : Int) - 13) ∧
    sample = (fun (m : Int) => ((m : Rat), phaseAt m)) ∧
    levels.filter good = [-10, -2, 3] ∧
    notGood = [-13, -12, -11, -9, -8, -7, -6, -5, -4, -3, -1, 0, 1, 2, 4, 5, 6, 7, 8, 9] ∧
    goodInGap = [-2] ∧ walls = [-10, 3] ∧
    (levels.filter fun m => good m && m ≤ -3) = [-10] ∧
    (levels.filter fun m => good m && 3 ≤ m) = [3] ∧
    levels.all (fun m => (reducedPhase m).isSome) = true := by
  refine ⟨by simp [levelPhases], rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves levelPhases levelPhases_spec

/-- What `terminalCrossing` draws, item for item, and why its records are right. The data are
`r = 53/25`, `x = 59/125`, `n = (4, -3, 1, 1, -3)` and the leaf `n + e₀`; the items are written
out in drawing order, those of the four neighbours `n + eₖ` and the four candidates `n + e₀ - eₖ`
(`k = 1, …, 4`) by the builders `neighbourEdge`, `rejectedStep`, `neighbourPoint`,
`neighbourLabel`, `candidatePoint` and `candidateLabel`, whose definitions are stated. The
records hold exactly: `n` has weight zero and its level `n₀ = 4` is good at `r = 2.12`,
`x = 0.472`; `n`, the leaf and every `n + eₖ` lie inside the window and every `n + e₀ - eₖ`
outside it (`windowSide`, from `|q P(m) - p|² ≤ q² r²/4` for `x = p/q`), so the leaf has no
neighbour but `n`; the leaf's real part `8 - 4φ` exceeds the cut `Re x + κ - η`, and
`P(n) = 7 - 4φ` is real. Not stated: how the builders and modifiers draw, the layout, the
lettering, the style's colour values and the pixels. -/
theorem terminalCrossing_spec :
    crossN = #[4, -3, 1, 1, -3] ∧ leaf = shift crossN 0 1 ∧ crossX = 59 / 125 ∧
    crossRadius = 53 / 25 ∧ crossCut = rat crossX + kappa - margin crossRadiusSq ∧
    (∀ k, neighbourEdge k = (Plane.Exact.segment (proj crossN) (proj (shift crossN k 1))
      |>.role "right" |>.width 1.5 |>.named s!"the edge from n to n + e{sub k}")) ∧
    (∀ k, rejectedStep k = (Plane.Exact.segment (proj leaf) (proj (shift leaf k (-1)))
      |>.faint |>.width 1.5 |>.dashed
      |>.named s!"the rejected step from n + e₀ to n + e₀ − e{sub k}")) ∧
    (∀ k, neighbourPoint k = (Plane.Exact.point (proj (shift crossN k 1)) |>.role "right"
      |>.named s!"n + e{sub k} = {labelText (shift crossN k 1)}, weight 1, a neighbour of n"
      |>.incident (windowSide (shift crossN k 1)).incidence "the window")) ∧
    (∀ k, neighbourLabel k =
      (Plane.Exact.label s!"n + e{sub k}" (proj (shift crossN k 1)) .auto |>.role "right")) ∧
    (∀ k, candidatePoint k = (Plane.Exact.point (proj (shift leaf k (-1))) |>.faint
      |>.marker .ring
      |>.named s!"n + e₀ − e{sub k} = {labelText (shift leaf k (-1))}, weight 0, outside the window"
      |>.incident (windowSide (shift leaf k (-1))).incidence "the window")) ∧
    (∀ k p, candidateLabel k p =
      Plane.Exact.label s!"n + e₀ − e{sub k}" (proj (shift leaf k (-1))) p) ∧
    terminalCrossing.items = #[
      Plane.Exact.polygon crossHalfPlane |>.faint |>.filled |>.noOutline |>.fillOpacity 0.16
        |>.named "the half-plane Re w ≥ Re x + κ − η"
        |>.describedBy "beyond the cut of the lens estimate, turned to the direction j = 0"
        |>.declRef `TDCSG.Five.div_two_lt_norm_sub_of_le_re,
      Plane.Exact.disk crossXPoint (53 / 50 : Rat) |>.role "window" |>.fillOpacity 0.07
        |>.named "the window" |>.describedBy "the closed disk |w − x| ≤ r/2, r = 2.12, x = 0.472"
        |>.declRef `TDCSG.Five.InWindow,
      Plane.Exact.segment crossXPoint crossRim |>.role "window" |>.width 1.5 |>.dashed
        |>.named "a radius r/2 = 1.06 of the window",
      Plane.Exact.labelBeside "r/2" crossXPoint crossRim |>.role "window",
      neighbourEdge 1, neighbourEdge 2, neighbourEdge 3, neighbourEdge 4,
      rejectedStep 1, rejectedStep 2, rejectedStep 3, rejectedStep 4,
      Plane.Exact.segment (proj crossN) (proj leaf) |>.width 3.5
        |>.named "the edge from n to n + e₀: it raises n₀ from the good level 4 to 5"
        |>.declRef `TDCSG.Five.IsGoodLevel.leaf,
      Plane.Exact.polygon zoomBox |>.width 1 |>.named "the square enlarged in the next figure",
      neighbourPoint 1, neighbourLabel 1, neighbourPoint 2, neighbourLabel 2,
      neighbourPoint 3, neighbourLabel 3, neighbourPoint 4, neighbourLabel 4,
      candidatePoint 1, candidateLabel 1 .belowLeft, candidatePoint 2, candidateLabel 2 .below,
      candidatePoint 3, candidateLabel 3 .above, candidatePoint 4, candidateLabel 4 .aboveLeft,
      Plane.Exact.point (proj crossN) |>.role "left" |>.size 5
        |>.named s!"n = {labelText crossN}, weight 0, P(n) = 7 − 4φ, at the good level n₀ = 4"
        |>.incident (windowSide crossN).incidence "the window",
      Plane.Exact.point (proj leaf) |>.role "right" |>.size 5
        |>.named s!"the leaf n + e₀ = {labelText leaf}, weight 1, P = 8 − 4φ"
        |>.incident (windowSide leaf).incidence "the window"
        |>.incident .inside "the half-plane Re w ≥ Re x + κ − η",
      Plane.Exact.label "n" (proj crossN) (.toward (Plane.deg 100)) (some 10) |>.role "left"
        |>.italic,
      Plane.Exact.label "n₀ = 4 → 5" ((rat (21 / 20), rat (2 / 25)) : QSqrt5 × QSqrt5),
      Plane.Exact.label "window, x = 0.472" ((rat (-1 / 20), rat (5 / 4)) : QSqrt5 × QSqrt5)
        |>.role "window",
      Plane.Exact.label "Re w ≥ x + κ − η" ((rat (27 / 10), rat (-5 / 4)) : QSqrt5 × QSqrt5)
        .left |>.size 12] ∧
    weight crossN = 0 ∧ isGoodLevel crossRadiusSq crossX 0 4 = some true ∧
    (windowSide crossN == .inside && windowSide leaf == .inside) = true ∧
    [1, 2, 3, 4].all (fun k => windowSide (shift crossN k 1) == .inside) = true ∧
    [1, 2, 3, 4].all (fun k => windowSide (shift leaf k (-1)) == .outside) = true ∧
    QSqrt.lt crossCut (proj leaf).realPart = true ∧
    ((proj crossN).realPart == ⟨5, -2⟩ && (proj crossN).conj == proj crossN &&
      (proj leaf).realPart == ⟨6, -2⟩) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ _ => rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves terminalCrossing terminalCrossing_spec

/-- What `terminalZoom` draws, item for item, and the distances it makes visible. The items are
written out in drawing order. The leaf `P(n + e₀) = 8 - 4φ` lies between `0.0045` and `0.0046`
beyond the cut `Re x + κ - η` and between `0.0041` and `0.0042` inside the window's edge
`x + r/2 = 1.532` on the real axis, so the scale bar of length `0.005` measures both gaps; at the
scale of `terminalCrossing` each is below a pixel. Not stated: the arc's angular extent (a
floating-point choice), how the builders draw, the layout and the pixels. -/
theorem terminalZoom_spec :
    leafQ = ((proj leaf).realPart, rat 0) ∧ edgeStart = (rat (1511 / 1000), rat 0) ∧
    terminalZoom.items = #[
      Plane.Exact.polygon [(crossCut, rat (-13 / 2000)), (rat (1542 / 1000), rat (-13 / 2000)),
          (rat (1542 / 1000), rat (13 / 2000)), (crossCut, rat (13 / 2000))]
        |>.faint |>.filled |>.noOutline |>.fillOpacity 0.16
        |>.named "the half-plane Re w ≥ Re x + κ − η",
      Plane.Exact.arc crossXPoint (53 / 50 : Rat) (-arcHalfAngle) arcHalfAngle |>.role "window"
        |>.named "the window's circle |w − x| = r/2",
      Plane.Exact.segment edgeStart leafQ |>.width 3.5 |>.named "the edge from n to n + e₀",
      Plane.Exact.segment ((rat (1516 / 1000), rat (-5 / 1000)) : QSqrt5 × QSqrt5)
          (rat (1521 / 1000), rat (-5 / 1000)) |>.width 2 |>.named "a scale bar of length 0.005",
      Plane.Exact.point leafQ |>.role "right" |>.size 6
        |>.named "the leaf n + e₀, P = 8 − 4φ ≈ 1.52786",
      Plane.Exact.label "n + e₀ (leaf)" leafQ .above |>.role "right",
      Plane.Exact.label "0.005" ((rat (15185 / 10000), rat (-5 / 1000)) : QSqrt5 × QSqrt5)
        .above,
      Plane.Exact.label "edge from n" ((rat (1518 / 1000), rat 0) : QSqrt5 × QSqrt5) .below,
      Plane.Exact.label "cut" ((crossCut, rat (1 / 200)) : QSqrt5 × QSqrt5) .right,
      Plane.Exact.label "Re w = x + κ − η" ((crossCut, rat (1 / 200)) : QSqrt5 × QSqrt5) .left,
      Plane.Exact.label "window edge" ((rat (15322 / 10000), rat (-1 / 200)) :
        QSqrt5 × QSqrt5) .right |>.role "window"] ∧
    QSqrt.lt (rat (45 / 10000)) ((proj leaf).realPart - crossCut) = true ∧
    QSqrt.lt ((proj leaf).realPart - crossCut) (rat (46 / 10000)) = true ∧
    QSqrt.lt (rat (41 / 10000)) (rat (crossX + 53 / 50) - (proj leaf).realPart) = true ∧
    QSqrt.lt (rat (crossX + 53 / 50) - (proj leaf).realPart) (rat (42 / 10000)) = true := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves terminalZoom terminalZoom_spec

end TDCSGFigures.Levels
