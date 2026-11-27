/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.PartTwo
import TDCSGFigures.Style

/-!
# The figures of chapter 5, the lens estimate

Two closed disks of radius `r/2` about `0` and `u = ζ`, their lens, and the half-planes
`Re v ≥ κ - η` (the hypothesis of the estimate) and `Re v ≥ κ`, with `κ = (2φ + 1)/4` and
`η = (3 + φ - r²)/16`. The tip of the lens is its corner of largest real part,
`u/2 + h (s, -c₁)` with `c₁ = Re ζ = (φ - 1)/2`, `s = Im ζ` and `h = √(r²/4 - 1/4)`; at a rational
radius its coordinates are `c₁/2 + √(h² s²)` and `√(s²/4) - √(h² c₁²)` (`Surd`s). The point
`v* = (1 + ζ - ζ²)/2 = 1 + t u` (`t = 1/2 - c₁`) of the proof lies at distance `R/2` from `0` and
from `u` and has real part `κ`.

* `lensEstimate`: the picture at `r = 1.8`, every element labelled.
* `lensRadius`: a loop through `r = 1.8, 2, 2.08, 2.12` and
  `R = √(3 + φ)`, drawn from these pictures (`Setting.motion`); the tip moves towards the cuts and
  meets both at `R`, where `η = 0` and the tip is `v*`.

The chapter's claim that the estimate is sharp exactly at `R` is checked exactly at the radii
drawn: the tip's real part is at most `κ - 2η` (`tipReLe`), so it lies left of `κ - η` below `R`,
and at `R` it is `κ` (`vStar`). The disk `|v| ≤ r/2` reaches `Re v = κ - η` only when
`r/2 ≥ κ - (R² - r²)/16`, that is `r² - 8r + 7φ + 1 ≤ 0` (as `16κ - R² = 7φ + 1`), so for
`r < 4 - √(15 - 7φ) ≈ 2.083` the estimate holds for want of any `v`: at `r = 1.8`, `2` and `2.08`
the disk stays left of the cut, at `2.12` it crosses it and the lens still does not.
-/

namespace TDCSGFigures.Lens

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-! ### The data -/

/-- `c₁ = Re ζ = (φ - 1)/2`. -/
def cosine : QSqrt5 := (zeta 1).realPart

/-- `s² = 1 - c₁²`, the square of `s = Im ζ = sin 72°`. -/
def sineSq : QSqrt5 := rat 1 - cosine * cosine

/-- `h² = (r/2)² - 1/4` at the half radius `ρ = r/2`. -/
def hSq (ρ : Rat) : QSqrt5 := rat (ρ * ρ - 1 / 4)

/-- The tip of the lens of the disks of radius `ρ` about `0` and `u`, given `h² = ρ² - 1/4`:
`(c₁/2 + √(h² s²), √(s²/4) - √(h² c₁²))`. -/
def tipOf (h2 : QSqrt5) : SurdPoint :=
  ⟨{ base := cosine * rat (1 / 2), roots := [(1, h2 * sineSq)] },
    { roots := [(1, sineSq * rat (1 / 4)), (-1, h2 * (cosine * cosine))] }⟩

/-- The tip of the lens at the half radius `ρ`: `(c₁/2 + √(h² s²), √(s²/4) - √(h² c₁²))`. -/
def tip (ρ : Rat) : SurdPoint := tipOf (hSq ρ)

/-- `u = ζ` with the coordinates `(c₁, √(s²))`. -/
def uSurd : SurdPoint := ⟨Surd.ofQ cosine, { roots := [(1, sineSq)] }⟩

/-- The point `v* = (1 + ζ - ζ²)/2 = 1 + t u` of the proof, the tip at `R`. -/
def vStar : ZetaFrac := ⟨Zeta5.ofInt 1 + zeta 1 - zeta 2, 2⟩

/-- The squared critical radius `R² = 3 + φ`. -/
def criticalSq : QSqrt5 := threePlusPhi

/-- `κ - η` at the squared radius `r2`. -/
def cut (r2 : QSqrt5) : QSqrt5 := kappa - margin r2

/-- The half-planes are drawn as rectangles filling the shown box to its edges: from `-1.1` to
`2.4`. -/
def yLow : QSqrt5 := rat (-11 / 10)

/-- The top of the rectangles. -/
def yHigh : QSqrt5 := rat (12 / 5)

/-- The right edge of the rectangles. -/
def xRight : QSqrt5 := rat (7 / 4)

/-- The half-plane `Re v ≥ a` as far as the picture shows it: the rectangle
`[a, 1.75] × [-1.1, 2.4]`. -/
def halfPlane (a : QSqrt5) : List (QSqrt5 × QSqrt5) :=
  [(a, yLow), (xRight, yLow), (xRight, yHigh), (a, yHigh)]

/-- The world box every lens picture shows. -/
def view : Box := ⟨-1.15, -1.1, 1.75, 2.4⟩

/-- The height at which the margin `η` between the cuts is drawn, near the top of the box. -/
def marginY : QSqrt5 := rat (21 / 10)

/-- The height of the labels of the half-planes, at the top of the box. -/
def cutLabelY : QSqrt5 := rat (9 / 4)

/-- The end of the drawn radius of the disk `|v| ≤ h`, down and to the left of `0`:
`h (-3/5, -4/5)`. -/
def radiusEnd (h : Float) : Point := ⟨-0.6 * h, -0.8 * h⟩

/-- Whether the point `p` lies on both circles of squared radius `ρ2` about `0` and `u = ζ`, read
off its own coordinates: `p` must be `(b + √A, √B - √C)` with `b = c₁/2`, `B = s²/4`, `A, C ≥ 0`
and `c₁ > 0`. Then `|p|² = c₁²/4 + A + B + C + c₁√A - √(s² C)` and
`|p - u|² = c₁²/4 + A + B + C - c₁√A + √(s² C)` (as `u = (c₁, √(s²))`), so `c₁² A = s² C` makes
both `c₁²/4 + A + B + C`, which must be `ρ2`. A point of another form is refused. -/
def tipOnCircles (p : SurdPoint) (ρ2 : QSqrt5) : Bool :=
  match p.re, p.im with
  | ⟨b, [(sa, A)]⟩, ⟨y0, [(sb, B), (sc, C)]⟩ =>
    sa == 1 && sb == 1 && sc == -1 && y0 == ⟨0, 0⟩ && b == cosine * rat (1 / 2) &&
      B == sineSq * rat (1 / 4) && QSqrt.lt ⟨0, 0⟩ cosine && QSqrt.le ⟨0, 0⟩ A &&
      QSqrt.le ⟨0, 0⟩ C && cosine * cosine * A == sineSq * C &&
      cosine * cosine * rat (1 / 4) + A + B + C == ρ2
  | _, _ => false

/-- Whether the real part of the point `p`, of the form `b + √A`, is at most `K` (`strict`: less
than `K`), read off its own coordinates. A point of another form is refused. -/
def reAtMost (p : SurdPoint) (K : QSqrt5) (strict : Bool := false) : Bool :=
  match p.re with
  | ⟨b, [(1, A)]⟩ => sqrtLt A (K - b) || (!strict && sqrtEq A (K - b))
  | _ => false

/-- The decided relations of the tip `tip ρ` at the half radius `ρ = r/2`: it lies on both
circles (`tipOnCircles`), and its real part is less than `κ - η`. -/
def tipFacts (ρ : Rat) : Bool :=
  tipOnCircles (tip ρ) (rat (ρ * ρ)) && reAtMost (tip ρ) (cut (rat (4 * ρ * ρ))) true

/-! ### The picture -/

/-- What changes from one lens picture to the next. -/
structure Setting (β : Type) where
  /-- The half radius `r/2`, the radius of both disks. -/
  half : β
  /-- `r²`. -/
  r2 : QSqrt5
  /-- `r` as text. -/
  rText : String
  /-- The tip as an item recording its relations. -/
  tipPt : Item
  /-- The tip's page coordinates before fitting, for its label. -/
  tipXY : Point
  /-- Where `0` stands relative to the circle about `u` and `u` relative to the circle about `0`
  (`|u|² = 1` against `(r/2)²`). -/
  other : Side
  /-- Whether `r = R`, where the cuts `κ - η` and `κ` coincide and the tip is `v*`. -/
  critical : Bool
  /-- Whether `v*` is drawn apart from the tip (far enough from it to be seen as a point of its
  own). -/
  showVStar : Bool
  /-- Whether the margin `η` is wide enough to be drawn as a dimension line. -/
  showMargin : Bool
  /-- Whether the picture is a key of a loop (`TDCSGFigures.Lens.LensLoopConfig`): the items that
  change with the radius are actors (`Setting.act`); the labels of `0`, `u` and `c₁` are placed
  explicitly (below, above right, below), clear of every circle at every radius of the loop, so
  that they keep their places; the titles of the circles and of the cut do not name the radius
  (so that the circles can be drawn alike at every radius but for their path data); the real axis
  is a segment across the box; and the radius is written at the top left. -/
  motion : Bool := false
  /-- The row of the radius written at the top left, in a key of a loop: `0`, or `1` a line below,
  so that consecutive keys write their radii in different rows and the two never overlap while
  one fades out and the next fades in. -/
  radiusRow : Nat := 0

/-- The item `it` as the actor `id` in a key of a loop; unchanged otherwise. -/
def Setting.act {β : Type} (st : Setting β) (id : String) (it : Item) : Item :=
  if st.motion then it.actor id else it

/-- The radius as the title of a circle or of the cut names it: `r = <value>`, or nothing in a key
of a loop. -/
def Setting.atR {β : Type} (st : Setting β) : String :=
  if st.motion then "" else s!", r = {st.rText}"

/-- The items of a lens picture: the half-planes `Re v ≥ κ - η` (below `R`) and `Re v ≥ κ`,
outlined (`κ - η` dashed), the real axis, the two disks and their lens, the foot of `u` on the
real axis, the margin `η` between the cuts as a dimension line (when `showMargin`), a radius `r/2`
of `|v| ≤ r/2`, the points `0`, `u`, `c₁`, the tip and `v*`, and their labels, each beside what it
names; in a key of a loop (`Setting.motion`), the radius at the top left, and neither the name
`η` of the margin nor `η = 0` at `R`, which the captions of the loop give. -/
def lensItems {β : Type} [RealValue β] (st : Setting β) : Array Item :=
  let kc := cut st.r2
  let foot : QSqrt5 × QSqrt5 := (cosine, ⟨0, 0⟩)
  (if st.critical then #[] else #[
    Plane.Exact.polygon (halfPlane kc) |>.faint |>.filled |>.width 1 |>.dashed
      |>.fillOpacity 0.16 |>.named "the half-plane Re v ≥ κ − η"
      |>.describedBy (if st.motion then "where the lens estimate puts no point of the lens"
        else s!"where the lens estimate puts no point of the lens, at r = {st.rText}")
      |>.declRef `TDCSG.Five.div_two_lt_norm_sub_of_le_re |> st.act "cut"]) ++ #[
    Plane.Exact.polygon (halfPlane kappa) |>.faint |>.filled |>.width 1 |>.fillOpacity 0.18
      |>.named "the half-plane Re v ≥ κ"
      |>.describedBy "κ = (2φ + 1)/4 = (1 + L)/2, L = φ − 1/2",
    (if st.motion then
      Plane.Exact.segment ((rat (-23 / 20), rat 0) : QSqrt5 × QSqrt5) (xRight, rat 0) |>.faint
        |>.width 1 |>.named "the real axis"
    else Plane.Exact.line origin rightCentre |>.faint |>.width 1 |>.named "the real axis"),
    Plane.Exact.disk origin st.half |>.noFill |>.role windowRole
      |>.named "the circle |v| = r/2" |>.describedBy s!"the closed disk |v| ≤ r/2{st.atR}"
      |> st.act "disk-0",
    Plane.Exact.disk (zeta 1) st.half |>.noFill |>.role windowRole |>.dashed
      |>.named "the circle |v − u| = r/2"
      |>.describedBy s!"the closed disk |v − u| ≤ r/2 about u = ζ{st.atR}" |> st.act "disk-u",
    Plane.Exact.lens origin (zeta 1) st.half st.half |>.role lensRole |>.noOutline
      |>.fillOpacity 0.12 |>.named "the lens" |> st.act "lens",
    Plane.Exact.segment uSurd ⟨Surd.ofQ cosine, Surd.ofQ ⟨0, 0⟩⟩ |>.faint |>.width 1
      |>.dashed #[2, 3] |>.named "the foot of u on the real axis"] ++
  (if st.showMargin then #[
    Plane.Exact.segment (kc, marginY) (kappa, marginY) |>.width 1
      |>.named "the margin η = (3 + φ − r²)/16 between the cuts κ − η and κ"
      |>.declRef `TDCSG.Five.IsGoodLevel |> st.act "margin",
    Plane.Exact.tickAt (kc, marginY) (kc, marginY) (kappa, marginY) |> st.act "margin-tick-cut",
    Plane.Exact.tickAt (kappa, marginY) (kc, marginY) (kappa, marginY)
      |> st.act "margin-tick-kappa"] ++
    (if st.motion then #[] else #[Plane.Exact.labelBeside "η" (kc, marginY) (kappa, marginY)])
    else #[]) ++ #[
    Plane.segment ⟨0, 0⟩ (radiusEnd (RealValue.toFloat st.half)) |>.role windowRole |>.width 1.5
      |>.dashed |>.named "a radius r/2 of the disk |v| ≤ r/2" |> st.act "radius",
    Plane.labelBeside "r/2" ⟨0, 0⟩ (radiusEnd (RealValue.toFloat st.half)) |>.role windowRole
      |> st.act "radius-label",
    Plane.Exact.point origin |>.role windowRole |>.named "0, the center of |v| ≤ r/2"
      |> (if st.motion then (·.incident .on "the real axis") else id)
      |>.incident .inside "the circle |v| = r/2"
      |>.incident st.other.incidence "the circle |v − u| = r/2"
      |>.incident (Side.lens .inside st.other).incidence "the lens",
    Plane.Exact.point (zeta 1) |>.role windowRole |>.named "u = ζ, the center of |v − u| ≤ r/2"
      |>.incident .inside "the circle |v − u| = r/2"
      |>.incident st.other.incidence "the circle |v| = r/2"
      |>.incident (Side.lens .inside st.other).incidence "the lens",
    Plane.Exact.point foot |>.faint |>.size 3
      |>.named "c₁ = Re u = (φ − 1)/2 on the real axis" |>.incident .on "the real axis",
    st.act "tip" st.tipPt] ++
  (if st.showVStar then #[
    Plane.Exact.point vStar |>.named "v∗ = 1 + t u, t = 1/2 − c₁, at distance R/2 from 0 and u"
      |>.incident .outside "the circle |v| = r/2" |>.incident .outside "the circle |v − u| = r/2"
      |>.incident .outside "the lens" |>.incident .on "the half-plane Re v ≥ κ"
      |>.incident .inside "the half-plane Re v ≥ κ − η" |> st.act "vstar",
    Plane.Exact.label "v∗" vStar .auto |> st.act "vstar-label"] else #[]) ++ #[
    (if st.motion then Plane.Exact.label "0" origin .below (some 12)
      else Plane.Exact.label "0" origin .auto) |>.role windowRole |> st.act "label-0",
    (if st.motion then Plane.Exact.label "u = ζ" (zeta 1) .aboveRight (some 8)
      else Plane.Exact.label "u = ζ" (zeta 1) .auto) |>.role windowRole |> st.act "label-u",
    (if st.motion then Plane.Exact.label "c₁" foot .below (some 16)
      else Plane.Exact.label "c₁" foot .auto) |> st.act "label-c1",
    Plane.label (if st.critical then "tip = v∗" else "tip") st.tipXY .auto
      |> st.act (if st.critical then "tip-label-critical" else "tip-label"),
    Plane.Exact.label "lens" ((rat (1 / 10), rat (11 / 20)) : QSqrt5 × QSqrt5) |>.role lensRole,
    Plane.Exact.label "|v| ≤ r/2" ((rat (3 / 10), rat (-11 / 20)) : QSqrt5 × QSqrt5)
      |>.role windowRole,
    Plane.Exact.label "|v − u| ≤ r/2" ((rat (9 / 20), rat (3 / 2)) : QSqrt5 × QSqrt5)
      |>.role windowRole,
    Plane.Exact.label (if st.critical && !st.motion then "Re v ≥ κ, η = 0" else "Re v ≥ κ")
      ((kappa, cutLabelY) : QSqrt5 × QSqrt5) .right |> st.act "kappa-label"] ++
  (if st.critical then #[] else #[
    Plane.Exact.label "Re v ≥ κ − η →" ((kc, cutLabelY) : QSqrt5 × QSqrt5) .left
      |> st.act "cut-label"]) ++
  (if st.motion then #[
    Plane.Exact.label s!"r = {st.rText}"
      ((rat (-11 / 10), rat (9 / 4) - rat (st.radiusRow / 5)) : QSqrt5 × QSqrt5)
      .right |>.bold |> st.act s!"r-{st.rText}"] else #[])

/-- Where `|u|² = 1` stands against `(r/2)²`. -/
def otherSide (ρ2 : QSqrt5) : Side :=
  if ρ2 == rat 1 then .on else if QSqrt.lt rat1 ρ2 then .inside else .outside
where
  /-- `1`. -/
  rat1 : QSqrt5 := rat 1

/-- The tip `p` of the lens, recording that it lies on both circles and on the lens, and, given
`cuts`, where it stands relative to both half-planes. -/
def tipItemWith (p : SurdPoint) (cuts : Option Plane.Incidence) : Item :=
  let it := Plane.Exact.point p |>.size 5
    |>.named "the tip of the lens: its corner of largest real part"
    |>.incident .on "the circle |v| = r/2" |>.incident .on "the circle |v − u| = r/2"
    |>.incident .on "the lens"
  match cuts with
  | some i => it |>.incident i "the half-plane Re v ≥ κ − η" |>.incident i "the half-plane Re v ≥ κ"
  | none => it

/-- The tip at the half radius `ρ`, recording that it lies on both circles and outside both
half-planes (`tipFacts`). -/
def tipItem (ρ : Rat) : Item := tipItemWith (tip ρ) (some .outside)

/-- The setting at the rational radius `r = 2ρ`, with `v*` drawn apart from the tip and the
margin `η` drawn as a dimension line when `showVStar` (at `r = 1.8`; from `r = 2` on `v*` is too
near the tip to be seen apart, and `η` is a few pixels wide). -/
def settingAt (ρ : Rat) (rText : String) (showVStar : Bool) : Setting Rat :=
  { half := ρ, r2 := rat (4 * ρ * ρ), rText, tipPt := tipItem ρ,
    tipXY := PlanePoint.toPoint (tip ρ), other := otherSide (rat (ρ * ρ)), critical := false,
    showVStar, showMargin := showVStar }

/-- A lens picture. -/
def lensFigure {β : Type} [RealValue β] (st : Setting β) (narrow : Bool) : Plane.Figure where
  width := figureWidth
  narrowWidth := if narrow then some narrowWidth else none
  view := some view
  padding := 1
  style := partTwoStyle
  checks := .fail
  items := lensItems st
  info := { title := s!"The lens at r = {st.rText} and the half-planes Re v ≥ κ − η and Re v ≥ κ" }

/-- The lens picture at the rational radius `r = 2ρ`. -/
def frameAt (ρ : Rat) (rText : String) (showVStar narrow : Bool) : Plane.Figure :=
  lensFigure (settingAt ρ rText showVStar) narrow

/-- Two closed disks of radius r/2 = 0.9 about 0 and u = ζ, their lens, and the half-planes
Re v ≥ κ − η and Re v ≥ κ: the tip of the lens lies left of both. -/
@[figure]
def lensEstimate : Plane.Figure := frameAt (9 / 10) "1.8" true true

/-! ### The facts the figures show -/

-- `v*` lies on both circles of radius `R/2` and has real part `κ`; the other corner
-- `(ζ + ζ² - 1)/2 = ζ² conj v*` of the lens at `R` lies on both circles too.
#guard vStar.normSq == criticalSq * rat (1 / 4) &&
  (vStar - ZetaFrac.ofZeta (zeta 1)).normSq == criticalSq * rat (1 / 4) &&
  vStar.realPart == kappa &&
  (ZetaFrac.mk (zeta 1 + zeta 2 - Zeta5.ofInt 1) 2).normSq == criticalSq * rat (1 / 4)

/-- The chapter's sharpness claim at the half radius `ρ`, exactly: the real part of `tip ρ` is at
most `κ - 2η`, so strictly below `κ - η` when `η > 0` (for every radius, every point of the lens:
`TDCSG.Five.re_le_of_mem_lens`). -/
def tipReLe (ρ : Rat) : Bool :=
  reAtMost (tip ρ) (kappa - margin (rat (4 * ρ * ρ)) * rat 2)

-- At `R` the bound is an equality: `h² = s²` there, and `c₁/2 + s² = κ`.
#guard hSq 0 + criticalSq * rat (1 / 4) == sineSq && cosine * rat (1 / 2) + sineSq == kappa

-- `16κ - R² = 7φ + 1`, the constant of the threshold `r² - 8r + 7φ + 1 = 0`.
#guard kappa * rat 16 - criticalSq == phi * rat 7 + rat 1

/-! ### The lens as the radius grows to `R`

`lensRadius`, a looping animation of the lens pictures of chapter 5 (`lensItems`) at increasing
radii, ending at the critical radius `R = √(3 + φ)`, beside the neighbourhood of the tip enlarged
(`zoomItems`), the two panels on one clock. Its keys are the exact pictures at the radii of
`LensLoopConfig.radii`, then two at `R`: the first with the dashed edge `Re v = κ - η` where it
has arrived, on `Re v = κ` (`η = 0`), and the tip there; the last with the two half-planes one and
the tip `v*`, the data of the lens picture at `R` drawn in the loop's layout (narrower, beside the
enlarged panel, the real axis a segment across the box, the radius written at the top left).

The lens is a function of the radius, and so are the circles, the dashed edge, the drawn radius,
the tip and its label: between two keys of different radii they are morphed through the exact
pictures at `samples - 1` radii between them (`r²` evenly spaced, all of them below `R`;
`LensLoopConfig.between`, `LensLoopConfig.zoomBetween`), and the browser interpolates the path
data linearly only between two consecutive samples. So at every sample the tip is the exact tip of
the sampled radius, on the perpendicular bisector of `0` and `u`. What one key shows and the next
does not (the margin `η` and `v*` of the first key, the bar of the margin in the enlarged panel at
`R`, the labels that change their words at `R`) fades.

The tip's title is set after its records, so that it does not list them (`tipTitle`): the records
change at `R`, where the tip lies on the edges, and an actor that morphs is drawn alike at every
radius but for its path data. The layout checks of every key still read the records.
-/

/-- `h² = r²/4 - 1/4` at the squared radius `r2`. -/
def hSqOf (r2 : QSqrt5) : QSqrt5 := r2 * rat (1 / 4) - rat (1 / 4)

/-- The title of the tip in the loop (see the module docstring). -/
def tipTitle : String := "the tip of the lens: its corner of largest real part"

/-- The setting of a key of the loop at the squared radius `r2` (`r` written `rText`), with the cut
`κ - η` drawn: the half radius `√(r²/4)`, the tip `tipOf (hSqOf r2)` recording that it lies on
both circles and on the lens, and `cuts` relative to both half-planes (`.outside` below `R`, `.on`
at `R`); `v*` and the margin `η` drawn apart when `first`. -/
def loopSetting (r2 : QSqrt5) (rText : String) (first : Bool)
    (cuts : Plane.Incidence := .outside) (radiusRow : Nat := 0) : Setting (SqrtOf QSqrt5) :=
  { half := ⟨r2 * rat (1 / 4)⟩, r2, rText,
    tipPt := tipItemWith (tipOf (hSqOf r2)) (some cuts) |>.named tipTitle,
    tipXY := PlanePoint.toPoint (tipOf (hSqOf r2)), other := otherSide (r2 * rat (1 / 4)),
    critical := false, showVStar := first, showMargin := first, motion := true, radiusRow }

/-- The setting of the last key: at `R`, the two half-planes one, the tip `tipOf (hSqOf R²)`, which
is `v*`, on the edge of `Re v ≥ κ`. -/
def criticalSetting : Setting (SqrtOf QSqrt5) :=
  { loopSetting criticalSq "R = √(3 + φ)" false .on with
    critical := true,
    tipPt := tipItemWith (tipOf (hSqOf criticalSq)) none
      |>.incident .on "the half-plane Re v ≥ κ" |>.named tipTitle }

/-! ### The neighbourhood of the tip, enlarged -/

/-- The right edge of the half-planes in the enlarged panel, whose box (about
`[0.84, 1.09] × [0.08, 0.34]`) the arcs through the tip fix on the left. -/
def zoomRight : QSqrt5 := rat (109 / 100)

/-- The bottom of the enlarged box. -/
def zoomBottom : QSqrt5 := rat (2 / 25)

/-- The top of the enlarged box. -/
def zoomTop : QSqrt5 := rat (8 / 25)

/-- The height of the bar that spans the margin `η` in the enlarged panel, above the box. -/
def zoomBarY : QSqrt5 := rat (17 / 50)

/-- The half-plane `Re v ≥ a` as far as the enlarged box shows it. -/
def zoomHalfPlane (a : QSqrt5) : List (QSqrt5 × QSqrt5) :=
  [(a, zoomBottom), (zoomRight, zoomBottom), (zoomRight, zoomTop), (a, zoomTop)]

/-- The width of the enlarged panel, in pixels. -/
def zoomWidth : Float := 216

/-- Half the angle of the arcs of the two circles drawn about the tip, in radians. -/
def zoomArc : Float := 0.08

/-- The angle of the point `p` seen from `c`, in radians. -/
def angleFrom (c p : Point) : Float := Float.atan2 (p.y - c.y) (p.x - c.x)

/-- The tip in the enlarged panel at the setting `st`: `tipOf (hSqOf st.r2)`, recording that it
lies on both circles and where it stands relative to the half-planes (`.outside` both below `R`,
`.on` both at `R`; on `Re v ≥ κ` at the last key). -/
def zoomTip (st : Setting (SqrtOf QSqrt5)) : Item :=
  let it := Plane.Exact.point (tipOf (hSqOf st.r2)) |>.size 5
    |>.incident .on "the circle |v| = r/2" |>.incident .on "the circle |v − u| = r/2"
  let it := if st.critical then it.incident .on "the half-plane Re v ≥ κ"
    else
      let i := if st.r2 == criticalSq then Plane.Incidence.on else .outside
      it.incident i "the half-plane Re v ≥ κ − η" |>.incident i "the half-plane Re v ≥ κ"
  it.named tipTitle |>.actor "tip"

/-- The margin in the enlarged panel at the setting `st`, above the box: below `R` the bar from
`κ - η` to `κ` with its ticks and its name `η`; at `R` the words `η = 0` above `κ`, higher than the
name `η`, so that the two never overlap while one fades out and the other fades in. -/
def zoomMargin (st : Setting (SqrtOf QSqrt5)) : Array Item :=
  let kc := cut st.r2
  if st.r2 == criticalSq then #[
    Plane.Exact.label "η = 0" ((kappa, zoomBarY) : QSqrt5 × QSqrt5) .above (some 26)
      |>.actor "zoom-eta-zero"]
  else #[
    Plane.Exact.segment (kc, zoomBarY) (kappa, zoomBarY) |>.width 1
      |>.named "the margin η between the edges" |>.actor "zoom-margin",
    Plane.Exact.tickAt (kc, zoomBarY) (kc, zoomBarY) (kappa, zoomBarY) |>.actor "zoom-tick-cut",
    Plane.Exact.tickAt (kappa, zoomBarY) (kc, zoomBarY) (kappa, zoomBarY)
      |>.actor "zoom-tick-kappa",
    Plane.Exact.labelBeside "η" (kc, zoomBarY) (kappa, zoomBarY) |>.actor "zoom-eta"]

/-- The items of the enlarged panel at the setting `st` (`r²` is `st.r2`), from the same data as
the whole picture: the half-plane `Re v ≥ κ` and, unless at the last key, `Re v ≥ κ - η` (dashed
edge), within the box; the arcs of the circles `|v| = r/2` and `|v − u| = r/2` through the tip
(exact centres and radius; the angles only choose the piece drawn); the tip (`zoomTip`),
unlabelled (the panel's title names it, and a label beside it would run into an arc or a
half-plane at some radius); the labels of the edges at the bottom of the box (below `R` only for
`κ - η`, which at `R` would run into `κ`); and the margin above it (`zoomMargin`). Its actors
have the ids of the whole picture's, and morph as they do. -/
def zoomItems (st : Setting (SqrtOf QSqrt5)) : Array Item :=
  let kc := cut st.r2
  let a0 := angleFrom ⟨0, 0⟩ st.tipXY
  let au := angleFrom (PlanePoint.toPoint (zeta 1)) st.tipXY
  #[Plane.Exact.polygon (zoomHalfPlane kappa) |>.faint |>.filled |>.width 1 |>.fillOpacity 0.18
      |>.named "the half-plane Re v ≥ κ"] ++
  (if st.critical then #[] else #[
    Plane.Exact.polygon (zoomHalfPlane kc) |>.faint |>.filled |>.width 1 |>.dashed
      |>.fillOpacity 0.16 |>.named "the half-plane Re v ≥ κ − η" |>.actor "cut"]) ++ #[
    Plane.Exact.arc origin st.half (a0 - zoomArc) (a0 + zoomArc) |>.role windowRole
      |>.named "the circle |v| = r/2" |>.actor "disk-0",
    Plane.Exact.arc (zeta 1) st.half (au - zoomArc) (au + zoomArc) |>.role windowRole |>.dashed
      |>.named "the circle |v − u| = r/2" |>.actor "disk-u",
    zoomTip st,
    Plane.Exact.label "κ" ((kappa, zoomBottom) : QSqrt5 × QSqrt5) .belowRight
      |>.actor "kappa-label"] ++
  (if st.r2 == criticalSq then #[] else #[
    Plane.Exact.label "κ − η" ((kc, zoomBottom) : QSqrt5 × QSqrt5) .belowLeft
      |>.actor "cut-label"]) ++
  zoomMargin st

/-! ### The loop -/

/-- The loop through the lens pictures as the radius grows to `R` (see the module docstring); the
defaults are the figure `lensRadius`. -/
structure LensLoopConfig where
  /-- The radii below `R`, increasing, with their values as text. -/
  radii : Array (Rat × String) := #[(9 / 5, "1.8"), (2, "2"), (52 / 25, "2.08"), (53 / 25, "2.12")]
  /-- The number of intervals of a morph, each ended by an exact picture. -/
  samples : Nat := 6
  /-- The duration of a step that changes the radius, in seconds. -/
  stepTime : Rat := 6 / 5
  /-- The rest at every key but the first and the last, in seconds. -/
  hold : Rat := 3 / 2

namespace LensLoopConfig

variable (cfg : LensLoopConfig)

/-- The number of keys: one per radius below `R`, and two at `R`. -/
def keyCount : Nat := cfg.radii.size + 2

/-- `r²` at key `k` (`3 + φ` for the two keys at `R`). -/
def r2At (k : Nat) : QSqrt5 :=
  match cfg.radii[k]? with
  | some (r, _) => rat (r * r)
  | none => criticalSq

/-- The setting of key `k`: the radius of `radii`, `v*` and the margin drawn at key `0`; then `R`
with the cut on `Re v = κ`; then the last key (`criticalSetting`). The radius is written in row
`k % 2`, the two keys at `R` in the same row. -/
def setting (k : Nat) : Setting (SqrtOf QSqrt5) :=
  match cfg.radii[k]? with
  | some (_, t) => loopSetting (cfg.r2At k) t (k == 0) .outside (k % 2)
  | none =>
    if k == cfg.radii.size then loopSetting criticalSq "R = √(3 + φ)" false .on (k % 2)
    else { criticalSetting with radiusRow := (k - 1) % 2 }

/-- The width of the whole picture's panel: the figure's width but for the gap and the enlarged
panel. -/
def mainWidth : Float := figureWidth - 24 - zoomWidth

/-- Key `k` of the whole picture: the lens picture of its setting, without a view of its own. -/
def key (k : Nat) : Plane.Figure :=
  { lensFigure (cfg.setting k) false with view := none, width := mainWidth }

/-- Key `k` of the enlarged panel: `zoomItems` of the same setting. -/
def zoomKey (k : Nat) : Plane.Figure :=
  { cfg.key k with items := zoomItems (cfg.setting k), width := zoomWidth }

/-- The ids of the actors of the figure `f`. -/
def actorIds (f : Plane.Figure) : Array String := f.items.filterMap (·.actorId?)

/-- Whether step `j` changes the radius. -/
def grows (j : Nat) : Bool := j < cfg.radii.size

/-- The moves of step `j` in the panel whose keys are `keyAt`: when the radius changes, the actors
of both keys morph through the exact pictures between (`between`), the tip and its label included
(they stay otherwise); those of key `j` alone vanish, those of key `j + 1` alone appear. -/
def movesOf (keyAt : Nat → Plane.Figure) (j : Nat) : Array (String × Move) :=
  let a := actorIds (keyAt j)
  let b := actorIds (keyAt (j + 1))
  (if cfg.grows j then (a.filter b.contains).map (·, Move.morph) else #[]) ++
    (a.filter (!b.contains ·)).map (·, Move.vanish) ++
    (b.filter (!a.contains ·)).map (·, Move.appear)

/-- The squared radius at the fraction `q` of step `j`: `(1 - q) r_j² + q r_{j+1}²`. -/
def r2Between (j : Nat) (q : Rat) : QSqrt5 := cfg.r2At j * rat (1 - q) + cfg.r2At (j + 1) * rat q

/-- The whole picture at the fraction `q` of step `j`: the lens picture at the squared radius
`r2Between j q`. -/
def between (j : Nat) (q : Rat) : Option Plane.Figure :=
  if cfg.grows j then
    some { cfg.key j with items := lensItems (loopSetting (cfg.r2Between j q) "" false) }
  else none

/-- The enlarged panel at the fraction `q` of step `j`. -/
def zoomBetween (j : Nat) (q : Rat) : Option Plane.Figure :=
  if cfg.grows j then
    some { cfg.zoomKey j with items := zoomItems (loopSetting (cfg.r2Between j q) "" false) }
  else none

/-- Whether the tip drawn at the squared radius `r2`, `tipOf (hSqOf r2)`, lies on both circles of
radius `r/2` about `0` and `u` (`tipOnCircles`), and so on the perpendicular bisector of `0` and
`u`, with real part at most `κ - 2η` (`reAtMost`). -/
def tipOnBoth (r2 : QSqrt5) : Bool :=
  tipOnCircles (tipOf (hSqOf r2)) (r2 * rat (1 / 4)) &&
    reAtMost (tipOf (hSqOf r2)) (kappa - margin r2 * rat 2)

/-- Whether every picture between two keys of different radii is at a radius below `R`
(`r2Between j (i / samples)`, `0 < i < samples`, below `R²`), with its tip on both circles and
at most `κ - 2η` (`tipOnBoth`). -/
def samplesBelowR : Bool :=
  (List.range cfg.radii.size).all fun j => (List.range (cfg.samples - 1)).all fun i =>
    let r2 := cfg.r2Between j ((i + 1 : Nat) / (cfg.samples : Rat))
    QSqrt.lt r2 criticalSq && tipOnBoth r2

/-- Whether the disk `|v| ≤ r/2` lies left of the dashed edge at the radius `r`. -/
def diskLeftOfCut (r : Rat) : Bool := QSqrt.lt (rat (r / 2)) (cut (rat (r * r)))

/-- The caption of key `k`. -/
def caption (k : Nat) : String :=
  match cfg.radii[k]? with
  | some (r, t) =>
    let disk := if diskLeftOfCut r then " The circle |v| = r/2 lies left of the dashed edge: no \
        v meets the hypothesis of the lemma."
      else " The circle |v| = r/2 crosses the dashed edge, and the lens does not."
    if k == 0 then
      s!"The lens of the closed disks |v| ≤ r/2 and |v − u| ≤ r/2 at r = {t}, with the \
        half-planes Re v ≥ κ − η (dashed edge) and Re v ≥ κ, η = (3 + φ − r²)/16, and v∗ on \
        Re v = κ. The second panel shows the tip enlarged, and above it the margin η between \
        the edges as a bar. The tip lies left of the dashed edge, at least η from it." ++ disk
    else
      s!"r = {t}: the margin η is smaller, and the tip has moved right; it stays at least η \
        left of the dashed edge." ++ disk
  | none =>
    if k == cfg.radii.size then
      "r = R = √(3 + φ): η = 0, so the dashed edge has reached Re v = κ, and so has the tip: \
        the tip is v∗."
    else
      "At R the two half-planes are one, Re v ≥ κ, and the tip of the lens is v∗, on its \
        edge. Below R it stays at least η left of the dashed edge."

/-- The loop: the lens beside the neighbourhood of its tip, enlarged, on one clock, each panel at
its own scale, stacked at the narrow width; its poster is the last key. -/
def motion : MotionPanels :=
  let n := cfg.keyCount
  let main : Motion :=
    { keys := ((List.range n).map cfg.key).toArray,
      steps := ((List.range (n - 1)).map fun j =>
        ({ moves := cfg.movesOf cfg.key j } : MotionStep)).toArray,
      between := cfg.between, morphSamples := cfg.samples }
  let zoomed : Motion :=
    { keys := ((List.range n).map cfg.zoomKey).toArray,
      steps := ((List.range (n - 1)).map fun j =>
        ({ moves := cfg.movesOf cfg.zoomKey j } : MotionStep)).toArray,
      between := cfg.zoomBetween, morphSamples := cfg.samples }
  { panels := #[{ title := "The lens", motion := main },
      { title := "Near the tip", motion := zoomed }]
    captions := ((List.range n).map cfg.caption).toArray
    pacing := { motionPacing with hold := cfg.hold, lastHold := 3 }
    timing := ((List.range (n - 1)).map fun j =>
      (if cfg.grows j then { duration := some cfg.stepTime, easing := some .linear }
        else { duration := some motionPacing.fade, easing := some .linear } : PanelTiming)).toArray
    info := { title := "The lens and its tip as r grows to R"
              description := s!"The lens of the closed disks |v| ≤ r/2 about 0 and \
                |v − u| ≤ r/2 about u = ζ, with the half-planes Re v ≥ κ − η (dashed edge) and \
                Re v ≥ κ, and in a second panel the neighbourhood of its tip enlarged, with the \
                margin η between the edges; at \
                r = {", ".intercalate (cfg.radii.map (·.2)).toList} and R = √(3 + φ). Between two \
                radii the picture passes through the exact pictures at radii between, and the \
                browser interpolates between those. As r grows the \
                margin narrows and the tip moves right, staying left of the dashed edge; at R, \
                where η = 0, the tip is v∗ on Re v = κ." }
    checks := .fail
    poster := n - 1
    scale := .independent
    width := figureWidth
    narrowWidth := some narrowWidth
    shares := #[mainWidth, zoomWidth] }

end LensLoopConfig

/-- The configuration of the figure: the defaults. -/
def lensConfig : LensLoopConfig := {}

/-- The lens of the disks of radius r/2 about 0 and u = ζ and the half-planes Re v ≥ κ − η and
Re v ≥ κ as r grows through 1.8, 2, 2.08 and 2.12 to R, beside the neighbourhood of the tip
enlarged: the tip moves right and stays left of Re v = κ − η, and reaches the line Re v = κ
exactly at R, where η = 0 and the tip is v∗. -/
@[figure]
def lensRadius : MotionPanels := lensConfig.motion

end TDCSGFigures.Lens
