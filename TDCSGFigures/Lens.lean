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
`u/2 + h (s, -c)` with `c = Re ζ = (φ - 1)/2`, `s = Im ζ` and `h = √(r²/4 - 1/4)`; at a rational
radius its coordinates are `c/2 + √(h² s²)` and `√(s²/4) - √(h² c²)` (`Surd`s). The point
`v* = (1 + ζ - ζ²)/2 = 1 + t u` (`t = 1/2 - c`) of the proof lies at distance `R/2` from `0` and
from `u` and has real part `κ`.

* `lensEstimate`: the picture at `r = 1.8`, every element labelled.
* `lensRadius`: a slider through `r = 1.8, 2, 2.08, 2.12` and `R = √(3 + φ)`; the tip moves
  towards the cuts and meets both at `R`, where `η = 0` and the tip is `v*`.

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

/-- `c = Re ζ = (φ - 1)/2`. -/
def cosine : QSqrt5 := (zeta 1).realPart

/-- `s² = 1 - c²`, the square of `s = Im ζ = sin 72°`. -/
def sineSq : QSqrt5 := rat 1 - cosine * cosine

/-- `h² = (r/2)² - 1/4` at the half radius `ρ = r/2`. -/
def hSq (ρ : Rat) : QSqrt5 := rat (ρ * ρ - 1 / 4)

/-- The tip of the lens at the half radius `ρ`: `(c/2 + √(h² s²), √(s²/4) - √(h² c²))`. -/
def tip (ρ : Rat) : SurdPoint :=
  ⟨{ base := cosine * rat (1 / 2), roots := [(1, hSq ρ * sineSq)] },
    { roots := [(1, sineSq * rat (1 / 4)), (-1, hSq ρ * (cosine * cosine))] }⟩

/-- `u = ζ` with the coordinates `(c, √(s²))`. -/
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

/-- The decided relations of the tip at the half radius `ρ = r/2`: it lies on both circles
(`|tip|² = |tip - u|² = ρ²`, from the radicands: `c² (h² s²) = 4 (s²/4)(h² c²)` makes the cross
terms cancel, and `c²/4 + h² s² + s²/4 + h² c² = ρ²`), and its real part is less than `κ - η`. -/
def tipFacts (ρ : Rat) : Bool :=
  let A := hSq ρ * sineSq
  let B := sineSq * rat (1 / 4)
  let C := hSq ρ * (cosine * cosine)
  QSqrt.lt ⟨0, 0⟩ cosine && cosine * cosine * A == rat 4 * B * C &&
    cosine * cosine * rat (1 / 4) + A + B + C == rat (ρ * ρ) &&
    sqrtLt A (cut (rat (4 * ρ * ρ)) - cosine * rat (1 / 2))

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

/-- The items of a lens picture: the half-planes `Re v ≥ κ - η` (below `R`) and `Re v ≥ κ`,
outlined (`κ - η` dashed), the real axis, the two disks and their lens, the foot of `u` on the
real axis, the margin `η` between the cuts as a dimension line (when `showMargin`), a radius `r/2`
of `|v| ≤ r/2`, the points `0`, `u`, `c`, the tip and `v*`, and their labels, each beside what it
names. -/
def lensItems {β : Type} [RealValue β] (st : Setting β) : Array Item :=
  let kc := cut st.r2
  let foot : QSqrt5 × QSqrt5 := (cosine, ⟨0, 0⟩)
  (if st.critical then #[] else #[
    Plane.Exact.polygon (halfPlane kc) |>.faint |>.filled |>.width 1 |>.dashed
      |>.fillOpacity 0.16 |>.named "the half-plane Re v ≥ κ − η"
      |>.describedBy s!"where the lens estimate puts no point of the lens, at r = {st.rText}"
      |>.declRef `TDCSG.Five.div_two_lt_norm_sub_of_le_re]) ++ #[
    Plane.Exact.polygon (halfPlane kappa) |>.faint |>.filled |>.width 1 |>.fillOpacity 0.18
      |>.named "the half-plane Re v ≥ κ"
      |>.describedBy "κ = (2φ + 1)/4 = (1 + L)/2, L = φ − 1/2",
    Plane.Exact.line origin rightCentre |>.faint |>.width 1 |>.named "the real axis",
    Plane.Exact.disk origin st.half |>.noFill |>.role windowRole
      |>.named "the circle |v| = r/2" |>.describedBy s!"the closed disk |v| ≤ r/2, r = {st.rText}",
    Plane.Exact.disk (zeta 1) st.half |>.noFill |>.role windowRole |>.dashed
      |>.named "the circle |v − u| = r/2"
      |>.describedBy s!"the closed disk |v − u| ≤ r/2 about u = ζ, r = {st.rText}",
    Plane.Exact.lens origin (zeta 1) st.half st.half |>.role lensRole |>.noOutline
      |>.fillOpacity 0.12 |>.named "the lens",
    Plane.Exact.segment uSurd ⟨Surd.ofQ cosine, Surd.ofQ ⟨0, 0⟩⟩ |>.faint |>.width 1
      |>.dashed #[2, 3] |>.named "the foot of u on the real axis"] ++
  (if st.showMargin then #[
    Plane.Exact.segment (kc, marginY) (kappa, marginY) |>.width 1
      |>.named "the margin η = (3 + φ − r²)/16 between the cuts κ − η and κ"
      |>.declRef `TDCSG.Five.IsGoodLevel,
    Plane.Exact.tickAt (kc, marginY) (kc, marginY) (kappa, marginY),
    Plane.Exact.tickAt (kappa, marginY) (kc, marginY) (kappa, marginY),
    Plane.Exact.labelBeside "η" (kc, marginY) (kappa, marginY)] else #[]) ++ #[
    Plane.segment ⟨0, 0⟩ (radiusEnd (RealValue.toFloat st.half)) |>.role windowRole |>.width 1.5
      |>.dashed |>.named "a radius r/2 of the disk |v| ≤ r/2",
    Plane.labelBeside "r/2" ⟨0, 0⟩ (radiusEnd (RealValue.toFloat st.half)) |>.role windowRole,
    Plane.Exact.point origin |>.role windowRole |>.named "0, the centre of |v| ≤ r/2"
      |>.incident .inside "the circle |v| = r/2"
      |>.incident st.other.incidence "the circle |v − u| = r/2"
      |>.incident (Side.lens .inside st.other).incidence "the lens",
    Plane.Exact.point (zeta 1) |>.role windowRole |>.named "u = ζ, the centre of |v − u| ≤ r/2"
      |>.incident .inside "the circle |v − u| = r/2"
      |>.incident st.other.incidence "the circle |v| = r/2"
      |>.incident (Side.lens .inside st.other).incidence "the lens",
    Plane.Exact.point foot |>.faint |>.size 3
      |>.named "c = Re u = (φ − 1)/2 on the real axis" |>.incident .on "the real axis",
    st.tipPt] ++
  (if st.showVStar then #[
    Plane.Exact.point vStar |>.named "v∗ = 1 + t u, t = 1/2 − c, at distance R/2 from 0 and u"
      |>.incident .outside "the circle |v| = r/2" |>.incident .outside "the circle |v − u| = r/2"
      |>.incident .outside "the lens" |>.incident .on "the half-plane Re v ≥ κ"
      |>.incident .inside "the half-plane Re v ≥ κ − η",
    Plane.Exact.label "v∗" vStar .auto] else #[]) ++ #[
    Plane.Exact.label "0" origin .auto |>.role windowRole,
    Plane.Exact.label "u = ζ" (zeta 1) .auto |>.role windowRole,
    Plane.Exact.label "c" foot .auto,
    Plane.label (if st.critical then "tip = v∗" else "tip") st.tipXY .auto,
    Plane.Exact.label "lens" ((rat (1 / 10), rat (11 / 20)) : QSqrt5 × QSqrt5) |>.role lensRole,
    Plane.Exact.label "|v| ≤ r/2" ((rat (3 / 10), rat (-11 / 20)) : QSqrt5 × QSqrt5)
      |>.role windowRole,
    Plane.Exact.label "|v − u| ≤ r/2" ((rat (9 / 20), rat (3 / 2)) : QSqrt5 × QSqrt5)
      |>.role windowRole,
    Plane.Exact.label (if st.critical then "Re v ≥ κ, η = 0" else "Re v ≥ κ")
      ((kappa, cutLabelY) : QSqrt5 × QSqrt5) .right] ++
  (if st.critical then #[] else #[
    Plane.Exact.label "Re v ≥ κ − η →" ((kc, cutLabelY) : QSqrt5 × QSqrt5) .left])

/-- Where `|u|² = 1` stands against `(r/2)²`. -/
def otherSide (ρ2 : QSqrt5) : Side :=
  if ρ2 == rat 1 then .on else if QSqrt.lt rat1 ρ2 then .inside else .outside
where
  /-- `1`. -/
  rat1 : QSqrt5 := rat 1

/-- The tip at the half radius `ρ`, recording that it lies on both circles and outside both
half-planes (`tipFacts`). -/
def tipItem (ρ : Rat) : Item :=
  Plane.Exact.point (tip ρ) |>.size 5
    |>.named "the tip of the lens: its corner of largest real part"
    |>.incident .on "the circle |v| = r/2" |>.incident .on "the circle |v − u| = r/2"
    |>.incident .on "the lens" |>.incident .outside "the half-plane Re v ≥ κ − η"
    |>.incident .outside "the half-plane Re v ≥ κ"

/-- The tip at `R`, the point `v*`: on both circles, on the lens and on the boundary of the
half-plane `Re v ≥ κ`, where the cut `κ - η` is `κ`. -/
def tipCritical : Item :=
  Plane.Exact.point vStar |>.size 5
    |>.named "the tip of the lens at R: v∗ = 1 + t u, t = 1/2 − c"
    |>.incident .on "the circle |v| = r/2" |>.incident .on "the circle |v − u| = r/2"
    |>.incident .on "the lens" |>.incident .on "the half-plane Re v ≥ κ"

/-- The setting at the rational radius `r = 2ρ`, with `v*` drawn apart from the tip and the
margin `η` drawn as a dimension line when `showVStar` (at `r = 1.8`; from `r = 2` on `v*` is too
near the tip to be seen apart, and `η` is a few pixels wide). -/
def settingAt (ρ : Rat) (rText : String) (showVStar : Bool) : Setting Rat :=
  { half := ρ, r2 := rat (4 * ρ * ρ), rText, tipPt := tipItem ρ,
    tipXY := PlanePoint.toPoint (tip ρ), other := otherSide (rat (ρ * ρ)), critical := false,
    showVStar, showMargin := showVStar }

/-- The setting at `R`. -/
def settingCritical : Setting (SqrtOf QSqrt5) :=
  { half := SqrtOf.mk (criticalSq * rat (1 / 4)), r2 := criticalSq, rText := "R = √(3 + φ)",
    tipPt := tipCritical, tipXY := PlanePoint.toPoint vStar,
    other := otherSide (criticalSq * rat (1 / 4)), critical := true, showVStar := false,
    showMargin := false }

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

/-- The lens picture at `R`. -/
def frameCritical : Plane.Figure := lensFigure settingCritical false

/-- Two closed disks of radius r/2 = 0.9 about 0 and u = ζ, their lens, and the half-planes
Re v ≥ κ − η and Re v ≥ κ: the tip of the lens lies left of both. -/
@[figure]
def lensEstimate : Plane.Figure := frameAt (9 / 10) "1.8" true true

/-- The half radii of the slider below `R`, with their radii as text. -/
def sliderRadii : Array (Rat × String) :=
  #[(9 / 10, "1.8"), (1, "2"), (26 / 25, "2.08"), (53 / 50, "2.12")]

/-- The frames of `lensRadius`. -/
def sliderFrames : Array (String × Plane.Figure) :=
  (sliderRadii.map fun (ρ, t) => (t, frameAt ρ t (ρ == 9 / 10) false)).push ("R", frameCritical)

/-- The lens and the cuts as the radius grows from 1.8 to R: the tip reaches the line Re v = κ
exactly at R, where η = 0. -/
@[figure]
def lensRadius : Explorer := Plane.slider "r" sliderFrames

/-! ### The facts the figures show -/

-- The tip lies on both circles and left of `κ - η` at every radius of the slider below `R`.
#guard sliderRadii.all fun (ρ, _) => tipFacts ρ

-- `v*` lies on both circles of radius `R/2` and has real part `κ`; the other corner
-- `(ζ + ζ² - 1)/2 = ζ² conj v*` of the lens at `R` lies on both circles too.
#guard vStar.normSq == criticalSq * rat (1 / 4) &&
  (vStar - ZetaFrac.ofZeta (zeta 1)).normSq == criticalSq * rat (1 / 4) &&
  vStar.realPart == kappa &&
  (ZetaFrac.mk (zeta 1 + zeta 2 - Zeta5.ofInt 1) 2).normSq == criticalSq * rat (1 / 4)

-- Below `R`, `v*` lies outside both disks of radius `r/2`: `|v*|² = R²/4 > r²/4`.
#guard sliderRadii.all fun (ρ, _) => QSqrt.lt (rat (ρ * ρ)) (criticalSq * rat (1 / 4))

/-- The chapter's sharpness claim, exactly: the tip's real part `c/2 + √(h² s²)` is at most
`κ - 2η`, so strictly below `κ - η` when `η > 0`. -/
def tipReLe (ρ : Rat) : Bool :=
  let A := hSq ρ * sineSq
  let K := kappa - margin (rat (4 * ρ * ρ)) * rat 2 - cosine * rat (1 / 2)
  sqrtLt A K || sqrtEq A K

#guard sliderRadii.all fun (ρ, _) => tipReLe ρ

-- At `R` the bound is an equality: `h² = s²` there, and `c/2 + s² = κ`.
#guard hSq 0 + criticalSq * rat (1 / 4) == sineSq && cosine * rat (1 / 2) + sineSq == kappa

-- The disk `|v| ≤ r/2` stays left of `κ - η` at `r = 1.8, 2, 2.08` and crosses it at `2.12`.
#guard (sliderRadii.map fun (ρ, _) => QSqrt.lt (rat ρ) (cut (rat (4 * ρ * ρ)))) ==
  #[true, true, true, false]

-- `16κ - R² = 7φ + 1`, the constant of the threshold `r² - 8r + 7φ + 1 = 0`.
#guard kappa * rat 16 - criticalSq == phi * rat 7 + rat 1

end TDCSGFigures.Lens
