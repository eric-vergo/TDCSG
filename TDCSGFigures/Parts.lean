/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.Early
import TDCSGFigures.Style

/-!
# The figures of the part dividers: the radius line

`radiusLineInfinite` (Part I) and `radiusLineFinite` (Part II) draw the same line of radii `r`
with the critical radius `R = √(3 + φ)` marked: above it the radii at which `GG₅(r)` is finite, the
half-line `r < R`, ending in an open ring at `R`; below it the radii at which it is infinite, the
closed half-line `r ≥ R`, starting with a filled dot at `R`. Each part's variant draws its own half
thick and the other thin. `R` lies exactly between `2` and `3` (`4 < 3 + φ < 9`,
`radiusLineInfinite_spec`, `radiusLineFinite_spec`).
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- The height of the finite half above the axis. -/
def finiteRow : Rat := 3 / 4

/-- The height of the infinite half above the axis. -/
def infiniteRow : Rat := 1 / 4

/-- A tick of the axis at `x`. -/
def axisTick (x : AxisValue) : Item :=
  Plane.Exact.tickAt (axisAt x 0) (axisAt (.rat 0) 0) (axisAt (.rat 1) 0)

/-- The items of the radius line; `infiniteFirst` draws the infinite half thick (Part I), otherwise
the finite half (Part II). -/
def radiusLineItems (infiniteFirst : Bool) : Array Item :=
  let thick := fun (b : Bool) => if b then (6 : Float) else 2.5
  #[Plane.Exact.segment (axisAt (.rat (-1 / 2)) 0) (axisAt (.rat (33 / 10)) 0) |>.withArrow
      |>.named "the axis of the radius r",
    Plane.Exact.segment (axisAt axisR finiteRow) (axisAt (.rat (-1 / 2)) finiteRow) |>.withArrow
      |>.role finiteRole |>.width (thick !infiniteFirst)
      |>.named "the radii r < R, at which GG₅(r) is finite"
      |>.declRef (if infiniteFirst then `TDCSG.CriticalRadius.finite_GG_five_iff
        else `TDCSG.Five.finite_GG_of_lt),
    Plane.Exact.segment (axisAt axisR infiniteRow) (axisAt (.rat (33 / 10)) infiniteRow)
      |>.withArrow |>.role infiniteRole |>.width (thick infiniteFirst)
      |>.named "the radii r ≥ R, at which GG₅(r) is infinite"
      |>.declRef (if infiniteFirst then `TDCSG.Five.infinite_GG
        else `TDCSG.CriticalRadius.infinite_GG_five),
    Plane.Exact.point (axisAt axisR finiteRow) |>.marker .ring |>.role finiteRole
      |>.named "R, not a radius of the finite half",
    Plane.Exact.point (axisAt axisR infiniteRow) |>.role infiniteRole
      |>.named "R, a radius of the infinite half",
    axisTick (.rat 0), axisTick (.rat 1), axisTick axisR, axisTick (.rat 3),
    Plane.Exact.label "0" (axisAt (.rat 0) 0) .below,
    Plane.Exact.label "1" (axisAt (.rat 1) 0) .below,
    Plane.Exact.label "R" (axisAt axisR 0) .below
      |>.declRef `TDCSG.CriticalRadius.criticalRadius_five,
    Plane.Exact.label "3" (axisAt (.rat 3) 0) .below,
    Plane.Exact.label "r" (axisAt (.rat (33 / 10)) 0) .right,
    Plane.Exact.label "GG₅(r) finite for r < R" (axisAt (.rat (4 / 5)) finiteRow) .above
      |>.role finiteRole,
    Plane.Exact.label "GG₅(r) infinite for r ≥ R" (axisAt (.rat (11 / 4)) infiniteRow) .above
      |>.role infiniteRole]

/-- The line of radii r with the critical radius R = √(3 + φ): GG₅(r) is finite for r < R (an open
ring at R) and infinite for r ≥ R (a filled dot at R), the infinite half drawn thick. -/
@[figure]
def radiusLineInfinite : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := radiusStyle
  checks := .fail
  items := radiusLineItems true
  info := { title := "Infinite from the critical radius on" }

/-- The line of radii r with the critical radius R = √(3 + φ): GG₅(r) is finite for r < R (an open
ring at R) and infinite for r ≥ R (a filled dot at R), the finite half drawn thick. -/
@[figure]
def radiusLineFinite : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := radiusStyle
  checks := .fail
  items := radiusLineItems false
  info := { title := "Finite below the critical radius" }


/-! ### What the figures state -/

/-- What `radiusLineInfinite` draws: the radius line, item for item, with the critical radius
`R = √(3 + φ)` on it exactly. The data are `R` (`axisR`, the square root of `3 + φ = 7/2 + √5/2`),
the rows of the two halves at heights `3/4` and `1/4`, and the axis ticks (`axisTick x`, a tick
across the axis at `x`). The items are written out in drawing order, each with its colour, width,
title and link: the axis, the finite half `r < R` drawn from the open ring at `R` towards the
negative radii, the infinite half `r ≥ R` from the filled dot at `R` onwards, the ticks and their
labels `0`, `1`, `R`, `3`, and the two names. The facts hold exactly in `ℚ(√5)`:
`4 < 3 + φ < 9`, so `2 < R < 3` and the ticks are in the order drawn. Not stated: how the builders
and modifiers draw, the layout, the lettering, the style's colour values and the pixels. The
infinite half is drawn thick. -/
theorem radiusLineInfinite_spec :
    axisR = .root ⟨⟨7 / 2, 1 / 2⟩⟩ ∧ finiteRow = 3 / 4 ∧ infiniteRow = 1 / 4 ∧
    radiusLineInfinite.items = #[
      Plane.Exact.segment (axisAt (.rat (-1 / 2)) 0) (axisAt (.rat (33 / 10)) 0) |>.withArrow
        |>.named "the axis of the radius r",
      Plane.Exact.segment (axisAt axisR finiteRow) (axisAt (.rat (-1 / 2)) finiteRow) |>.withArrow
        |>.role finiteRole |>.width 2.5
        |>.named "the radii r < R, at which GG₅(r) is finite"
        |>.declRef `TDCSG.CriticalRadius.finite_GG_five_iff,
      Plane.Exact.segment (axisAt axisR infiniteRow) (axisAt (.rat (33 / 10)) infiniteRow)
        |>.withArrow |>.role infiniteRole |>.width 6
        |>.named "the radii r ≥ R, at which GG₅(r) is infinite"
        |>.declRef `TDCSG.Five.infinite_GG,
      Plane.Exact.point (axisAt axisR finiteRow) |>.marker .ring |>.role finiteRole
        |>.named "R, not a radius of the finite half",
      Plane.Exact.point (axisAt axisR infiniteRow) |>.role infiniteRole
        |>.named "R, a radius of the infinite half",
      axisTick (.rat 0), axisTick (.rat 1), axisTick axisR, axisTick (.rat 3),
      Plane.Exact.label "0" (axisAt (.rat 0) 0) .below,
      Plane.Exact.label "1" (axisAt (.rat 1) 0) .below,
      Plane.Exact.label "R" (axisAt axisR 0) .below
        |>.declRef `TDCSG.CriticalRadius.criticalRadius_five,
      Plane.Exact.label "3" (axisAt (.rat 3) 0) .below,
      Plane.Exact.label "r" (axisAt (.rat (33 / 10)) 0) .right,
      Plane.Exact.label "GG₅(r) finite for r < R" (axisAt (.rat (4 / 5)) finiteRow) .above
        |>.role finiteRole,
      Plane.Exact.label "GG₅(r) infinite for r ≥ R" (axisAt (.rat (11 / 4)) infiniteRow) .above
        |>.role infiniteRole] ∧
    QSqrt.lt (rat 4) threePlusPhi = true ∧ QSqrt.lt threePlusPhi (rat 9) = true := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves radiusLineInfinite radiusLineInfinite_spec

/-- What `radiusLineFinite` draws: the radius line, item for item, with the critical radius
`R = √(3 + φ)` on it exactly. The data are `R` (`axisR`, the square root of `3 + φ = 7/2 + √5/2`),
the rows of the two halves at heights `3/4` and `1/4`, and the axis ticks (`axisTick x`, a tick
across the axis at `x`). The items are written out in drawing order, each with its colour, width,
title and link: the axis, the finite half `r < R` drawn from the open ring at `R` towards the
negative radii, the infinite half `r ≥ R` from the filled dot at `R` onwards, the ticks and their
labels `0`, `1`, `R`, `3`, and the two names. The facts hold exactly in `ℚ(√5)`:
`4 < 3 + φ < 9`, so `2 < R < 3` and the ticks are in the order drawn. Not stated: how the builders
and modifiers draw, the layout, the lettering, the style's colour values and the pixels. The
finite half is drawn thick. -/
theorem radiusLineFinite_spec :
    axisR = .root ⟨⟨7 / 2, 1 / 2⟩⟩ ∧ finiteRow = 3 / 4 ∧ infiniteRow = 1 / 4 ∧
    radiusLineFinite.items = #[
      Plane.Exact.segment (axisAt (.rat (-1 / 2)) 0) (axisAt (.rat (33 / 10)) 0) |>.withArrow
        |>.named "the axis of the radius r",
      Plane.Exact.segment (axisAt axisR finiteRow) (axisAt (.rat (-1 / 2)) finiteRow) |>.withArrow
        |>.role finiteRole |>.width 6
        |>.named "the radii r < R, at which GG₅(r) is finite"
        |>.declRef `TDCSG.Five.finite_GG_of_lt,
      Plane.Exact.segment (axisAt axisR infiniteRow) (axisAt (.rat (33 / 10)) infiniteRow)
        |>.withArrow |>.role infiniteRole |>.width 2.5
        |>.named "the radii r ≥ R, at which GG₅(r) is infinite"
        |>.declRef `TDCSG.CriticalRadius.infinite_GG_five,
      Plane.Exact.point (axisAt axisR finiteRow) |>.marker .ring |>.role finiteRole
        |>.named "R, not a radius of the finite half",
      Plane.Exact.point (axisAt axisR infiniteRow) |>.role infiniteRole
        |>.named "R, a radius of the infinite half",
      axisTick (.rat 0), axisTick (.rat 1), axisTick axisR, axisTick (.rat 3),
      Plane.Exact.label "0" (axisAt (.rat 0) 0) .below,
      Plane.Exact.label "1" (axisAt (.rat 1) 0) .below,
      Plane.Exact.label "R" (axisAt axisR 0) .below
        |>.declRef `TDCSG.CriticalRadius.criticalRadius_five,
      Plane.Exact.label "3" (axisAt (.rat 3) 0) .below,
      Plane.Exact.label "r" (axisAt (.rat (33 / 10)) 0) .right,
      Plane.Exact.label "GG₅(r) finite for r < R" (axisAt (.rat (4 / 5)) finiteRow) .above
        |>.role finiteRole,
      Plane.Exact.label "GG₅(r) infinite for r ≥ R" (axisAt (.rat (11 / 4)) infiniteRow) .above
        |>.role infiniteRole] ∧
    QSqrt.lt (rat 4) threePlusPhi = true ∧ QSqrt.lt threePlusPhi (rat 9) = true := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves radiusLineFinite radiusLineFinite_spec

end TDCSGFigures
