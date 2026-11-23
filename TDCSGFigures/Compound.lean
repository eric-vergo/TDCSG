/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.Early
import TDCSGFigures.Style

/-!
# The figures of chapter 1, compound symmetry

* `extensionJump`: a turn of one closed disk `B`, extended by the identity, moves a point just
  inside `B` far from a point just outside it, which stays: the extension is not continuous, so
  the group it generates lives among the permutations of the plane, not its isometries.
* `disjointDisks`: two disjoint closed disks, each turned by its own generator; the two turns move
  disjoint sets of points and commute, and the group is the product of the two cyclic groups.

Every point is exact in `ℤ[ζ₅]`, every radius rational, and every incidence the figures record is
decided exactly in `ℚ(√5)` (`extensionJump_spec`, `disjointDisks_spec`).
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-! ### One disk turned, the identity outside -/

/-- The items of `extensionJump`, in drawing order. -/
def extensionJumpItems : Array Item := #[
  Plane.Exact.disk origin ballRadius |>.noFill |>.role leftRole |>.named "the disk B"
    |>.describedBy "the closed disk of radius 10 about c = 0" |>.declRef `TDCSG.ballPerm,
  Plane.Exact.arc origin (9 : Rat) 0 (-deg 72) |>.withArrow |>.role leftRole |>.width 1.5
    |>.named "the turn of p through 72° clockwise about c"
    |>.declRef `TDCSG.ballPerm_apply_of_mem,
  Plane.Exact.segment origin ballSpoke |>.role leftRole |>.width 1.5 |>.dashed
    |>.named "a radius of B, length 10",
  Plane.Exact.labelBeside "radius 10" origin ballSpoke |>.role leftRole,
  Plane.Exact.angleMark origin 0 (-deg 72) (some 30) |>.role leftRole
    |>.named "the angle of the turn, 72° clockwise",
  Plane.Exact.segment nearInside nearOutside |>.faint |>.dashed |>.named "p to q, length 2",
  Plane.Exact.segment nearInsideImage nearOutside |>.faint |>.dashed
    |>.named "ĥ(p) to ĥ(q), length about 11.9",
  Plane.label "2" ⟨21 / 2, 0⟩ .above,
  Plane.label "≈ 11.9" ((PlanePoint.toPoint nearInsideImage).lerp
    (PlanePoint.toPoint nearOutside) 0.62) (.toward (deg 136)) (some 4),
  Plane.Exact.point origin |>.role leftRole |>.named "the centre c",
  Plane.Exact.point nearInside |>.role leftRole |>.named "p" |>.incident .inside "the disk B"
    |>.declRef `TDCSG.ballPerm_apply_of_mem,
  Plane.Exact.point nearOutside |>.named "q = ĥ(q)" |>.incident .outside "the disk B"
    |>.declRef `TDCSG.ballPerm_apply_of_notMem,
  Plane.Exact.point nearInsideImage |>.role leftRole |>.named "ĥ(p)"
    |>.incident .inside "the disk B",
  Plane.Exact.label "c" origin .auto |>.role leftRole,
  Plane.Exact.label "p" nearInside .above |>.role leftRole,
  Plane.Exact.label "q, fixed" nearOutside .auto,
  Plane.Exact.label "image of p" nearInsideImage .auto |>.role leftRole,
  Plane.Exact.label "72°" origin (.toward (-deg 36)) (some 42) |>.role leftRole,
  Plane.Exact.label "disk B" ((-6 : Rat), (-5 : Rat)) |>.role leftRole]

/-- A closed disk B of radius 10 about c = 0, turned through 72° clockwise and extended by the
identity: the point p = 9 just inside B moves to ĥ(p) = 9ζ⁴, the point q = 11 just outside stays
where it is. Two points 2 apart end up about 11.9 apart. -/
@[figure]
def extensionJump : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := extensionJumpItems
  info := { title := "A turn of one disk, extended by the identity, is not continuous" }

/-! ### Two disjoint disks -/

/-- The items of `disjointDisks`, in drawing order. -/
def disjointDisksItems : Array Item := #[
  Plane.Exact.disk leftCentre disjointLeft |>.noFill |>.role leftRole |>.named "the disk B₁"
    |>.describedBy "the closed disk of radius 4/5 about −1",
  Plane.Exact.disk rightCentre disjointRight |>.noFill |>.role rightRole |>.named "the disk B₂"
    |>.describedBy "the closed disk of radius 7/10 about 1",
  Plane.Exact.segment ((-1 / 5 : Rat), (0 : Rat)) ((3 / 10 : Rat), (0 : Rat)) |>.faint |>.dashed
    |>.named "the gap between B₁ and B₂, of length 1/2"
    |>.declRef `TDCSG.leftDisk_disjoint_rightDisk,
  Plane.label "gap" ⟨1 / 20, 0⟩ .below,
  Plane.Exact.arc leftCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role leftRole
    |>.width 1.5 |>.named "the turn a of B₁, 72° clockwise about −1" |>.declRef `TDCSG.genA,
  Plane.Exact.arc rightCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role rightRole
    |>.width 1.5 |>.named "the turn b of B₂, 72° clockwise about 1" |>.declRef `TDCSG.genB,
  Plane.Exact.point leftCentre |>.role leftRole |>.named "the centre −1",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the centre 1",
  Plane.Exact.point leftSample |>.role leftRole |>.named "x" |>.incident .inside "the disk B₁"
    |>.incident .outside "the disk B₂",
  Plane.Exact.point (leftCentre + phiInv * zeta 1) |>.role leftRole |>.named "a(x)"
    |>.incident .inside "the disk B₁",
  Plane.Exact.point rightSample |>.role rightRole |>.named "y" |>.incident .inside "the disk B₂"
    |>.incident .outside "the disk B₁",
  Plane.Exact.point (rightCentre + phiInv * zeta 1) |>.role rightRole |>.named "b(y)"
    |>.incident .inside "the disk B₂",
  Plane.Exact.label "−1" leftCentre .below |>.role leftRole,
  Plane.Exact.label "+1" rightCentre .below |>.role rightRole,
  Plane.Exact.label "x" leftSample .auto |>.role leftRole,
  Plane.Exact.label "a(x)" (leftCentre + phiInv * zeta 1) .auto |>.role leftRole,
  Plane.Exact.label "y" rightSample .auto |>.role rightRole,
  Plane.Exact.label "b(y)" (rightCentre + phiInv * zeta 1) .auto |>.role rightRole,
  Plane.Exact.label "B₁, radius 4/5" ((-1 : Rat), (-1 : Rat)) |>.role leftRole
    |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two,
  Plane.Exact.label "B₂, radius 7/10" ((1 : Rat), (-1 : Rat)) |>.role rightRole
    |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two]

/-- Two disjoint closed disks, B₁ of radius 4/5 about −1 and B₂ of radius 7/10 about 1, each
turned through 72° clockwise by its own generator: a turns x in B₁ and fixes everything outside
B₁, b turns y in B₂ and fixes everything outside B₂. -/
@[figure]
def disjointDisks : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := disjointDisksItems
  info := { title := "Two disjoint disks, each turned by its own generator" }


/-! ### What the figures state -/

/-- What `extensionJump` draws, item for item, and why its records are right. The data are the
disk `B` of radius `10` about `c = 0`, the points `p = 9` and `q = 11`, the image
`ĥ(p) = 9ζ⁴` of `p` under the turn through `72°` clockwise (multiplication by
`ζ⁴ = e^{-2πi/5}`), and the end `10ζ²` of the drawn radius. The items are written out in drawing
order, each with its colour, title, width, dashes, link and recorded incidences. The facts hold
exactly in `ℚ(√5)`: `|p|² = 81 < 100 < 121 = |q|²` (`p` inside `B`, `q` outside, so the extension
turns `p` and fixes `q`), `|ĥ(p)|² = 81`, `|p - q|² = 4`, `|ĥ(p) - ĥ(q)|² = |9ζ⁴ - 11|² =
301 - 99φ > 100`, and `|10ζ²|² = 100`. Not stated: how the builders and modifiers draw, the layout,
the lettering, the style's colour values and the pixels. -/
theorem extensionJump_spec :
    ballRadius = 10 ∧ nearInside = Zeta5.ofInt 9 ∧ nearOutside = Zeta5.ofInt 11 ∧
    nearInsideImage = nearInside * Zeta5.pow 4 ∧ ballSpoke = Zeta5.ofInt 10 * Zeta5.pow 2 ∧
    origin = Zeta5.zero ∧
    extensionJump.items = #[
      Plane.Exact.disk origin ballRadius |>.noFill |>.role leftRole |>.named "the disk B"
        |>.describedBy "the closed disk of radius 10 about c = 0" |>.declRef `TDCSG.ballPerm,
      Plane.Exact.arc origin (9 : Rat) 0 (-deg 72) |>.withArrow |>.role leftRole |>.width 1.5
        |>.named "the turn of p through 72° clockwise about c"
        |>.declRef `TDCSG.ballPerm_apply_of_mem,
      Plane.Exact.segment origin ballSpoke |>.role leftRole |>.width 1.5 |>.dashed
        |>.named "a radius of B, length 10",
      Plane.Exact.labelBeside "radius 10" origin ballSpoke |>.role leftRole,
      Plane.Exact.angleMark origin 0 (-deg 72) (some 30) |>.role leftRole
        |>.named "the angle of the turn, 72° clockwise",
      Plane.Exact.segment nearInside nearOutside |>.faint |>.dashed |>.named "p to q, length 2",
      Plane.Exact.segment nearInsideImage nearOutside |>.faint |>.dashed
        |>.named "ĥ(p) to ĥ(q), length about 11.9",
      Plane.label "2" ⟨21 / 2, 0⟩ .above,
      Plane.label "≈ 11.9" ((PlanePoint.toPoint nearInsideImage).lerp
        (PlanePoint.toPoint nearOutside) 0.62) (.toward (deg 136)) (some 4),
      Plane.Exact.point origin |>.role leftRole |>.named "the centre c",
      Plane.Exact.point nearInside |>.role leftRole |>.named "p" |>.incident .inside "the disk B"
        |>.declRef `TDCSG.ballPerm_apply_of_mem,
      Plane.Exact.point nearOutside |>.named "q = ĥ(q)" |>.incident .outside "the disk B"
        |>.declRef `TDCSG.ballPerm_apply_of_notMem,
      Plane.Exact.point nearInsideImage |>.role leftRole |>.named "ĥ(p)"
        |>.incident .inside "the disk B",
      Plane.Exact.label "c" origin .auto |>.role leftRole,
      Plane.Exact.label "p" nearInside .above |>.role leftRole,
      Plane.Exact.label "q, fixed" nearOutside .auto,
      Plane.Exact.label "image of p" nearInsideImage .auto |>.role leftRole,
      Plane.Exact.label "72°" origin (.toward (-deg 36)) (some 42) |>.role leftRole,
      Plane.Exact.label "disk B" ((-6 : Rat), (-5 : Rat)) |>.role leftRole] ∧
    QSqrt.lt nearInside.normSq (rat 100) = true ∧ QSqrt.lt (rat 100) nearOutside.normSq = true ∧
    (nearInsideImage.normSq == rat 81) = true ∧
    ((nearInside - nearOutside).normSq == rat 4) = true ∧
    ((nearInsideImage - nearOutside).normSq == rat 301 - phi * rat 99) = true ∧
    QSqrt.lt (rat 100) (nearInsideImage - nearOutside).normSq = true ∧
    (ballSpoke.normSq == rat 100) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves extensionJump extensionJump_spec

/-- What `disjointDisks` draws, item for item, and why its records are right. The data are the
radii `r₁ = 4/5` and `r₂ = 7/10` of the disks `B₁` about `-1` and `B₂` about `1`, the points
`x = -1 + φ⁻¹ ζ²` and `y = 1 + φ⁻¹ ζ²` (`φ⁻¹ = ζ + ζ⁴`), and their images `a(x) = -1 + φ⁻¹ ζ` and
`b(y) = 1 + φ⁻¹ ζ`. The items are written out in drawing order. The facts hold exactly:
`r₁ + r₂ < 2`, so the disks are disjoint and the gap runs from `-1 + r₁ = -1/5` to
`1 - r₂ = 3/10`; `|x + 1|² = |y - 1|² = φ⁻²` with `φ⁻² < r₂² < r₁²`; `x` lies outside `B₂` and `y`
outside `B₁`; `a` turns `x` to `a(x)` and fixes `y`, `b` turns `y` to `b(y)` and fixes `x`; `a(x)`
lies in `B₁` and `b(y)` in `B₂`. Not stated: how the builders and modifiers draw, the layout, the
lettering, the style's colour values and the pixels. -/
theorem disjointDisks_spec :
    disjointLeft = 4 / 5 ∧ disjointRight = 7 / 10 ∧
    leftSample = leftCentre + phiInv * Zeta5.pow 2 ∧
    rightSample = rightCentre + phiInv * Zeta5.pow 2 ∧ phiInvReal = ⟨-1 / 2, 1 / 2⟩ ∧
    disjointDisks.items = #[
      Plane.Exact.disk leftCentre disjointLeft |>.noFill |>.role leftRole |>.named "the disk B₁"
        |>.describedBy "the closed disk of radius 4/5 about −1",
      Plane.Exact.disk rightCentre disjointRight |>.noFill |>.role rightRole |>.named "the disk B₂"
        |>.describedBy "the closed disk of radius 7/10 about 1",
      Plane.Exact.segment ((-1 / 5 : Rat), (0 : Rat)) ((3 / 10 : Rat), (0 : Rat)) |>.faint |>.dashed
        |>.named "the gap between B₁ and B₂, of length 1/2"
        |>.declRef `TDCSG.leftDisk_disjoint_rightDisk,
      Plane.label "gap" ⟨1 / 20, 0⟩ .below,
      Plane.Exact.arc leftCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role leftRole
        |>.width 1.5 |>.named "the turn a of B₁, 72° clockwise about −1" |>.declRef `TDCSG.genA,
      Plane.Exact.arc rightCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role rightRole
        |>.width 1.5 |>.named "the turn b of B₂, 72° clockwise about 1" |>.declRef `TDCSG.genB,
      Plane.Exact.point leftCentre |>.role leftRole |>.named "the centre −1",
      Plane.Exact.point rightCentre |>.role rightRole |>.named "the centre 1",
      Plane.Exact.point leftSample |>.role leftRole |>.named "x" |>.incident .inside "the disk B₁"
        |>.incident .outside "the disk B₂",
      Plane.Exact.point (leftCentre + phiInv * zeta 1) |>.role leftRole |>.named "a(x)"
        |>.incident .inside "the disk B₁",
      Plane.Exact.point rightSample |>.role rightRole |>.named "y" |>.incident .inside "the disk B₂"
        |>.incident .outside "the disk B₁",
      Plane.Exact.point (rightCentre + phiInv * zeta 1) |>.role rightRole |>.named "b(y)"
        |>.incident .inside "the disk B₂",
      Plane.Exact.label "−1" leftCentre .below |>.role leftRole,
      Plane.Exact.label "+1" rightCentre .below |>.role rightRole,
      Plane.Exact.label "x" leftSample .auto |>.role leftRole,
      Plane.Exact.label "a(x)" (leftCentre + phiInv * zeta 1) .auto |>.role leftRole,
      Plane.Exact.label "y" rightSample .auto |>.role rightRole,
      Plane.Exact.label "b(y)" (rightCentre + phiInv * zeta 1) .auto |>.role rightRole,
      Plane.Exact.label "B₁, radius 4/5" ((-1 : Rat), (-1 : Rat)) |>.role leftRole
        |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two,
      Plane.Exact.label "B₂, radius 7/10" ((1 : Rat), (-1 : Rat)) |>.role rightRole
        |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two] ∧
    decide (disjointLeft + disjointRight < 2) = true ∧
    decide ((-1 : Rat) + disjointLeft = -1 / 5 ∧ (1 : Rat) - disjointRight = 3 / 10) = true ∧
    ((leftSample - leftCentre).normSq == phiInvReal * phiInvReal) = true ∧
    ((rightSample - rightCentre).normSq == phiInvReal * phiInvReal) = true ∧
    QSqrt.lt (phiInvReal * phiInvReal) (rat (disjointRight * disjointRight)) = true ∧
    QSqrt.lt (rat (disjointRight * disjointRight)) (leftSample - rightCentre).normSq = true ∧
    QSqrt.lt (rat (disjointLeft * disjointLeft)) (rightSample - leftCentre).normSq = true ∧
    (Letter.a.act (rat (disjointLeft * disjointLeft)) leftSample ==
      leftCentre + phiInv * Zeta5.pow 1) = true ∧
    (Letter.a.act (rat (disjointLeft * disjointLeft)) rightSample == rightSample) = true ∧
    (Letter.b.act (rat (disjointRight * disjointRight)) rightSample ==
      rightCentre + phiInv * Zeta5.pow 1) = true ∧
    (Letter.b.act (rat (disjointRight * disjointRight)) leftSample == leftSample) = true ∧
    QSqrt.lt ((leftCentre + phiInv * Zeta5.pow 1) - leftCentre).normSq
      (rat (disjointLeft * disjointLeft)) = true ∧
    QSqrt.lt ((rightCentre + phiInv * Zeta5.pow 1) - rightCentre).normSq
      (rat (disjointRight * disjointRight)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves disjointDisks disjointDisks_spec

end TDCSGFigures
