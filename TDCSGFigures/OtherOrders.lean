/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.Early
import TDCSGFigures.Style

/-!
# The figures of chapter 9, other orders

For each of the orders `n = 8, 10, 12`, the two closed disks about `∓1` at the radius `rₙ` from
which the library proves the group infinite, with the points its proof uses:

* `orderEight`: `r₈ = √(10 - 5√2)`; the critical point `p* = 1 - 2ζ + ζ² - ζ³` (`ζ = e^{2πi/8}`) on
  the left circle and inside the right disk, the vertical chord through it, and the first points
  `q_k = p* + 4i (√2 - 1)^(k+1)` of its orbit.
* `orderTen`: `r₁₀ = √(4 - φ)`; the chord from `-W` to `W = √5 ζ₅²` through `0`, `W` on the left
  circle and `-W` on the right one, cut at `-φ⁻¹ ζ₅²` and `ζ₅²` into the pieces of three words.
* `orderTwelve`: `r₁₂ = √(40 - 22√3)`; the critical point `p* = -2ζ + 4ζ² - 3ζ³`
  (`ζ = e^{2πi/12}`) on the left circle and inside the right disk, the chord through it in the
  direction `V = ζ⁵ + ζ⁶`, and the first point `q₀ = p* + (14 - 8√3) V` of its orbit.

The points are elements of `ℤ[ζₙ]` of the orbit engine (`TDCSGFigures.Early.CycPt`), drawn from
their exact coordinates; every incidence the figures record is decided exactly in `ℚ(√2)`,
`ℚ(√5)` or `ℚ(√3)`, and the engine replays the seed words with exact disk tests
(`orderEight_spec`, `orderTen_spec`, `orderTwelve_spec`).
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-! ### Order 8 -/

/-- The point `p` of `ℤ[ζ₈]` recording where it stands relative to the disks of radius `r₈`. -/
def sides8 (p : CycPt 8) (it : Item) : Item :=
  recordLR (sideQ (centre8 (-1)).coords8 p.coords8 radiusEight.radicand)
    (sideQ (centre8 1).coords8 p.coords8 radiusEight.radicand) it

/-- The items of `orderEight`, in drawing order. -/
def orderEightItems : Array Item := #[
  Plane.Exact.disk (centre8 (-1)) radiusEight |>.noFill |>.role leftRole |>.named "the left circle"
    |>.describedBy "the closed disk of radius r₈ = √(10 − 5√2) about −1"
    |>.declRef `TDCSG.CriticalRadius.criticalRadius_eight_le,
  Plane.Exact.disk (centre8 1) radiusEight |>.noFill |>.role rightRole |>.named "the right circle"
    |>.describedBy "the closed disk of radius r₈ = √(10 − 5√2) about 1"
    |>.declRef `TDCSG.CriticalRadius.criticalRadius_eight_le,
  Plane.Exact.lens (centre8 (-1)) (centre8 1) radiusEight radiusEight |>.role lensRole
    |>.noOutline |>.fillOpacity 0.12 |>.named "the lens",
  Plane.Exact.segment (centre8 (-1)) pStar8 |>.role leftRole |>.width 1.5 |>.dashed
    |>.named "a radius r₈ of the left disk",
  Plane.Exact.labelBeside "r₈" (centre8 (-1)) pStar8 |>.role leftRole,
  Plane.Exact.line pStar8 q8₀ |>.faint |>.dashed
    |>.named "the chord p* + it, vertical through p*",
  Plane.Exact.point (centre8 (-1)) |>.role leftRole |>.named "the centre −1",
  Plane.Exact.point (centre8 1) |>.role rightRole |>.named "the centre 1",
  sides8 pStar8 (Plane.Exact.point pStar8 |>.role leftRole |>.named "p* = 1 − 2ζ + ζ² − ζ³"
    |>.incident .on "the chord p* + it, vertical through p*"
    |>.declRef `TDCSG.CriticalRadius.pStar_eight_mem_sphere),
  sides8 q8₀ (Plane.Exact.point q8₀ |>.named "q₀ = p* + 4(√2 − 1)i"
    |>.incident .on "the chord p* + it, vertical through p*"
    |>.declRef `TDCSG.CriticalRadius.infinite_orbit_pStar_eight),
  sides8 q8₁ (Plane.Exact.point q8₁ |>.named "q₁ = p* + 4(√2 − 1)²i"
    |>.incident .on "the chord p* + it, vertical through p*"
    |>.declRef `TDCSG.CriticalRadius.infinite_orbit_pStar_eight),
  Plane.Exact.label "−1" (centre8 (-1)) .auto |>.role leftRole,
  Plane.Exact.label "+1" (centre8 1) .auto |>.role rightRole,
  Plane.Exact.label "p*" pStar8 .right |>.role leftRole,
  Plane.Exact.label "q₀" q8₀ .auto,
  Plane.Exact.label "q₁" q8₁ .auto,
  Plane.label "chord" ⟨(PlanePoint.toPoint pStar8).x, -37 / 20⟩ .right,
  Plane.Exact.label "left disk" ((-19 / 10 : Rat), (3 / 5 : Rat)) |>.role leftRole,
  Plane.Exact.label "right disk" ((19 / 10 : Rat), (3 / 5 : Rat)) |>.role rightRole]

/-- Order 8: the closed disks of radius r₈ = √(10 − 5√2) about −1 and 1, the critical point
p* = 1 − 2ζ + ζ² − ζ³ (ζ = e^{2πi/8}) on the left circle and inside the right disk, the vertical
chord through p*, and the first two points q₀, q₁ of the orbit of p* on it. -/
@[figure]
def orderEight : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := orderEightItems
  info := { title := "Order 8: the critical point and its orbit on the chord" }

/-! ### Order 10 -/

/-- The point `p` of `ℤ[ζ₁₀]` recording where it stands relative to the disks of radius `r₁₀`. -/
def sides10 (p : CycPt 10) (it : Item) : Item :=
  recordLR (exactSide leftCentre fourMinusPhi p.toZeta5)
    (exactSide rightCentre fourMinusPhi p.toZeta5) it

/-- The words of order 10 written out. -/
def wordTextTen (i : Nat) : String :=
  " ".intercalate ((wordsTen.getD (i - 1) []).map Letter.text)

/-- The items of `orderTen`, in drawing order. -/
def orderTenItems : Array Item := #[
  Plane.Exact.disk (centre10 (-1)) radiusTen |>.noFill |>.role leftRole
    |>.named "the left circle" |>.describedBy "the closed disk of radius r₁₀ = √(4 − φ) about −1"
    |>.declRef `TDCSG.CriticalRadius.criticalRadius_ten_le,
  Plane.Exact.disk (centre10 1) radiusTen |>.noFill |>.role rightRole
    |>.named "the right circle" |>.describedBy "the closed disk of radius r₁₀ = √(4 − φ) about 1"
    |>.declRef `TDCSG.CriticalRadius.criticalRadius_ten_le,
  Plane.Exact.lens (centre10 (-1)) (centre10 1) radiusTen radiusTen |>.role lensRole
    |>.noOutline |>.fillOpacity 0.12 |>.named "the lens",
  Plane.Exact.segment negW10 cut10₁ |>.role (pieceRole 1) |>.width 5
    |>.named "the piece [−W, −φ⁻¹u] of word 1",
  Plane.Exact.labelBeside "1" negW10 cut10₁ |>.role (pieceRole 1),
  Plane.Exact.segment cut10₁ cut10₂ |>.role (pieceRole 2) |>.width 5
    |>.named "the piece [−φ⁻¹u, u] of word 2",
  Plane.Exact.labelBeside "2" cut10₁ cut10₂ |>.role (pieceRole 2),
  Plane.Exact.segment cut10₂ w10 |>.role (pieceRole 3) |>.width 5
    |>.named "the piece [u, W] of word 3",
  Plane.Exact.labelBeside "3" cut10₂ w10 |>.role (pieceRole 3),
  Plane.Exact.point (centre10 (-1)) |>.role leftRole |>.named "the centre −1",
  Plane.Exact.point (centre10 1) |>.role rightRole |>.named "the centre 1",
  sides10 w10 (Plane.Exact.point w10 |>.role leftRole
    |>.named "W = √5 u"),
  sides10 negW10 (Plane.Exact.point negW10 |>.role rightRole
    |>.named "−W"),
  sides10 zero10 (Plane.Exact.point zero10 |>.named "0"
    |>.incident .on "the piece [−φ⁻¹u, u] of word 2"
    |>.declRef `TDCSG.CriticalRadius.infinite_orbit_zero_ten),
  sides10 cut10₁ (Plane.Exact.point cut10₁ |>.named "−φ⁻¹u"),
  sides10 cut10₂ (Plane.Exact.point cut10₂ |>.named "u = ζ²"),
  Plane.Exact.label "−1" (centre10 (-1)) .auto |>.role leftRole,
  Plane.Exact.label "+1" (centre10 1) .auto |>.role rightRole,
  Plane.Exact.label "W" w10 .auto |>.role leftRole,
  Plane.Exact.label "−W" negW10 .auto |>.role rightRole,
  Plane.Exact.label "0" zero10 .auto,
  Plane.Exact.label "−φ⁻¹u" cut10₁ .auto,
  Plane.Exact.label "u" cut10₂ .auto,
  Plane.Exact.label "left disk" ((-8 / 5 : Rat), (-3 / 5 : Rat)) |>.role leftRole,
  Plane.Exact.label "right disk" ((8 / 5 : Rat), (3 / 5 : Rat)) |>.role rightRole,
  Plane.Exact.label s!"word 1: {wordTextTen 1}" ((0 : Rat), (-19 / 10 : Rat))
    |>.role (pieceRole 1),
  Plane.Exact.label s!"word 2: {wordTextTen 2}" ((0 : Rat), (-11 / 5 : Rat))
    |>.role (pieceRole 2),
  Plane.Exact.label s!"word 3: {wordTextTen 3}" ((0 : Rat), (-5 / 2 : Rat))
    |>.role (pieceRole 3)]

/-- Order 10: the closed disks of radius r₁₀ = √(4 − φ) about −1 and 1 and the chord from −W to
W = √5 u (u = ζ₅²) through 0, W on the left circle and −W on the right circle, cut at −φ⁻¹u and u
into the pieces of three words. -/
@[figure]
def orderTen : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := orderTenItems
  info := { title := "Order 10: the chord through 0 and its three words" }

/-! ### Order 12 -/

/-- The point `p` of `ℤ[ζ₁₂]` recording where it stands relative to the disks of radius `r₁₂`. -/
def sides12 (p : CycPt 12) (it : Item) : Item :=
  recordLR (sideQ (centre12 (-1)).coords12 p.coords12 radiusTwelve.radicand)
    (sideQ (centre12 1).coords12 p.coords12 radiusTwelve.radicand) it

/-- The items of `orderTwelve`, in drawing order. -/
def orderTwelveItems : Array Item := #[
  Plane.Exact.disk (centre12 (-1)) radiusTwelve |>.noFill |>.role leftRole
    |>.named "the left circle"
    |>.describedBy "the closed disk of radius r₁₂ = √(40 − 22√3) about −1"
    |>.declRef `TDCSG.CriticalRadius.criticalRadius_twelve_le,
  Plane.Exact.disk (centre12 1) radiusTwelve |>.noFill |>.role rightRole
    |>.named "the right circle"
    |>.describedBy "the closed disk of radius r₁₂ = √(40 − 22√3) about 1"
    |>.declRef `TDCSG.CriticalRadius.criticalRadius_twelve_le,
  Plane.Exact.lens (centre12 (-1)) (centre12 1) radiusTwelve radiusTwelve |>.role lensRole
    |>.noOutline |>.fillOpacity 0.12 |>.named "the lens",
  Plane.Exact.segment (centre12 (-1)) pStar12Conj |>.role leftRole |>.width 1.5 |>.dashed
    |>.named "a radius r₁₂ of the left disk",
  Plane.Exact.labelBeside "r₁₂" (centre12 (-1)) pStar12Conj |>.role leftRole,
  Plane.Exact.line pStar12 orbit12 |>.faint |>.dashed
    |>.named "the chord p* + uV, in the direction V = ζ⁵ + ζ⁶",
  Plane.Exact.point (centre12 (-1)) |>.role leftRole |>.named "the centre −1",
  Plane.Exact.point (centre12 1) |>.role rightRole |>.named "the centre 1",
  sides12 pStar12 (Plane.Exact.point pStar12 |>.role leftRole |>.size 3
    |>.named "p* = −2ζ + 4ζ² − 3ζ³"
    |>.incident .on "the chord p* + uV, in the direction V = ζ⁵ + ζ⁶"
    |>.declRef `TDCSG.CriticalRadius.pStar_twelve_mem_sphere),
  sides12 orbit12 (Plane.Exact.point orbit12 |>.size 3 |>.named "q₀ = p* + (14 − 8√3)V"
    |>.incident .on "the chord p* + uV, in the direction V = ζ⁵ + ζ⁶"
    |>.declRef `TDCSG.CriticalRadius.infinite_orbit_pStar_twelve),
  Plane.Exact.label "−1" (centre12 (-1)) .auto |>.role leftRole,
  Plane.Exact.label "+1" (centre12 1) .auto |>.role rightRole,
  Plane.Exact.label "p*" pStar12 .auto |>.role leftRole,
  Plane.Exact.label "q₀" orbit12 .auto,
  Plane.label "chord" ((PlanePoint.toPoint pStar12).lerp (PlanePoint.toPoint orbit12) (-3.5))
    .below,
  Plane.Exact.label "left disk" ((-8 / 5 : Rat), (-3 / 10 : Rat)) |>.role leftRole,
  Plane.Exact.label "right disk" ((8 / 5 : Rat), (3 / 10 : Rat)) |>.role rightRole]

/-- Order 12: the closed disks of radius r₁₂ = √(40 − 22√3) about −1 and 1, the critical point
p* = −2ζ + 4ζ² − 3ζ³ (ζ = e^{2πi/12}) on the left circle and inside the right disk, the chord
through p* in the direction V = ζ⁵ + ζ⁶, and the first point q₀ of the orbit of p* on it. -/
@[figure]
def orderTwelve : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := orderTwelveItems
  info := { title := "Order 12: the critical point and its orbit on the chord" }


/-! ### What the figures state -/

/-- What `orderEight` draws, item for item, and why its records are right. The data are
`p* = 1 - 2ζ + ζ² - ζ³`, `q₀ = 1 + 2ζ - 3ζ² + 3ζ³` and `q₁ = 1 - 10ζ + 13ζ² - 9ζ³` in `ℤ[ζ₈]`, drawn
at their coordinates in `ℚ(√2)` (`ζ₈ = (√2/2, √2/2)`), the centres `∓1` and the radius
`r₈ = √(10 - 5√2)`. The items are written out in drawing order; `sides8` records where a point
stands relative to the two disks and the lens, decided by `sideQ`. The facts hold exactly in
`ℚ(√2)`: `p* = (1 - √2/2, 1 - 3√2/2)` with `|p* + 1|² = 10 - 5√2` (on the left circle) and
`|p* - 1|² = 6 - 3√2 < 10 - 5√2` (inside the right disk); `q₀ = p* + 4(√2 - 1) i` and
`q₁ = p* + 4(√2 - 1)² i`, on the vertical chord through `p*`, inside both disks; every recorded
incidence is the one `sideQ` decides. That `q₀` is the image of `p*` under the seed word
`b b a b`, every disk test holding, is replayed by the orbit engine in `TDCSGFigures.Data.Early`.
Not stated: how the builders and modifiers draw, the layout, the lettering, the style's colour
values and the pixels. -/
theorem orderEight_spec :
    pStar8 = ⟨#[1, -2, 1, -1]⟩ ∧ q8₀ = ⟨#[1, 2, -3, 3]⟩ ∧ q8₁ = ⟨#[1, -10, 13, -9]⟩ ∧
    radiusEight = ⟨⟨10, -5⟩⟩ ∧ (∀ k : Int, centre8 k = ⟨#[k, 0, 0, 0]⟩) ∧
    orderEight.items = #[
      Plane.Exact.disk (centre8 (-1)) radiusEight |>.noFill |>.role leftRole
        |>.named "the left circle"
        |>.describedBy "the closed disk of radius r₈ = √(10 − 5√2) about −1"
        |>.declRef `TDCSG.CriticalRadius.criticalRadius_eight_le,
      Plane.Exact.disk (centre8 1) radiusEight |>.noFill |>.role rightRole
        |>.named "the right circle"
        |>.describedBy "the closed disk of radius r₈ = √(10 − 5√2) about 1"
        |>.declRef `TDCSG.CriticalRadius.criticalRadius_eight_le,
      Plane.Exact.lens (centre8 (-1)) (centre8 1) radiusEight radiusEight |>.role lensRole
        |>.noOutline |>.fillOpacity 0.12 |>.named "the lens",
      Plane.Exact.segment (centre8 (-1)) pStar8 |>.role leftRole |>.width 1.5 |>.dashed
        |>.named "a radius r₈ of the left disk",
      Plane.Exact.labelBeside "r₈" (centre8 (-1)) pStar8 |>.role leftRole,
      Plane.Exact.line pStar8 q8₀ |>.faint |>.dashed
        |>.named "the chord p* + it, vertical through p*",
      Plane.Exact.point (centre8 (-1)) |>.role leftRole |>.named "the centre −1",
      Plane.Exact.point (centre8 1) |>.role rightRole |>.named "the centre 1",
      sides8 pStar8 (Plane.Exact.point pStar8 |>.role leftRole |>.named "p* = 1 − 2ζ + ζ² − ζ³"
        |>.incident .on "the chord p* + it, vertical through p*"
        |>.declRef `TDCSG.CriticalRadius.pStar_eight_mem_sphere),
      sides8 q8₀ (Plane.Exact.point q8₀ |>.named "q₀ = p* + 4(√2 − 1)i"
        |>.incident .on "the chord p* + it, vertical through p*"
        |>.declRef `TDCSG.CriticalRadius.infinite_orbit_pStar_eight),
      sides8 q8₁ (Plane.Exact.point q8₁ |>.named "q₁ = p* + 4(√2 − 1)²i"
        |>.incident .on "the chord p* + it, vertical through p*"
        |>.declRef `TDCSG.CriticalRadius.infinite_orbit_pStar_eight),
      Plane.Exact.label "−1" (centre8 (-1)) .auto |>.role leftRole,
      Plane.Exact.label "+1" (centre8 1) .auto |>.role rightRole,
      Plane.Exact.label "p*" pStar8 .right |>.role leftRole,
      Plane.Exact.label "q₀" q8₀ .auto,
      Plane.Exact.label "q₁" q8₁ .auto,
      Plane.label "chord" ⟨(PlanePoint.toPoint pStar8).x, -37 / 20⟩ .right,
      Plane.Exact.label "left disk" ((-19 / 10 : Rat), (3 / 5 : Rat)) |>.role leftRole,
      Plane.Exact.label "right disk" ((19 / 10 : Rat), (3 / 5 : Rat)) |>.role rightRole] ∧
    (pStar8.coords8 == (⟨1, -1 / 2⟩, ⟨1, -3 / 2⟩)) = true ∧
    (q8₀.coords8 == (⟨1, -1 / 2⟩, ⟨-3, 5 / 2⟩)) = true ∧
    (q8₁.coords8 == (⟨1, -1 / 2⟩, ⟨13, -19 / 2⟩)) = true ∧
    ((centre8 (-1)).coords8 == (⟨-1, 0⟩, ⟨0, 0⟩)) = true ∧
    ((centre8 1).coords8 == (⟨1, 0⟩, ⟨0, 0⟩)) = true ∧
    (distSq pStar8.coords8 (centre8 (-1)).coords8 == ⟨10, -5⟩) = true ∧
    (distSq pStar8.coords8 (centre8 1).coords8 == ⟨6, -3⟩) = true ∧
    (sideQ (centre8 (-1)).coords8 pStar8.coords8 radiusEight.radicand == .on) = true ∧
    (sideQ (centre8 1).coords8 pStar8.coords8 radiusEight.radicand == .inside) = true ∧
    (sideQ (centre8 (-1)).coords8 q8₀.coords8 radiusEight.radicand == .inside) = true ∧
    (sideQ (centre8 1).coords8 q8₀.coords8 radiusEight.radicand == .inside) = true ∧
    (sideQ (centre8 (-1)).coords8 q8₁.coords8 radiusEight.radicand == .inside) = true ∧
    (sideQ (centre8 1).coords8 q8₁.coords8 radiusEight.radicand == .inside) = true := by
  refine ⟨rfl, rfl, rfl, rfl, fun _ => rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves orderEight orderEight_spec

/-- What `orderTen` draws, item for item, and why its records are right. The data are the points
`W`, `-W`, the cuts `-φ⁻¹u` and `u` and `0` in `ℤ[ζ₁₀]`, drawn as the elements of `ℤ[ζ₅]` they are
(`ζ₁₀ = -ζ₅³`), the centres `∓1`, the radius `r₁₀ = √(4 - φ)` and the three words. The items are
written out in drawing order; `sides10` records where a point stands relative to the two disks and
the lens, decided by `exactSide`. The facts hold exactly in `ℚ(√5)`: the drawn points are
`W = √5 u = (1 + 2φ⁻¹) u` (`u = ζ₅²`, `|W|² = 5`), `-W`, `-φ⁻¹u`, `u` and `0`;
`|W + 1|² = |-W - 1|² = 4 - φ` (on the left and the right circle) and `|W - 1|² > 4 - φ`; the cut
`-φ⁻¹u` lies on the left circle as well (`|-φ⁻¹u + 1|² = 4 - φ`); `0` lies between the cuts; the
words are those of `TDCSG.Ten.word₁`, `word₂`, `word₃`. That each word carries its piece onto the
chord, every disk test holding, is replayed by the orbit engine in `TDCSGFigures.Data.Early`. Not
stated: how the builders and modifiers draw, the layout, the lettering, the style's colour values
and the pixels. -/
theorem orderTen_spec :
    w10 = ⟨#[-1, -1, 1, 1]⟩ ∧ negW10 = ⟨#[1, 1, -1, -1]⟩ ∧ cut10₁ = ⟨#[0, 1, -1, 0]⟩ ∧
    cut10₂ = ⟨#[-1, 1, -1, 1]⟩ ∧ zero10 = ⟨#[0, 0, 0, 0]⟩ ∧ radiusTen = ⟨⟨7 / 2, -1 / 2⟩⟩ ∧
    (∀ k : Int, centre10 k = ⟨#[k, 0, 0, 0]⟩) ∧
    wordsTen = [[.b, .b, .aInv, .bInv], [.a, .b, .aInv, .aInv], [.a, .a, .a, .bInv, .bInv, .bInv]] ∧
    orderTenItems = #[
      Plane.Exact.disk (centre10 (-1)) radiusTen |>.noFill |>.role leftRole
        |>.named "the left circle"
        |>.describedBy "the closed disk of radius r₁₀ = √(4 − φ) about −1"
        |>.declRef `TDCSG.CriticalRadius.criticalRadius_ten_le,
      Plane.Exact.disk (centre10 1) radiusTen |>.noFill |>.role rightRole
        |>.named "the right circle"
        |>.describedBy "the closed disk of radius r₁₀ = √(4 − φ) about 1"
        |>.declRef `TDCSG.CriticalRadius.criticalRadius_ten_le,
      Plane.Exact.lens (centre10 (-1)) (centre10 1) radiusTen radiusTen |>.role lensRole
        |>.noOutline |>.fillOpacity 0.12 |>.named "the lens",
      Plane.Exact.segment negW10 cut10₁ |>.role (pieceRole 1) |>.width 5
        |>.named "the piece [−W, −φ⁻¹u] of word 1",
      Plane.Exact.labelBeside "1" negW10 cut10₁ |>.role (pieceRole 1),
      Plane.Exact.segment cut10₁ cut10₂ |>.role (pieceRole 2) |>.width 5
        |>.named "the piece [−φ⁻¹u, u] of word 2",
      Plane.Exact.labelBeside "2" cut10₁ cut10₂ |>.role (pieceRole 2),
      Plane.Exact.segment cut10₂ w10 |>.role (pieceRole 3) |>.width 5
        |>.named "the piece [u, W] of word 3",
      Plane.Exact.labelBeside "3" cut10₂ w10 |>.role (pieceRole 3),
      Plane.Exact.point (centre10 (-1)) |>.role leftRole |>.named "the centre −1",
      Plane.Exact.point (centre10 1) |>.role rightRole |>.named "the centre 1",
      sides10 w10 (Plane.Exact.point w10 |>.role leftRole
        |>.named "W = √5 u"),
      sides10 negW10 (Plane.Exact.point negW10 |>.role rightRole
        |>.named "−W"),
      sides10 zero10 (Plane.Exact.point zero10 |>.named "0"
        |>.incident .on "the piece [−φ⁻¹u, u] of word 2"
        |>.declRef `TDCSG.CriticalRadius.infinite_orbit_zero_ten),
      sides10 cut10₁ (Plane.Exact.point cut10₁ |>.named "−φ⁻¹u"),
      sides10 cut10₂ (Plane.Exact.point cut10₂ |>.named "u = ζ²"),
      Plane.Exact.label "−1" (centre10 (-1)) .auto |>.role leftRole,
      Plane.Exact.label "+1" (centre10 1) .auto |>.role rightRole,
      Plane.Exact.label "W" w10 .auto |>.role leftRole,
      Plane.Exact.label "−W" negW10 .auto |>.role rightRole,
      Plane.Exact.label "0" zero10 .auto,
      Plane.Exact.label "−φ⁻¹u" cut10₁ .auto,
      Plane.Exact.label "u" cut10₂ .auto,
      Plane.Exact.label "left disk" ((-8 / 5 : Rat), (-3 / 5 : Rat)) |>.role leftRole,
      Plane.Exact.label "right disk" ((8 / 5 : Rat), (3 / 5 : Rat)) |>.role rightRole,
      Plane.Exact.label s!"word 1: {wordTextTen 1}" ((0 : Rat), (-19 / 10 : Rat))
        |>.role (pieceRole 1),
      Plane.Exact.label s!"word 2: {wordTextTen 2}" ((0 : Rat), (-11 / 5 : Rat))
        |>.role (pieceRole 2),
      Plane.Exact.label s!"word 3: {wordTextTen 3}" ((0 : Rat), (-5 / 2 : Rat))
        |>.role (pieceRole 3)] ∧
    orderTen.items = orderTenItems ∧
    (w10.toZeta5 == (Zeta5.ofInt 1 + phiInv + phiInv) * Zeta5.pow 2) = true ∧
    ((w10.toZeta5 * w10.toZeta5.conj) == Zeta5.ofInt 5) = true ∧
    (negW10.toZeta5 == -w10.toZeta5) = true ∧
    (cut10₁.toZeta5 == -(phiInv * Zeta5.pow 2)) = true ∧ (cut10₂.toZeta5 == Zeta5.pow 2) = true ∧
    (zero10.toZeta5 == Zeta5.zero) = true ∧ ((centre10 (-1)).toZeta5 == leftCentre) = true ∧
    ((centre10 1).toZeta5 == rightCentre) = true ∧
    ((w10.toZeta5 - leftCentre).normSq == fourMinusPhi) = true ∧
    QSqrt.lt fourMinusPhi (w10.toZeta5 - rightCentre).normSq = true ∧
    ((negW10.toZeta5 - rightCentre).normSq == fourMinusPhi) = true ∧
    ((cut10₁.toZeta5 - leftCentre).normSq == fourMinusPhi) = true ∧
    ((exactSide leftCentre fourMinusPhi zero10.toZeta5 == .inside) &&
      (exactSide rightCentre fourMinusPhi zero10.toZeta5 == .inside) &&
      (exactSide rightCentre fourMinusPhi cut10₁.toZeta5 == .inside) &&
      (exactSide leftCentre fourMinusPhi cut10₂.toZeta5 == .inside) &&
      (exactSide rightCentre fourMinusPhi cut10₂.toZeta5 == .outside) &&
      (exactSide leftCentre fourMinusPhi negW10.toZeta5 == .outside)) = true ∧
    wordTextTen 1 = "b b a⁻¹ b⁻¹" ∧ wordTextTen 2 = "a b a⁻¹ a⁻¹" ∧
    wordTextTen 3 = "a a a b⁻¹ b⁻¹ b⁻¹" := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves orderTen orderTen_spec

/-- What `orderTwelve` draws, item for item, and why its records are right. The data are
`p* = -2ζ + 4ζ² - 3ζ³`, its mirror image `p̄* = 4 - 2ζ - 4ζ² + 5ζ³`, `q₀ = 2 - 4ζ² + 3ζ³` and the
direction `V = -1 - ζ + ζ³ = ζ⁵ + ζ⁶` in `ℤ[ζ₁₂]`, drawn at their coordinates in `ℚ(√3)`
(`ζ₁₂ = (√3/2, 1/2)`), the centres `∓1` and the radius `r₁₂ = √(40 - 22√3)`. The items are written
out in drawing order; `sides12` records where a point stands relative to the two disks and the
lens, decided by `sideQ`. The facts hold exactly in `ℚ(√3)`: `p* = (2 - √3, -4 + 2√3)` with
`|p* + 1|² = 40 - 22√3` (on the left circle) and `|p* - 1|² = 32 - 18√3 < 40 - 22√3` (inside the
right disk); `p̄*` is on the left circle too; `V = (-(1 + √3/2), 1/2)` and
`q₀ - p* = (14 - 8√3) V`, so `q₀` is on the chord; `q₀` is inside both disks. That `q₀` is the
image of `p*` under the seed word `b a b b a a`, every disk test holding, is replayed by the orbit
engine in `TDCSGFigures.Data.Early`. Not stated: how the builders and modifiers draw, the layout,
the lettering, the style's colour values and the pixels. -/
theorem orderTwelve_spec :
    pStar12 = ⟨#[0, -2, 4, -3]⟩ ∧ pStar12Conj = ⟨#[4, -2, -4, 5]⟩ ∧ orbit12 = ⟨#[2, 0, -4, 3]⟩ ∧
    chordDir12 = #[-1, -1, 0, 1] ∧ radiusTwelve = ⟨⟨40, -22⟩⟩ ∧
    (∀ k : Int, centre12 k = ⟨#[k, 0, 0, 0]⟩) ∧
    orderTwelve.items = #[
      Plane.Exact.disk (centre12 (-1)) radiusTwelve |>.noFill |>.role leftRole
        |>.named "the left circle"
        |>.describedBy "the closed disk of radius r₁₂ = √(40 − 22√3) about −1"
        |>.declRef `TDCSG.CriticalRadius.criticalRadius_twelve_le,
      Plane.Exact.disk (centre12 1) radiusTwelve |>.noFill |>.role rightRole
        |>.named "the right circle"
        |>.describedBy "the closed disk of radius r₁₂ = √(40 − 22√3) about 1"
        |>.declRef `TDCSG.CriticalRadius.criticalRadius_twelve_le,
      Plane.Exact.lens (centre12 (-1)) (centre12 1) radiusTwelve radiusTwelve |>.role lensRole
        |>.noOutline |>.fillOpacity 0.12 |>.named "the lens",
      Plane.Exact.segment (centre12 (-1)) pStar12Conj |>.role leftRole |>.width 1.5 |>.dashed
        |>.named "a radius r₁₂ of the left disk",
      Plane.Exact.labelBeside "r₁₂" (centre12 (-1)) pStar12Conj |>.role leftRole,
      Plane.Exact.line pStar12 orbit12 |>.faint |>.dashed
        |>.named "the chord p* + uV, in the direction V = ζ⁵ + ζ⁶",
      Plane.Exact.point (centre12 (-1)) |>.role leftRole |>.named "the centre −1",
      Plane.Exact.point (centre12 1) |>.role rightRole |>.named "the centre 1",
      sides12 pStar12 (Plane.Exact.point pStar12 |>.role leftRole |>.size 3
        |>.named "p* = −2ζ + 4ζ² − 3ζ³"
        |>.incident .on "the chord p* + uV, in the direction V = ζ⁵ + ζ⁶"
        |>.declRef `TDCSG.CriticalRadius.pStar_twelve_mem_sphere),
      sides12 orbit12 (Plane.Exact.point orbit12 |>.size 3 |>.named "q₀ = p* + (14 − 8√3)V"
        |>.incident .on "the chord p* + uV, in the direction V = ζ⁵ + ζ⁶"
        |>.declRef `TDCSG.CriticalRadius.infinite_orbit_pStar_twelve),
      Plane.Exact.label "−1" (centre12 (-1)) .auto |>.role leftRole,
      Plane.Exact.label "+1" (centre12 1) .auto |>.role rightRole,
      Plane.Exact.label "p*" pStar12 .auto |>.role leftRole,
      Plane.Exact.label "q₀" orbit12 .auto,
      Plane.label "chord" ((PlanePoint.toPoint pStar12).lerp (PlanePoint.toPoint orbit12) (-3.5))
      .below,
      Plane.Exact.label "left disk" ((-8 / 5 : Rat), (-3 / 10 : Rat)) |>.role leftRole,
      Plane.Exact.label "right disk" ((8 / 5 : Rat), (3 / 10 : Rat)) |>.role rightRole] ∧
    (pStar12.coords12 == (⟨2, -1⟩, ⟨-4, 2⟩)) = true ∧
    (pStar12Conj.coords12 == (⟨2, -1⟩, ⟨4, -2⟩)) = true ∧
    ((CycPt.coords12 ⟨chordDir12⟩) == (⟨-1, -1 / 2⟩, ⟨1 / 2, 0⟩)) = true ∧
    ((orbit12.coords12.1 - pStar12.coords12.1) ==
      (⟨14, -8⟩ : QSqrt 3) * (CycPt.coords12 ⟨chordDir12⟩).1) = true ∧
    ((orbit12.coords12.2 - pStar12.coords12.2) ==
      (⟨14, -8⟩ : QSqrt 3) * (CycPt.coords12 ⟨chordDir12⟩).2) = true ∧
    (distSq pStar12.coords12 (centre12 (-1)).coords12 == ⟨40, -22⟩) = true ∧
    (distSq pStar12.coords12 (centre12 1).coords12 == ⟨32, -18⟩) = true ∧
    (distSq pStar12Conj.coords12 (centre12 (-1)).coords12 == ⟨40, -22⟩) = true ∧
    (sideQ (centre12 (-1)).coords12 pStar12.coords12 radiusTwelve.radicand == .on) = true ∧
    (sideQ (centre12 1).coords12 pStar12.coords12 radiusTwelve.radicand == .inside) = true ∧
    (sideQ (centre12 (-1)).coords12 orbit12.coords12 radiusTwelve.radicand == .inside) = true ∧
    (sideQ (centre12 1).coords12 orbit12.coords12 radiusTwelve.radicand == .inside) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves orderTwelve orderTwelve_spec

end TDCSGFigures
