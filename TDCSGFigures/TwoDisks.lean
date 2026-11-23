/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.Early
import TDCSGFigures.Style

/-!
# The figures of chapter 2, two disks and the critical radius

* `generatorStep`: the closed disks of radius `3/2` about `-1` and `1`, their lens, and one step
  of the left generator: `a` turns `0` clockwise through `72°` about `-1`, to `a(0) = -1 + ζ⁴`.
* `wordSteps`: a stepper that follows `0` through the word `a b b a` at radius `2.1`, letter by
  letter; a letter turns the point when the point lies in the letter's closed disk and leaves it
  where it is otherwise.

Every point is exact in `ℤ[ζ₅]`, every radius rational, and every incidence the figures record is
decided exactly in `ℚ(√5)` (`generatorStep_spec`, `wordSteps_spec`).
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-! ### One step of the left generator -/

/-- The end `(19/10, -6/5)` of the drawn radius of the right disk: `|(9/10, -6/5)| = 3/2`. -/
def rightSpokeEnd : Rat × Rat := (19 / 10, -6 / 5)

/-- The items of `generatorStep`, in drawing order. -/
def generatorStepItems : Array Item := #[
  Plane.Exact.disk leftCentre (3 / 2 : Rat) |>.noFill |>.role leftRole |>.named "the left circle"
    |>.describedBy "the closed disk of radius 3/2 about −1, turned by a" |>.declRef `TDCSG.genA,
  Plane.Exact.disk rightCentre (3 / 2 : Rat) |>.noFill |>.role rightRole
    |>.named "the right circle" |>.describedBy "the closed disk of radius 3/2 about 1, turned by b"
    |>.declRef `TDCSG.genB,
  Plane.Exact.lens leftCentre rightCentre (3 / 2 : Rat) (3 / 2 : Rat) |>.role lensRole
    |>.noOutline |>.fillOpacity 0.12 |>.named "the lens",
  Plane.Exact.segment ((1 : Rat), (0 : Rat)) rightSpokeEnd |>.role rightRole |>.width 1.5
    |>.dashed |>.named "a radius of the right disk, length 3/2",
  Plane.Exact.labelBeside "r = 1.5" ((1 : Rat), (0 : Rat)) rightSpokeEnd |>.role rightRole,
  Plane.Exact.segment leftCentre origin |>.role leftRole |>.width 1.5
    |>.named "from −1 to 0",
  Plane.Exact.segment leftCentre aZero |>.role leftRole |>.width 1.5
    |>.named "from −1 to a(0)",
  Plane.Exact.angleMark leftCentre 0 (-deg 72) (some 22) |>.role leftRole
    |>.named "72° clockwise",
  Plane.Exact.label "72°" leftCentre (.toward (-deg 112)) (some 26) |>.role leftRole |>.size 12,
  Plane.Exact.arc leftCentre (1 : Rat) (deg 0) (-deg 72) |>.withArrow |>.role leftRole
    |>.width 2 |>.dashed |>.named "a turns 0 through 72° clockwise about −1"
    |>.declRef `TDCSG.diskRotation,
  Plane.Exact.point leftCentre |>.role leftRole |>.named "the centre −1",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the centre 1",
  Plane.Exact.point origin |>.named "0" |>.incident .inside "the left circle"
    |>.incident .inside "the right circle" |>.incident .inside "the lens",
  Plane.Exact.point aZero |>.role leftRole |>.named "a(0) = −1 + ζ⁴"
    |>.incident .inside "the left circle" |>.incident .outside "the right circle"
    |>.incident .outside "the lens" |>.declRef `TDCSG.genA,
  Plane.Exact.label "−1" leftCentre .above |>.role leftRole,
  Plane.Exact.label "+1" rightCentre .above |>.role rightRole,
  Plane.Exact.label "0" origin .aboveRight,
  Plane.Exact.label "a(0)" aZero .below |>.role leftRole,
  Plane.Exact.label "left disk" ((-8 / 5 : Rat), (3 / 4 : Rat)) |>.role leftRole,
  Plane.Exact.label "right disk" ((8 / 5 : Rat), (3 / 4 : Rat)) |>.role rightRole,
  Plane.Exact.label "lens" ((0 : Rat), (5 / 8 : Rat)) |>.role lensRole |>.size 13]

/-- The closed disks of radius 1.5 about −1 and 1 and their lens; the left generator a turns the
origin clockwise through 72° about −1, to a(0) = −1 + ζ⁴. The origin lies in both disks, a(0) in
the left disk only. -/
@[figure]
def generatorStep : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := generatorStepItems
  info := { title := "One step of the left generator" }

/-! ### A word, letter by letter -/

/-- The point with where it stands relative to the two closed disks of radius 2.1 and their lens,
decided exactly. -/
def withSidesStep (z : Zeta5) (it : Item) : Item := recordSides r2Step z it

/-- The labels `z₀, …, z₄` of the points of the stepper. -/
def stepName (k : Nat) : String := s!"z{#["₀", "₁", "₂", "₃", "₄"].getD k ""}"

/-- What every frame of the stepper draws: the two closed disks of radius 2.1, their lens, the
centres and the names. -/
def stepBase : Array Item := #[
  Plane.Exact.disk leftCentre (21 / 10 : Rat) |>.noFill |>.role leftRole |>.named "the left circle"
    |>.describedBy "the closed disk of radius 2.1 about −1, turned by a" |>.declRef `TDCSG.genA,
  Plane.Exact.disk rightCentre (21 / 10 : Rat) |>.noFill |>.role rightRole
    |>.named "the right circle"
    |>.describedBy "the closed disk of radius 2.1 about 1, turned by b" |>.declRef `TDCSG.genB,
  Plane.Exact.lens leftCentre rightCentre (21 / 10 : Rat) (21 / 10 : Rat) |>.role lensRole
    |>.noOutline
    |>.fillOpacity 0.12 |>.named "the lens",
  withSidesStep leftCentre (Plane.Exact.point leftCentre |>.role leftRole |>.named "the centre −1"),
  withSidesStep rightCentre
    (Plane.Exact.point rightCentre |>.role rightRole |>.named "the centre 1"),
  Plane.Exact.label "−1" leftCentre .auto |>.role leftRole,
  Plane.Exact.label "+1" rightCentre .auto |>.role rightRole,
  Plane.Exact.label "left disk, radius 2.1" ((-1 : Rat), (-5 / 2 : Rat)) |>.role leftRole,
  Plane.Exact.label "right disk, radius 2.1" ((1 : Rat), (5 / 2 : Rat)) |>.role rightRole]

/-- Frame `k` of the stepper: the base, the points `z₀, …, z_{k-1}` faint, the point `z_k`, and for
`k ≥ 1` the turn of letter `k` as an arc from `z_{k-1}` to `z_k` about its centre, or, when the
letter fixes the point, a note saying so beside the point. -/
def stepFrame (k : Nat) : Plane.Figure :=
  let pts := stepPoints
  let z := pts.getD k origin
  let past := (List.range k).filter (fun j => pts.getD j origin != z)
  let move : Array Item := match k with
    | 0 => #[]
    | k + 1 =>
      let l := stepWord.getD k .a
      let z₀ := pts.getD k origin
      let role := if l.centre == leftCentre then leftRole else rightRole
      if z₀ == z then
        #[Plane.Exact.label s!"{stepName (k + 1)} = {stepName k}: {l.text} fixes it" z .left
            |>.role role]
      else
        let θ := angleFrom l.centre z₀
        #[Plane.Exact.arc l.centre (SqrtOf.mk (z₀ - l.centre).normSq) θ (θ - deg 72)
            |>.withArrow |>.role role |>.width 2 |>.dashed
            |>.named s!"{l.text} turns {stepName k} through 72° clockwise"
            |>.declRef (if l.centre == leftCentre then `TDCSG.genA else `TDCSG.genB)]
  { width := figureWidth
    padding := 16
    style := houseStyle
    checks := .fail
    items := stepBase ++ move ++
      (past.toArray.map fun j =>
        withSidesStep (pts.getD j origin)
          (Plane.Exact.point (pts.getD j origin) |>.faint |>.named (stepName j))) ++
      (past.toArray.map fun j =>
        Plane.Exact.label (stepName j) (pts.getD j origin) .auto) ++
      #[withSidesStep z (Plane.Exact.point z |>.named (stepName k)),
        Plane.Exact.label (stepName k) z .auto |>.bold]
    info := { title := s!"The point {stepName k} of 0 under a b b a at radius 2.1" } }

/-- The captions of the stepper's frames. -/
def stepCaptions : Array String := #[
  "z₀ = 0, in both disks",
  "a: z₀ is in the left disk; a turns it 72° clockwise about −1",
  "b: z₁ is in the right disk; b turns it 72° clockwise about +1",
  "b: z₂ is in the right disk; b turns it again",
  "a: z₃ is outside the left disk; a leaves it where it is"]

/-- The frames of the stepper with their captions. -/
def stepFrames : Array (String × Plane.Figure) :=
  stepCaptions.mapIdx fun k c => (c, stepFrame k)

/-- The point 0 under the word a b b a at radius 2.1, letter by letter: a turns the point when it
lies in the left closed disk and leaves it otherwise, b likewise with the right disk. -/
@[figure]
def wordSteps : Explorer := Plane.stepper stepFrames

end TDCSGFigures
