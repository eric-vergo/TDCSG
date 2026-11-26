/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2, Claude Opus 5.5
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.Early
import TDCSGFigures.Data.Moves
import TDCSGFigures.Style

/-!
# The figures of chapter 2, two disks and the critical radius

* `generatorStep`: an animation of one step of the left generator at radius `3/2`. The left disk
  turns a fifth of a turn clockwise about `-1`, carrying the points inside it (`turnedSamples`,
  the origin among them) and leaving the points outside it where they are (`fixedSamples`);
  then the turn is drawn as an arc from `0` to `a(0) = -1 + ζ⁴`. Its last key frame is the figure
  of one step of the generator (`generatorStepFinal`), which keeps its linked theorem.
* `wordSteps`: an animation that follows `0` through the word `a b b a` at radius `2.1`, letter by
  letter (an illustration): a letter turns the point a fifth of a turn about its centre when the
  point lies in the letter's closed disk, and the last letter, whose disk does not hold the point,
  leaves it where it is.

Every point is exact in `ℤ[ζ₅]`, every radius rational, and every incidence the figures record is
decided exactly in `ℚ(√5)`; every declared move is checked exactly (`generatorArrives`,
`stepsArrive`). The statements are `generatorStep_spec`, `generatorStep_keys` and
`wordSteps_keys`.
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-! ### One step of the left generator -/

/-- The end `(19/10, -6/5)` of the drawn radius of the right disk: `|(9/10, -6/5)| = 3/2`. -/
def rightSpokeEnd : Rat × Rat := (19 / 10, -6 / 5)

/-- The items of `generatorStepFinal` before the marks of the turn: the disks, the lens, the
drawn radius of the right disk and the segment from `-1` to `0`. -/
def generatorBase : Array Item := #[
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
    |>.named "from −1 to 0"]

/-- The marks of the turn, which the animation fades in after the turn (actors `"image-spoke"`,
`"angle"`, `"angle-label"`, `"arc"`): the segment from `-1` to `a(0)`, the angle of `72°` and the
arc from `0` to `a(0)`. -/
def generatorMarks : Array Item := #[
  Plane.Exact.segment leftCentre aZero |>.role leftRole |>.width 1.5
    |>.named "from −1 to a(0)" |>.withId "image-spoke",
  Plane.Exact.angleMark leftCentre 0 (-deg 72) (some 22) |>.role leftRole
    |>.named "72° clockwise" |>.withId "angle",
  Plane.Exact.label "72°" leftCentre (.toward (-deg 112)) (some 26) |>.role leftRole |>.size 12
    |>.withId "angle-label",
  Plane.Exact.arc leftCentre (1 : Rat) (deg 0) (-deg 72) |>.withArrow |>.role leftRole
    |>.width 2 |>.dashed |>.named "a turns 0 through 72° clockwise about −1"
    |>.declRef `TDCSG.diskRotation |>.withId "arc"]

/-- The centres. -/
def generatorCentres : Array Item := #[
  Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1"]

/-- The origin, where it was before the turn (actor `"origin"`). -/
def generatorOrigin : Item :=
  Plane.Exact.point origin |>.named "0" |>.incident .inside "the left circle"
    |>.incident .inside "the right circle" |>.incident .inside "the lens" |>.withId "origin"

/-- The point `a(0)` (actor `"image"`). -/
def generatorImage : Item :=
  Plane.Exact.point aZero |>.role leftRole |>.named "a(0) = −1 + ζ⁴"
    |>.incident .inside "the left circle" |>.incident .outside "the right circle"
    |>.incident .outside "the lens" |>.declRef `TDCSG.genA |>.withId "image"

/-- The labels of the centres and of the origin. -/
def generatorLabels : Array Item := #[
  Plane.Exact.label "−1" leftCentre .above |>.role leftRole,
  Plane.Exact.label "+1" rightCentre .above |>.role rightRole,
  Plane.Exact.label "0" origin .aboveRight]

/-- The label of `a(0)` (actor `"image-label"`). -/
def generatorImageLabel : Item :=
  Plane.Exact.label "a(0)" aZero .below |>.role leftRole |>.withId "image-label"

/-- The names of the disks and of the lens. -/
def generatorNames : Array Item := #[
  Plane.Exact.label "left disk" ((-8 / 5 : Rat), (3 / 4 : Rat)) |>.role leftRole,
  Plane.Exact.label "right disk" ((8 / 5 : Rat), (3 / 4 : Rat)) |>.role rightRole,
  Plane.Exact.label "lens" ((0 : Rat), (5 / 8 : Rat)) |>.role lensRole |>.size 13]

/-- The figure of one step of the left generator, the last key frame of `generatorStep`: the
closed disks of radius 1.5 about −1 and 1 and their lens; the left generator a turns the origin
clockwise through 72° about −1, to a(0) = −1 + ζ⁴. The origin lies in both disks, a(0) in the
left disk only. -/
def generatorStepFinal : Plane.Figure where
  width := figureWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := generatorBase ++ generatorMarks ++ generatorCentres ++
    #[generatorOrigin, generatorImage] ++ generatorLabels ++ #[generatorImageLabel] ++
    generatorNames
  info := { title := "One step of the left generator" }

/-- The points of the left disk that the animation turns with it: `0` (on the circle of radius
`1` about `-1`), `-1 + φ⁻¹ ζ³`, `ζ⁴ - 2 = -1 + (ζ⁴ - 1)` and `-1 + ζ² - ζ³`
(`φ⁻¹ = ζ + ζ⁴`). -/
def turnedSamples : List Zeta5 :=
  [origin, leftCentre + phiInv * zeta 3, zeta 4 - Zeta5.ofInt 2, leftCentre + zeta 2 - zeta 3]

/-- Points just outside the left disk, which the animation leaves where they are: `φ⁻¹`, in the
right disk, and `-1 + φ ζ²`, `-1 + φ ζ³` (`φ = 1 + φ⁻¹`), at distance `φ > 3/2` from `-1`. -/
def fixedSamples : List Zeta5 :=
  [phiInv, leftCentre + (Zeta5.ofInt 1 + phiInv) * zeta 2,
    leftCentre + (Zeta5.ofInt 1 + phiInv) * zeta 3]

/-- The points of `turnedSamples` after the turn by `a`, `-1 + ζ⁴ (z + 1)`. -/
def turnedImages : List Zeta5 := turnedSamples.map Letter.a.rotate

/-- The content of the left disk that turns (actor `"disk"`), with the samples at `zs`: the
segment from the first to `-1`, the first as a point and the others as small dots, each recording
that it lies inside the left disk. -/
def turningContent (zs : List Zeta5) : Item :=
  let z := zs.headD origin
  (group (#[Plane.Exact.segment z leftCentre |>.role leftRole |>.width 1.5,
      Plane.Exact.point z |>.role leftRole] ++
    (zs.drop 1).toArray.map fun w =>
      Plane.Exact.point w |>.role leftRole |>.size 3 |>.incident .inside "the left circle"))
    |>.named "points of the left disk, which a turns" |>.withId "disk"

/-- The points outside the left disk (actor `"outside"`), each recording that it lies outside. -/
def fixedContent : Item :=
  group (fixedSamples.toArray.map fun w =>
      Plane.Exact.point w |>.size 3 |>.incident .outside "the left circle")
    |>.named "points outside the left disk, which a fixes" |>.withId "outside"

/-- The items of key `k` of `generatorStep`, `k ≤ 1`: the content of the left disk, the origin and
the samples inside it, before (`k = 0`) or after the turn, and the points outside it, between the
base and the centres of `generatorStepFinal`, in place of its marks of the turn, the origin,
`a(0)` and its label. -/
def generatorKeyItems (k : Nat) : Array Item :=
  generatorBase ++
    #[turningContent (if k == 0 then turnedSamples else turnedImages), fixedContent] ++
    generatorCentres ++ generatorLabels ++ generatorNames

/-- The captions of the keys of `generatorStep`. -/
def generatorCaptions : Array String := #[
  "The left generator a acts on its closed disk of radius 1.5 about −1. The points inside the \
    disk, the origin among them (drawn in the color of the left disk), turn with it; the points \
    outside it stay where they are.",
  "a turns the disk a fifth of a turn clockwise about −1: the origin goes to a(0) = −1 + ζ⁴, \
    and the points outside the left disk have not moved.",
  "One step of the left generator: a turns the origin through 72° clockwise about −1, along the \
    dashed arc, to a(0). The origin lies in both disks, a(0) in the left disk only."]

/-- Key `k` of `generatorStep`, `k ≤ 1`: the items `generatorKeyItems k` in the frame of
`generatorStepFinal`. -/
def generatorKey (k : Nat) : Plane.Figure :=
  { generatorStepFinal with items := generatorKeyItems k,
                            info := { title := generatorCaptions.getD k "" } }

/-- The keys of `generatorStep`: two keys, then the figure `generatorStepFinal`. -/
def generatorKeys : Array Plane.Figure := #[generatorKey 0, generatorKey 1, generatorStepFinal]

/-- The turn of the left disk: about `-1`, by `-1/5` of a full turn (clockwise). -/
def generatorTurn : ExactTurn := ⟨ZetaFrac.ofZeta leftCentre, -1 / 5⟩

/-- The declared moves of the steps of `generatorStep`: the content of the left disk turns; then
it and the points outside vanish while the marks of the turn, the origin, `a(0)` and its label
appear. -/
def generatorMoves : Nat → List (String × ExactMove ZetaFrac)
  | 0 => [("disk", .turn generatorTurn)]
  | _ => [("disk", .vanish), ("outside", .vanish), ("image-spoke", .appear), ("angle", .appear),
      ("angle-label", .appear), ("arc", .appear), ("origin", .appear), ("image", .appear),
      ("image-label", .appear)]

/-- The exact anchors of the actors of key `k` of `generatorStep`: at keys `0` and `1`, the
content of the disk (the first sample and the centre, the ends of the segment, then the samples,
`turnedSamples` before the turn and `turnedImages` after) and the points
outside; at key `2`, the marks of the turn (the ends of the segment and of the arc, the centre of
the angle and of its label), the origin, `a(0)` and its label. -/
def generatorActors (k : Nat) : List (ExactActor ZetaFrac) :=
  let z := ZetaFrac.ofZeta
  let samples := if k == 0 then turnedSamples else turnedImages
  if k ≤ 1 then
    [⟨"disk", [z (samples.headD origin), z leftCentre] ++ samples.map z⟩,
      ⟨"outside", fixedSamples.map z⟩]
  else
    [⟨"image-spoke", [z leftCentre, z aZero]⟩, ⟨"angle", [z leftCentre]⟩,
      ⟨"angle-label", [z leftCentre]⟩, ⟨"arc", [z origin, z aZero]⟩, ⟨"origin", [z origin]⟩,
      ⟨"image", [z aZero]⟩, ⟨"image-label", [z aZero]⟩]

/-- Whether every declared move of `generatorStep` carries the actors of one key onto those of the
next, exactly in `ℚ(ζ₅)`. -/
def generatorArrives : Bool := allArrive 2 generatorMoves generatorActors

/-- One step of the left generator at radius 1.5: the left disk turns a fifth of a turn clockwise
about −1, carrying the points inside it, the origin to a(0) = −1 + ζ⁴, and leaving the points
outside it where they are; then the turn is drawn as an arc. The last key frame is the figure of
the step, `generatorStepFinal`. -/
@[figure]
def generatorStep : MotionPanels where
  panels := #[{ motion := { keys := generatorKeys,
                            steps := ((List.range 2).map (exactStep ∘ generatorMoves)).toArray } }]
  captions := generatorCaptions
  pacing := motionPacing
  timing := ((List.range 2).map fun k => moveTiming (generatorMoves k)).toArray
  info := { title := "One step of the left generator"
            description := "The closed disks of radius 1.5 about −1 and 1 and their lens. The \
              left disk turns a fifth of a turn clockwise about −1 and carries the points inside \
              it: the origin goes to a(0) = −1 + ζ⁴. The points outside the left disk stay \
              where they are. Then the turn is drawn as a dashed arc from 0 to a(0)." }
  checks := .fail
  poster := 2
  width := figureWidth
  narrowWidth := some narrowWidth

/-! ### A word, letter by letter -/

/-- The point with where it stands relative to the two closed disks of radius 2.1 and their lens,
decided exactly. -/
def withSidesStep (z : Zeta5) (it : Item) : Item := recordSides r2Step z it

/-- The labels `z₀, …, z₄` of the points of the word. -/
def stepName (k : Nat) : String := s!"z{#["₀", "₁", "₂", "₃", "₄"].getD k ""}"

/-- What every key of `wordSteps` draws: the two closed disks of radius 2.1, their lens, the
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
  withSidesStep leftCentre (Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1"),
  withSidesStep rightCentre
    (Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1"),
  Plane.Exact.label "−1" leftCentre .left (some 24) |>.role leftRole,
  Plane.Exact.label "+1" rightCentre .right (some 24) |>.role rightRole,
  Plane.Exact.label "left disk, radius 2.1" ((-1 : Rat), (-5 / 2 : Rat)) |>.role leftRole,
  Plane.Exact.label "right disk, radius 2.1" ((1 : Rat), (5 / 2 : Rat)) |>.role rightRole]

/-- The point `z_k` of `0` under `a b b a` (`stepPoints`). -/
def stepPoint (k : Nat) : Zeta5 := stepPoints.getD k origin

/-- Whether letter `k + 1` of `a b b a` turns `z_k` (`Letter.covers`, decided exactly). -/
def stepActs (k : Nat) : Bool := (stepWord.getD k .a).covers r2Step (stepPoint k)

/-- The point that follows the word (actor `"point"`), at `z_k`. -/
def stepMover (k : Nat) : Item :=
  Plane.Exact.point (stepPoint k) |>.size 5 |>.named "the point followed through the word"
    |>.withId "point"

/-- The point `z_j` left behind (actor `"trail-<j>"`): faint, with its label, recording where it
stands relative to the disks. -/
def stepTrail (j : Nat) : Item :=
  (group #[withSidesStep (stepPoint j) (Plane.Exact.point (stepPoint j) |>.faint),
      Plane.Exact.label (stepName j) (stepPoint j) .auto])
    |>.named (stepName j) |>.withId s!"trail-{j}"

/-- The points left behind at key `k`: `z_j` for `j < k` with `z_j ≠ z_k`. -/
def stepTrailIndices (k : Nat) : List Nat :=
  (List.range k).filter fun j => !(stepPoint j == stepPoint k)

/-- The radius of the circle that marks the centre of the last turn. -/
def stepPivotRadius : Rat := 1 / 5

/-- The circle about the centre of the last turn at key `k`, for `1 ≤ k ≤ 3`, the keys after a
letter that turns (actor `"pivot-left"` about `-1` or `"pivot-right"` about `1`). -/
def stepPivot (k : Nat) : Array Item :=
  if k == 0 || 3 < k then #[]
  else
    let c := (stepWord.getD (k - 1) .a).centre
    let left := c == leftCentre
    #[Plane.Exact.circle c stepPivotRadius |>.role (if left then leftRole else rightRole)
      |>.width 2 |>.named s!"a circle about the center {if left then "−1" else "+1"} of the last \
        turn" |>.withId (if left then "pivot-left" else "pivot-right")]

/-- At key `4`, the segment from `-1` to `z₃` (actor `"reach"`), longer than the radius `2.1`:
`z₃` lies outside the left disk, so the last `a` does not act. -/
def stepReach (k : Nat) : Array Item :=
  if k == 4 then
    #[Plane.Exact.segment leftCentre (stepPoint 3) |>.role leftRole |>.width 1.5 |>.dashed
      |>.named "from −1 to z₃, longer than 2.1" |>.withId "reach"]
  else #[]

/-- The items of key `k` of `wordSteps`. -/
def stepKeyItems (k : Nat) : Array Item :=
  stepBase ++ stepPivot k ++ stepReach k ++ (stepTrailIndices k).toArray.map stepTrail ++
    #[stepMover k]

/-- The captions of the keys of `wordSteps`. -/
def stepCaptions : Array String := #[
  "z₀ = 0, in both disks. The word a b b a is applied to it at radius 2.1, letter by letter from \
    left to right.",
  "Letter 1, a: z₀ lies in the left disk, so a turns it a fifth of a turn clockwise about −1 \
    (circled), to z₁.",
  "Letter 2, b: z₁ lies in the right disk, so b turns it a fifth of a turn clockwise about +1 \
    (circled), to z₂.",
  "Letter 3, b: z₂ lies in the right disk, so b turns it again, to z₃.",
  "Letter 4, a: z₃ lies outside the left disk, farther than 2.1 from −1 (dashed), so a leaves it \
    where it is: z₄ = z₃."]

/-- Key `k` of `wordSteps`. -/
def stepKey (k : Nat) : Plane.Figure :=
  { width := figureWidth
    padding := 16
    style := houseStyle
    checks := .fail
    items := stepKeyItems k
    info := { title := s!"The point {stepName k} of 0 under a b b a at radius 2.1" } }

/-- The turn of letter `k + 1` of `a b b a`: about its centre by `-1/5` of a full turn. -/
def stepTurn (k : Nat) : ExactTurn :=
  ⟨ZetaFrac.ofZeta (stepWord.getD k .a).centre, -1 / 5⟩

/-- The id of the circle about the centre of letter `k + 1` of `a b b a`. -/
def stepPivotId (k : Nat) : String :=
  if (stepWord.getD k .a).centre == leftCentre then "pivot-left" else "pivot-right"

/-- The declared moves from key `k` to key `k + 1` of `wordSteps`: for the three letters that act,
the point turns by `stepTurn k`, the circle about the letter's centre appears unless it is already
there and the circle of the letter before vanishes, and the point left behind appears; for the
last letter, which does not act, the segment from `-1` to `z₃` appears and the circle vanishes. -/
def stepMoves : Nat → List (String × ExactMove ZetaFrac)
  | 0 => [("point", .turn (stepTurn 0)), (stepPivotId 0, .appear), ("trail-0", .appear)]
  | 1 => [("point", .turn (stepTurn 1)), (stepPivotId 1, .appear), ("trail-1", .appear),
      (stepPivotId 0, .vanish)]
  | 2 => [("point", .turn (stepTurn 2)), ("trail-2", .appear)]
  | _ => [("reach", .appear), (stepPivotId 2, .vanish)]

/-- The exact anchors of the actors of key `k` of `wordSteps`: the circle about the centre of
letter `k`, the segment from `-1` to `z₃` at key `4`, the points left behind and the point
`z_k`. -/
def stepActors (k : Nat) : List (ExactActor ZetaFrac) :=
  let z := ZetaFrac.ofZeta
  let pivot : List (ExactActor ZetaFrac) :=
    if k == 0 || 3 < k then []
    else
      let c := (stepWord.getD (k - 1) .a).centre
      [⟨if c == leftCentre then "pivot-left" else "pivot-right", [z c]⟩]
  let reach : List (ExactActor ZetaFrac) :=
    if k == 4 then [⟨"reach", [z leftCentre, z (stepPoint 3)]⟩] else []
  pivot ++ reach ++ (stepTrailIndices k).map (fun j => ⟨s!"trail-{j}", [z (stepPoint j)]⟩) ++
    [⟨"point", [z (stepPoint k)]⟩]

/-- Whether every declared move of `wordSteps` carries the actors of one key onto those of the
next, exactly in `ℚ(ζ₅)`. -/
def stepsArrive : Bool := allArrive 4 stepMoves stepActors

/-- The point 0 under the word a b b a at radius 2.1, letter by letter: a turns the point a fifth
of a turn clockwise about −1 when it lies in the left closed disk and leaves it otherwise, b
likewise about +1 with the right disk; here the last a leaves the point where it is. -/
@[figure illustration]
def wordSteps : MotionPanels where
  panels := #[{ motion := { keys := ((List.range 5).map stepKey).toArray,
                            steps := ((List.range 4).map (exactStep ∘ stepMoves)).toArray } }]
  captions := stepCaptions
  pacing := motionPacing
  timing := ((List.range 4).map fun k => moveTiming (stepMoves k)).toArray
  info := { title := "The point 0 under the word a b b a"
            description := "The closed disks of radius 2.1 about −1 and 1 and their lens. The \
              origin is followed through the word a b b a, letters applied from left to right: \
              a turns the point a fifth of a turn clockwise about −1 when it lies in the left \
              disk, b likewise about +1 with the right disk. The first three letters turn it; \
              the point the last a meets lies outside the left disk and stays. A small circle \
              marks the center of the last turn, and the points left behind stay faint." }
  checks := .fail
  width := figureWidth
  narrowWidth := some narrowWidth

end TDCSGFigures
