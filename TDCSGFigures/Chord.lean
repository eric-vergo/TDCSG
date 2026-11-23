/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.Early
import TDCSGFigures.Style

/-!
# The figures of chapter 3, the chord and its three words

* `chordPieces`: the two closed disks of radius `R = √(3 + φ)` about `∓1`, their lens, and the
  chord from `-E` to `E` (`E = ζ - ζ²`) cut at `(1 - φ) E` and `(3 - 2φ) E` into the pieces of
  the three words, each word written out.
* `wordTrace`: a stepper, one frame per word, that follows the word's piece letter by letter
  through the two disks until it lands on the chord again; the ends that meet a boundary circle
  (a disk test that holds with equality) are marked.
* `chordOrbit`: the orbit of `0` along the chord, `t₀ = 0, t₁, …, t₂₄` on the parameter line
  `t ∈ [-1, 1)` of the points `tE`, one row per step, each point in the colour of the piece that
  holds it (the word applied next).

Every point is exact in `ℤ[ζ₅]` or `ℚ(√5)²`, and every recorded incidence is decided exactly in
`ℚ(√5)` (`chordPieces_spec`, `wordTrace_spec`, `chordOrbit_spec`).
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-! ### The pieces of the chord -/

/-- The two closed disks of radius `R` and their lens, as the house style draws them. -/
def criticalDisks : Array Item := #[
  Plane.Exact.disk leftCentre critical |>.noFill |>.role leftRole |>.named "the left circle"
    |>.describedBy "the closed disk of radius R = √(3 + φ) about −1",
  Plane.Exact.disk rightCentre critical |>.noFill |>.role rightRole |>.named "the right circle"
    |>.describedBy "the closed disk of radius R = √(3 + φ) about 1",
  Plane.Exact.lens leftCentre rightCentre critical critical |>.role lensRole |>.noOutline
    |>.fillOpacity 0.12 |>.named "the lens"]

/-- The word `i` written out. -/
def wordText (i : Nat) : String :=
  " ".intercalate ((wordPiece i).1.map Letter.text)

/-- The Lean name of word `i`. -/
def wordDecl : Nat → Lean.Name
  | 1 => `TDCSG.Five.word₁
  | 2 => `TDCSG.Five.word₂
  | _ => `TDCSG.Five.word₃

/-- The items of `chordPieces`, in drawing order. -/
def chordPiecesItems : Array Item := criticalDisks ++ #[
  Plane.Exact.segment (-chordEnd) cutF |>.role (pieceRole 1) |>.width 5
    |>.named "the piece [−E, (1 − φ)E] of word 1" |>.declRef `TDCSG.Five.applyWord_word₁,
  Plane.Exact.labelBeside "1" (-chordEnd) cutF |>.role (pieceRole 1),
  Plane.Exact.segment cutF cutG |>.role (pieceRole 2) |>.width 5
    |>.named "the piece [(1 − φ)E, (3 − 2φ)E] of word 2" |>.declRef `TDCSG.Five.applyWord_word₂,
  Plane.Exact.labelBeside "2" cutF cutG |>.role (pieceRole 2),
  Plane.Exact.segment cutG chordEnd |>.role (pieceRole 3) |>.width 5
    |>.named "the piece [(3 − 2φ)E, E] of word 3" |>.declRef `TDCSG.Five.applyWord_word₃,
  Plane.Exact.labelBeside "3" cutG chordEnd |>.role (pieceRole 3),
  Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1",
  Plane.Exact.point (-chordEnd) |>.role rightRole |>.named "−E"
    |>.incident .on "the right circle" |>.incident .on "the lens",
  Plane.Exact.point cutF |>.named "(1 − φ)E" |>.incident .inside "the lens",
  Plane.Exact.point cutG |>.named "(3 − 2φ)E" |>.incident .inside "the lens",
  Plane.Exact.point chordEnd |>.role leftRole |>.named "E" |>.incident .on "the left circle"
    |>.incident .on "the lens" |>.declRef `TDCSG.Five.norm_embed_pointE_add_one_sq,
  Plane.Exact.label "−1" leftCentre .auto |>.role leftRole,
  Plane.Exact.label "+1" rightCentre .auto |>.role rightRole,
  Plane.Exact.label "−E" (-chordEnd) .left |>.role rightRole,
  Plane.segment (PlanePoint.toPoint cutF) ⟨-1 / 10, -17 / 20⟩ |>.faint |>.width 1
    |>.named "a leader to the label of (1 − φ)E",
  Plane.segment (PlanePoint.toPoint cutG) ⟨-1 / 4, 3 / 5⟩ |>.faint |>.width 1
    |>.named "a leader to the label of (3 − 2φ)E",
  Plane.label "(1 − φ)E" ⟨-1 / 10, -17 / 20⟩ .below,
  Plane.label "(3 − 2φ)E" ⟨-1 / 4, 3 / 5⟩ .above,
  Plane.Exact.label "E" chordEnd .right |>.role leftRole,
  Plane.Exact.label "left disk" ((-2 : Rat), (-9 / 10 : Rat)) |>.role leftRole,
  Plane.Exact.label "right disk" ((2 : Rat), (9 / 10 : Rat)) |>.role rightRole,
  Plane.Exact.label s!"word 1: {wordText 1}" ((0 : Rat), (-12 / 5 : Rat)) |>.role (pieceRole 1)
    |>.declRef `TDCSG.Five.word₁,
  Plane.Exact.label s!"word 2: {wordText 2}" ((0 : Rat), (-27 / 10 : Rat)) |>.role (pieceRole 2)
    |>.declRef `TDCSG.Five.word₂,
  Plane.Exact.label s!"word 3: {wordText 3}" ((0 : Rat), (-3 : Rat)) |>.role (pieceRole 3)
    |>.declRef `TDCSG.Five.word₃]

/-- The two closed disks of radius R = √(3 + φ) about −1 and 1 and the chord from −E to E,
E = ζ − ζ², cut at (1 − φ)E and (3 − 2φ)E into the three pieces on which the three words act,
each word written out below. -/
@[figure]
def chordPieces : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := chordPiecesItems
  info := { title := "The pieces of the chord and their words" }

/-! ### Each word carries its piece back into the chord -/

/-- The name of the circle about `c`. -/
def circleName (c : Zeta5) : String :=
  if c == leftCentre then "the left circle" else "the right circle"

/-- Frame `i` of `wordTrace`: the disks, the chord thin, the piece of word `i` and its images after
`1, 2, …` letters, each image labelled by the number of letters applied, the last one thick on the
chord; the ends on a boundary circle marked. -/
def traceFrame (i : Nat) : Plane.Figure :=
  let path := wordPath i
  let n := path.length - 1
  let segs := path.zipIdx.toArray.map fun ((p, q), k) =>
    Plane.Exact.segment p q |>.role (pieceRole i) |>.width (if k == 0 || k == n then 5 else 2)
      |>.dashed (if k == 0 then #[9, 6] else #[])
      |>.named (if k == 0 then s!"the piece of word {i}"
        else if k == n then s!"its image after all {n} letters, on the chord"
        else s!"its image after {k} letters")
  let labels := path.zipIdx.toArray.map fun ((p, q), k) =>
    Plane.Exact.labelBeside (toString k) p q |>.role (pieceRole i)
  let marks := (wordEqualities i).toArray.map fun (k, z, isLeft) =>
    recordSides threePlusPhi z (Plane.Exact.point z |>.role (if isLeft then leftRole else rightRole)
      |>.named
        s!"an end on {if isLeft then "the left" else "the right"} circle before letter {k + 1}")
  { width := figureWidth
    padding := 16
    style := houseStyle
    checks := .fail
    items := criticalDisks ++
      #[Plane.Exact.segment (-chordEnd) chordEnd |>.faint |>.named "the chord from −E to E"] ++
      segs ++ labels ++ marks ++
      #[Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1",
        Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1",
        Plane.Exact.label "−1" leftCentre .auto |>.role leftRole,
        Plane.Exact.label "+1" rightCentre .auto |>.role rightRole,
        Plane.Exact.label s!"word {i}: {wordText i}" ((0 : Rat), (-12 / 5 : Rat))
          |>.role (pieceRole i) |>.declRef (wordDecl i)]
    info := { title := s!"Word {i} carries its piece back into the chord" } }

/-- The captions of the frames of `wordTrace`. -/
def traceCaptions : Array String := #[
  "word 1 = a⁻¹ a⁻¹ b⁻¹ a⁻¹ b⁻¹ moves its piece by (2φ − 2)E",
  "word 2 = a b a b b moves its piece by (2φ − 2)E",
  "word 3 = a b a b⁻¹ a⁻¹ b⁻¹ moves its piece by (2φ − 4)E"]

/-- The frames of `wordTrace` with their captions. -/
def traceFrames : Array (String × Plane.Figure) :=
  traceCaptions.mapIdx fun k c => (c, traceFrame (k + 1))

/-- The three words at the critical radius, one per frame: the piece of the chord that word i acts
on, its images after each letter (numbered by the letters applied), and the last image, on the
chord again; the ends on a boundary circle are marked. -/
@[figure]
def wordTrace : Explorer := Plane.stepper traceFrames

/-! ### The orbit of zero along the chord -/

/-- The number of steps drawn. -/
def orbitSteps : Nat := 24

/-- The height of row `k`: `-k/20`. -/
def rowY (k : Nat) : QSqrt5 := rat (-(k : Rat) / 20)

/-- The point `(t, y)`. -/
def tPoint (t y : QSqrt5) : QSqrt5 × QSqrt5 := (t, y)

/-- The height of the chord's pieces above row 0. -/
def chordRowY : QSqrt5 := rat (3 / 20)

/-- The height of the axis below the last row. -/
def axisY : QSqrt5 := rat (-((orbitSteps : Rat) + 2) / 20)

/-- The ends `-1, 1 - φ, 3 - 2φ, 1` of the pieces on the parameter line. -/
def pieceEnds : Array QSqrt5 := #[rat (-1), rat 1 - phi, rat 3 - phi * rat 2, rat 1]

/-- The point of row `k`: `t_k`, in the colour of the piece holding it. -/
def rowPoint (k : Nat) (w : Nat) (t : QSqrt5) : Item :=
  Plane.Exact.point (tPoint t (rowY k)) |>.role (pieceRole w) |>.size 3 |>.halo false
    |>.named s!"t{subscript k} = {phiText t}, word {w} next"
    |>.incident (if w == 1 then .inside else .outside) "the band of piece 1"
    |>.incident (if w == 2 then .inside else .outside) "the band of piece 2"
    |>.incident (if w == 3 then .inside else .outside) "the band of piece 3"

/-- The band of piece `i` behind the rows: the parameters of the piece, from the chord's row down
to the axis. -/
def band (i : Nat) : Item :=
  let a := pieceEnds[i - 1]!
  let b := pieceEnds[i]!
  Plane.Exact.polygon [tPoint a chordRowY, tPoint b chordRowY, tPoint b axisY, tPoint a axisY]
    |>.filled |>.noOutline |>.fillOpacity 0.08 |>.role (pieceRole i)
    |>.named s!"the band of piece {i}"

/-- The items of `chordOrbit`, before the points. -/
def chordOrbitFrame : Array Item :=
  let p := fun (i : Nat) => pieceEnds[i]!
  #[band 1, band 2, band 3,
    Plane.Exact.segment (tPoint (p 0) chordRowY) (tPoint (p 1) chordRowY) |>.role (pieceRole 1)
      |>.width 5 |>.named "the piece of word 1, t ≤ 1 − φ" |>.declRef `TDCSG.Five.applyWord_word₁,
    Plane.Exact.segment (tPoint (p 1) chordRowY) (tPoint (p 2) chordRowY) |>.role (pieceRole 2)
      |>.width 5 |>.named "the piece of word 2, 1 − φ < t < 3 − 2φ"
      |>.declRef `TDCSG.Five.applyWord_word₂,
    Plane.Exact.segment (tPoint (p 2) chordRowY) (tPoint (p 3) chordRowY) |>.role (pieceRole 3)
      |>.width 5 |>.named "the piece of word 3, t ≥ 3 − 2φ" |>.declRef `TDCSG.Five.applyWord_word₃,
    Plane.Exact.label "1" (tPoint ((p 0 + p 1) * rat (1 / 2)) chordRowY) .above
      |>.role (pieceRole 1),
    Plane.Exact.label "2" (tPoint ((p 1 + p 2) * rat (1 / 2)) chordRowY) .above
      |>.role (pieceRole 2),
    Plane.Exact.label "3" (tPoint ((p 2 + p 3) * rat (1 / 2)) chordRowY) .above
      |>.role (pieceRole 3),
    Plane.Exact.label "word" (tPoint (p 0) chordRowY) .left,
    Plane.Exact.point (tPoint (p 0) chordRowY) |>.named "t = −1, the point −E, in the range",
    Plane.Exact.point (tPoint (p 3) chordRowY) |>.marker .ring
      |>.named "t = 1, the point E, not in the range [−1, 1)",
    Plane.Exact.segment (tPoint (p 0) axisY) (tPoint (p 3) axisY)
      |>.named "the parameter t of the point tE",
    Plane.Exact.tickAt (tPoint (p 0) axisY) (tPoint (p 0) axisY) (tPoint (p 3) axisY),
    Plane.Exact.tickAt (tPoint (p 1) axisY) (tPoint (p 0) axisY) (tPoint (p 3) axisY),
    Plane.Exact.tickAt (tPoint (p 2) axisY) (tPoint (p 0) axisY) (tPoint (p 3) axisY),
    Plane.Exact.tickAt (tPoint (p 3) axisY) (tPoint (p 0) axisY) (tPoint (p 3) axisY),
    Plane.Exact.label "−1" (tPoint (p 0) axisY) .below |>.size 13,
    Plane.Exact.label "1 − φ" (tPoint (p 1) axisY) .belowLeft |>.size 13,
    Plane.Exact.label "3 − 2φ" (tPoint (p 2) axisY) .belowRight |>.size 13,
    Plane.Exact.label "1" (tPoint (p 3) axisY) .below |>.size 13,
    Plane.Exact.label "t, the point tE of the chord" (tPoint (rat 0) (axisY - rat (3 / 20)))
      .below]

/-- The abscissa of the axis of steps, left of the bands. -/
def stepAxisX : QSqrt5 := rat (-11 / 10)

/-- The steps `k` with a tick on the axis of steps. -/
def stepTicks : List Nat := [0, 6, 12, 18, 24]

/-- The axis of steps left of the bands: the step number `k` downwards, from row `0` to row
`orbitSteps`, with ticks at `stepTicks` and its name. -/
def stepAxis : Array Item :=
  let top := tPoint stepAxisX (rowY 0)
  let bottom := tPoint stepAxisX (rowY orbitSteps)
  #[Plane.Exact.segment top bottom |>.named "the step number k, one row per step"] ++
    (stepTicks.toArray.map fun k => Plane.Exact.tickAt (tPoint stepAxisX (rowY k)) top bottom) ++
    (stepTicks.toArray.map fun k => Plane.Exact.label s!"{k}" (tPoint stepAxisX (rowY k)) .left) ++
    #[Plane.Exact.label "step k" (tPoint (stepAxisX - rat (1 / 5)) (rowY 12)) .left]

/-- The items of `chordOrbit`. -/
def chordOrbitItems : Array Item :=
  chordOrbitFrame ++ stepAxis ++ (chordRows orbitSteps).mapIdx fun k (w, t) => rowPoint k w t

/-- The orbit of 0 along the chord at the critical radius: the parameters t₀ = 0, t₁, …, t₂₄ of
the points tₖE, one row per step k from the top, each point in the colour of the piece that holds
it, which is the word applied next; above, the three pieces of [−1, 1). Each step adds 2φ − 2
modulo 2. -/
@[figure]
def chordOrbit : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := chordOrbitItems
  info := { title := "The orbit of 0 along the chord" }

end TDCSGFigures
