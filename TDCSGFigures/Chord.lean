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
  Plane.Exact.point leftCentre |>.role leftRole |>.named "the centre −1",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the centre 1",
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
      #[Plane.Exact.point leftCentre |>.role leftRole |>.named "the centre −1",
        Plane.Exact.point rightCentre |>.role rightRole |>.named "the centre 1",
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
    Plane.Exact.tickAt (tPoint (rat 0) axisY) (tPoint (p 0) axisY) (tPoint (p 3) axisY),
    Plane.Exact.tickAt (tPoint (p 3) axisY) (tPoint (p 0) axisY) (tPoint (p 3) axisY),
    Plane.Exact.label "−1" (tPoint (p 0) axisY) .below,
    Plane.Exact.label "1 − φ" (tPoint (p 1) axisY) .below,
    Plane.Exact.label "3 − 2φ" (tPoint (p 2) axisY) .below,
    Plane.Exact.label "0" (tPoint (rat 0) axisY) .below,
    Plane.Exact.label "1" (tPoint (p 3) axisY) .below,
    Plane.Exact.label "t, the point tE of the chord" (tPoint (rat 0) (axisY - rat (3 / 20)))
      .below,
    Plane.Exact.label "k = 0" (tPoint (rat (-1)) (rowY 0)) .left,
    Plane.Exact.label s!"k = {orbitSteps}" (tPoint (rat (-1)) (rowY orbitSteps)) .left]

/-- The items of `chordOrbit`. -/
def chordOrbitItems : Array Item :=
  chordOrbitFrame ++ (chordRows orbitSteps).mapIdx fun k (w, t) => rowPoint k w t

/-- The orbit of 0 along the chord at the critical radius: the parameters t₀ = 0, t₁, …, t₂₄ of
the points tₖE, one row per step from the top, each point in the colour of the piece that holds
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


/-! ### What the figures state -/

/-- What `chordPieces` draws, item for item, and why its records are right. The data are
`E = ζ - ζ²`, the radius `R = √(3 + φ)`, the cuts `(1 - φ)E = -φ⁻¹E` and `(3 - 2φ)E = -φ⁻³E`
(`φ⁻¹ = ζ + ζ⁴`), and the three words. The items are written out in drawing order: the two disks
and their lens (`criticalDisks`, written out), the three pieces with their labels, links to the
theorems that the words translate them, the points with their records, the labels with two
leaders, and the three words written out. The facts hold exactly in `ℚ(√5)`: `|E + 1|² = 3 + φ`
and `|E - 1|² < 3 + φ`, the same for `-E` with the sides exchanged (so `E` and `-E` are on the
lens's boundary); both cuts lie strictly inside both disks; `-φ⁻¹ = 1 - φ` and
`-φ⁻³ = 3 - 2φ` (as elements of `ℤ[ζ₅]`, `φ = 1 + φ⁻¹`); the words are those of
`TDCSG.Five.word₁`, `word₂`, `word₃`, written as below the figure. Not stated: how the builders
and modifiers draw, the layout, the lettering, the style's colour values and the pixels. -/
theorem chordPieces_spec :
    chordEnd = Zeta5.pow 1 - Zeta5.pow 2 ∧ critical = ⟨⟨7 / 2, 1 / 2⟩⟩ ∧
    cutF = -(phiInv * chordEnd) ∧ cutG = -(phiInv * phiInv * phiInv * chordEnd) ∧
    word₁ = [.aInv, .aInv, .bInv, .aInv, .bInv] ∧ word₂ = [.a, .b, .a, .b, .b] ∧
    word₃ = [.a, .b, .a, .bInv, .aInv, .bInv] ∧
    criticalDisks = #[
      Plane.Exact.disk leftCentre critical |>.noFill |>.role leftRole |>.named "the left circle"
        |>.describedBy "the closed disk of radius R = √(3 + φ) about −1",
      Plane.Exact.disk rightCentre critical |>.noFill |>.role rightRole |>.named "the right circle"
        |>.describedBy "the closed disk of radius R = √(3 + φ) about 1",
      Plane.Exact.lens leftCentre rightCentre critical critical |>.role lensRole |>.noOutline
        |>.fillOpacity 0.12 |>.named "the lens"] ∧
    chordPieces.items = criticalDisks ++ #[
    Plane.Exact.segment (-chordEnd) cutF |>.role (pieceRole 1) |>.width 5
      |>.named "the piece [−E, (1 − φ)E] of word 1" |>.declRef `TDCSG.Five.applyWord_word₁,
    Plane.Exact.labelBeside "1" (-chordEnd) cutF |>.role (pieceRole 1),
    Plane.Exact.segment cutF cutG |>.role (pieceRole 2) |>.width 5
      |>.named "the piece [(1 − φ)E, (3 − 2φ)E] of word 2" |>.declRef `TDCSG.Five.applyWord_word₂,
    Plane.Exact.labelBeside "2" cutF cutG |>.role (pieceRole 2),
    Plane.Exact.segment cutG chordEnd |>.role (pieceRole 3) |>.width 5
      |>.named "the piece [(3 − 2φ)E, E] of word 3" |>.declRef `TDCSG.Five.applyWord_word₃,
    Plane.Exact.labelBeside "3" cutG chordEnd |>.role (pieceRole 3),
    Plane.Exact.point leftCentre |>.role leftRole |>.named "the centre −1",
    Plane.Exact.point rightCentre |>.role rightRole |>.named "the centre 1",
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
      |>.declRef `TDCSG.Five.word₃] ∧
    ((chordEnd - leftCentre).normSq == threePlusPhi) = true ∧
    QSqrt.lt (chordEnd - rightCentre).normSq threePlusPhi = true ∧
    ((-chordEnd - rightCentre).normSq == threePlusPhi) = true ∧
    QSqrt.lt (-chordEnd - leftCentre).normSq threePlusPhi = true ∧
    QSqrt.lt (cutF - leftCentre).normSq threePlusPhi = true ∧
    QSqrt.lt (cutF - rightCentre).normSq threePlusPhi = true ∧
    QSqrt.lt (cutG - leftCentre).normSq threePlusPhi = true ∧
    QSqrt.lt (cutG - rightCentre).normSq threePlusPhi = true ∧
    (cutF == (Zeta5.ofInt 1 - (Zeta5.ofInt 1 + phiInv)) * chordEnd) = true ∧
    (cutG == (Zeta5.ofInt 3 - Zeta5.ofInt 2 * (Zeta5.ofInt 1 + phiInv)) * chordEnd) = true ∧
    wordText 1 = "a⁻¹ a⁻¹ b⁻¹ a⁻¹ b⁻¹" ∧ wordText 2 = "a b a b b" ∧
    wordText 3 = "a b a b⁻¹ a⁻¹ b⁻¹" := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves chordPieces chordPieces_spec

/-- What `wordTrace` shows, frame by frame, and why. It is the stepper of `traceFrame 1`,
`traceFrame 2`, `traceFrame 3` with the captions written out. Frame `i` draws the two disks and
their lens, the chord thin, and the segments `[w_k(p), w_k(q)]` of `wordPath i` for
`k = 0, 1, …`: the piece `[p, q]` of word `i` (`k = 0`, dashed), its images after `k` letters, the
last one on the chord; each labelled `k`; and the ends lying on a boundary circle before a letter
(`wordEqualities i`), each recording exactly where it stands relative to both disks and the lens.
The images are written out in the basis `1, ζ, ζ², ζ³`. Before every letter both current ends
lie in the letter's closed disk of radius `R` (`wordChecks`), so the letter turns the whole
segment, as in `TDCSG.Five.applyWord_chord`; the tests that hold with equality are those before
letters 3, 4 of word 1, letters 2, 3 of word 2 and letters 1, 2, 5, 6 of word 3. The last images
are the pieces moved by `(2φ - 2)E` (words 1, 2) and `(2φ - 4)E` (word 3). Not stated: the
layout, the lettering, the style's colour values and the pixels. -/
theorem wordTrace_spec :
    wordTrace = Plane.stepper (traceCaptions.mapIdx fun k c => (c, traceFrame (k + 1))) ∧
    traceCaptions = #[
        "word 1 = a⁻¹ a⁻¹ b⁻¹ a⁻¹ b⁻¹ moves its piece by (2φ − 2)E",
        "word 2 = a b a b b moves its piece by (2φ − 2)E",
        "word 3 = a b a b⁻¹ a⁻¹ b⁻¹ moves its piece by (2φ − 4)E"] ∧
    (wordPath 1 == [(⟨#[0, -1, 1, 0]⟩, ⟨#[-1, 1, -1, 1]⟩), (⟨#[-1, 1, -1, 1]⟩, ⟨#[-2, -1, 0, -2]⟩),
      (⟨#[-2, -1, 0, -2]⟩, ⟨#[1, 1, 1, 2]⟩), (⟨#[3, -1, 1, 2]⟩, ⟨#[-1, -2, -1, -1]⟩),
      (⟨#[-3, 2, -3, -1]⟩, ⟨#[0, 1, -1, 0]⟩), (⟨#[2, -3, 3, -2]⟩, ⟨#[1, -1, 1, -1]⟩)]) = true ∧
    (wordPath 2 == [(⟨#[-1, 1, -1, 1]⟩, ⟨#[-2, 3, -3, 2]⟩), (⟨#[0, -1, 1, 0]⟩, ⟨#[3, -2, 3, 1]⟩),
      (⟨#[1, 2, 1, 1]⟩, ⟨#[-3, 1, -1, -2]⟩), (⟨#[-1, -1, -1, -2]⟩, ⟨#[2, 1, 0, 2]⟩),
      (⟨#[2, 1, 0, 2]⟩, ⟨#[1, -1, 1, -1]⟩), (⟨#[1, -1, 1, -1]⟩, ⟨#[0, 1, -1, 0]⟩)]) = true ∧
    (wordPath 3 == [(⟨#[-2, 3, -3, 2]⟩, ⟨#[0, 1, -1, 0]⟩), (⟨#[3, -2, 3, 1]⟩, ⟨#[-1, -2, -1, -1]⟩),
      (⟨#[-3, 1, -1, -2]⟩, ⟨#[1, 1, 1, 2]⟩), (⟨#[2, 1, 0, 2]⟩, ⟨#[-2, -1, 0, -2]⟩),
      (⟨#[-1, -1, -1, -2]⟩, ⟨#[3, -1, 1, 2]⟩), (⟨#[1, 2, 1, 1]⟩, ⟨#[-3, 2, -3, -1]⟩),
      (⟨#[0, -1, 1, 0]⟩, ⟨#[2, -3, 3, -2]⟩)]) = true ∧
    wordChecks 1 = true ∧ wordChecks 2 = true ∧ wordChecks 3 = true ∧
    (wordEqualities 1).map (·.1) = [2, 3] ∧ (wordEqualities 2).map (·.1) = [1, 2] ∧
    (wordEqualities 3).map (·.1) = [0, 1, 4, 5] ∧
    ((wordPath 1).getLast? == some (-chordEnd + (phiInv + phiInv) * chordEnd,
      cutF + (phiInv + phiInv) * chordEnd)) = true ∧
    ((wordPath 2).getLast? == some (cutF + (phiInv + phiInv) * chordEnd,
      cutG + (phiInv + phiInv) * chordEnd)) = true ∧
    ((wordPath 3).getLast? == some (cutG + (phiInv + phiInv) * chordEnd - Zeta5.ofInt 2 * chordEnd,
      chordEnd + (phiInv + phiInv) * chordEnd - Zeta5.ofInt 2 * chordEnd)) = true := by
  refine ⟨rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves wordTrace wordTrace_spec

/-- What `chordOrbit` draws, item for item, and why. The items are the frame (`chordOrbitFrame`,
written out: the bands of the three pieces, the pieces of `[-1, 1]` with their labels, the end `-1`
in the range and the end `1` not, the axis with ticks at `-1, 1 - φ, 3 - 2φ, 0, 1` and its name,
and the names of the first and last row), then one point per row `k = 0, …, 24` at `(t_k, -k/20)`
(`rowPoint`, written out), in the colour of word `w_k` and recording that it lies in the band of
piece `w_k` and outside the other two. The rows are written out: `t_k = a + b√5` with the word
applied next. The facts hold exactly in `ℚ(√5)`: every `t_k` lies in `[-1, 1)` and in the piece
of its word (`t ≤ 1 - φ` for word 1, `1 - φ < t < 3 - 2φ` for word 2, `t ≥ 3 - 2φ` for word 3),
`t_(k+1) = t_k + 2φ - 2` for words 1, 2 and `t_k + 2φ - 4` for word 3, and the 25 values are
pairwise distinct. Not stated: how the builders and modifiers draw, the layout, the lettering, the
style's colour values and the pixels. -/
theorem chordOrbit_spec :
    orbitSteps = 24 ∧ pieceEnds = #[rat (-1), rat 1 - phi, rat 3 - phi * rat 2, rat 1] ∧
    (∀ k : Nat, rowY k = rat (-(k : Rat) / 20)) ∧ chordRowY = rat (3 / 20) ∧
    axisY = rat (-((orbitSteps : Rat) + 2) / 20) ∧
    (∀ i : Nat, band i = (Plane.Exact.polygon [tPoint pieceEnds[i - 1]! chordRowY,
      tPoint pieceEnds[i]! chordRowY, tPoint pieceEnds[i]! axisY, tPoint pieceEnds[i - 1]! axisY]
      |>.filled |>.noOutline |>.fillOpacity 0.08 |>.role (pieceRole i)
      |>.named s!"the band of piece {i}")) ∧
    (∀ (k w : Nat) (t : QSqrt5), rowPoint k w t =
      (Plane.Exact.point (tPoint t (rowY k)) |>.role (pieceRole w) |>.size 3 |>.halo false
        |>.named s!"t{subscript k} = {phiText t}, word {w} next"
        |>.incident (if w == 1 then .inside else .outside) "the band of piece 1"
        |>.incident (if w == 2 then .inside else .outside) "the band of piece 2"
        |>.incident (if w == 3 then .inside else .outside) "the band of piece 3")) ∧
    chordOrbitFrame = #[band 1, band 2, band 3,
      Plane.Exact.segment (tPoint pieceEnds[0]! chordRowY) (tPoint pieceEnds[1]! chordRowY)
        |>.role (pieceRole 1)
        |>.width 5 |>.named "the piece of word 1, t ≤ 1 − φ" |>.declRef `TDCSG.Five.applyWord_word₁,
      Plane.Exact.segment (tPoint pieceEnds[1]! chordRowY) (tPoint pieceEnds[2]! chordRowY)
        |>.role (pieceRole 2)
        |>.width 5 |>.named "the piece of word 2, 1 − φ < t < 3 − 2φ"
        |>.declRef `TDCSG.Five.applyWord_word₂,
      Plane.Exact.segment (tPoint pieceEnds[2]! chordRowY) (tPoint pieceEnds[3]! chordRowY)
        |>.role (pieceRole 3)
        |>.width 5 |>.named "the piece of word 3, t ≥ 3 − 2φ"
        |>.declRef `TDCSG.Five.applyWord_word₃,
      Plane.Exact.label "1" (tPoint ((pieceEnds[0]! + pieceEnds[1]!) * rat (1 / 2)) chordRowY)
        .above
        |>.role (pieceRole 1),
      Plane.Exact.label "2" (tPoint ((pieceEnds[1]! + pieceEnds[2]!) * rat (1 / 2)) chordRowY)
        .above
        |>.role (pieceRole 2),
      Plane.Exact.label "3" (tPoint ((pieceEnds[2]! + pieceEnds[3]!) * rat (1 / 2)) chordRowY)
        .above
        |>.role (pieceRole 3),
      Plane.Exact.label "word" (tPoint pieceEnds[0]! chordRowY) .left,
      Plane.Exact.point (tPoint pieceEnds[0]! chordRowY)
        |>.named "t = −1, the point −E, in the range",
      Plane.Exact.point (tPoint pieceEnds[3]! chordRowY) |>.marker .ring
        |>.named "t = 1, the point E, not in the range [−1, 1)",
      Plane.Exact.segment (tPoint pieceEnds[0]! axisY) (tPoint pieceEnds[3]! axisY)
        |>.named "the parameter t of the point tE",
      Plane.Exact.tickAt (tPoint pieceEnds[0]! axisY)
        (tPoint pieceEnds[0]! axisY) (tPoint pieceEnds[3]! axisY),
      Plane.Exact.tickAt (tPoint pieceEnds[1]! axisY)
        (tPoint pieceEnds[0]! axisY) (tPoint pieceEnds[3]! axisY),
      Plane.Exact.tickAt (tPoint pieceEnds[2]! axisY)
        (tPoint pieceEnds[0]! axisY) (tPoint pieceEnds[3]! axisY),
      Plane.Exact.tickAt (tPoint (rat 0) axisY)
        (tPoint pieceEnds[0]! axisY) (tPoint pieceEnds[3]! axisY),
      Plane.Exact.tickAt (tPoint pieceEnds[3]! axisY)
        (tPoint pieceEnds[0]! axisY) (tPoint pieceEnds[3]! axisY),
      Plane.Exact.label "−1" (tPoint pieceEnds[0]! axisY) .below,
      Plane.Exact.label "1 − φ" (tPoint pieceEnds[1]! axisY) .below,
      Plane.Exact.label "3 − 2φ" (tPoint pieceEnds[2]! axisY) .below,
      Plane.Exact.label "0" (tPoint (rat 0) axisY) .below,
      Plane.Exact.label "1" (tPoint pieceEnds[3]! axisY) .below,
      Plane.Exact.label "t, the point tE of the chord" (tPoint (rat 0) (axisY - rat (3 / 20)))
        .below,
      Plane.Exact.label "k = 0" (tPoint (rat (-1)) (rowY 0)) .left,
      Plane.Exact.label s!"k = {orbitSteps}" (tPoint (rat (-1)) (rowY orbitSteps)) .left] ∧
    chordOrbit.items =
      chordOrbitFrame ++ (chordRows orbitSteps).mapIdx (fun k (w, t) => rowPoint k w t) ∧
    chordRows 24 = #[(3, ⟨0, 0⟩), (1, ⟨-3, 1⟩), (3, ⟨-4, 2⟩), (2, ⟨-7, 3⟩), (3, ⟨-8, 4⟩),
      (3, ⟨-11, 5⟩), (2, ⟨-14, 6⟩), (3, ⟨-15, 7⟩), (3, ⟨-18, 8⟩), (1, ⟨-21, 9⟩), (3, ⟨-22, 10⟩),
      (2, ⟨-25, 11⟩), (3, ⟨-26, 12⟩), (3, ⟨-29, 13⟩), (1, ⟨-32, 14⟩), (3, ⟨-33, 15⟩),
      (3, ⟨-36, 16⟩), (1, ⟨-39, 17⟩), (3, ⟨-40, 18⟩), (2, ⟨-43, 19⟩), (3, ⟨-44, 20⟩),
      (3, ⟨-47, 21⟩), (1, ⟨-50, 22⟩), (3, ⟨-51, 23⟩), (2, ⟨-54, 24⟩)] ∧
    (chordRows 24).all (fun (w, t) => QSqrt.le (rat (-1)) t && QSqrt.lt t (rat 1) &&
      (if w == 1 then QSqrt.le t (rat 1 - phi) else if w == 2 then
        QSqrt.lt (rat 1 - phi) t && QSqrt.lt t (rat 3 - phi * rat 2)
        else QSqrt.le (rat 3 - phi * rat 2) t)) = true ∧
    ((List.range 24).all fun k =>
      let (w, t) := (chordRows 24)[k]!
      (chordRows 24)[k + 1]!.2 ==
        t + phi * rat 2 - (if w == 3 then rat 4 else rat 2)) = true ∧
    ((chordRows 24).map (phiForm ·.2)).toList.eraseDups.length = 25 := by
  refine ⟨rfl, rfl, fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ _ _ => rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves chordOrbit chordOrbit_spec

end TDCSGFigures
