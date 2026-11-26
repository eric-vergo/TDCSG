/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.Early
import TDCSGFigures.Style
import TDCSGFigures.Data.Turns
import TDCSGFigures.Data.Moves
import TDCSGFigures.WordStrip

/-!
# The figures of chapter 3, the chord and its three words

* `chordPieces`: the two closed disks of radius `R = √(3 + φ)` about `∓1`, their lens, and the
  chord from `-E` to `E` (`E = ζ - ζ²`) cut at `(1 - φ) E` and `(3 - 2φ) E` into the pieces of
  the three words, each word written out.
* `wordLoop1`, `wordLoop2`, `wordLoop3`: three looping animations (illustrations), one per word,
  in which an image of the word's piece turns about `−1` or `+1`, a fifth of a turn for each
  letter, until it lies on the chord again; the key figures are the images after `0, 1, …`
  letters (`wordPath`), the centre of the last turn is circled, and the ends that lie on a
  boundary circle (a disk test that holds with equality, `wordEqualities`) are marked while the
  image rests there.
* `chordOrbit`: an animation of the orbit of `0` along the chord, `t₀ = 0, t₁, …, t₂₄` on the
  parameter line `t ∈ [-1, 1)` of the points `tE`, one row per step: a point hops from row `k` at
  `t_k` to row `k + 1` at `t_{k+1}`, one hop per return, and leaves behind it the point of row `k`
  in the colour of the piece that holds it (the word applied next); after twelve hops the other
  rows are shown at once. Its last key frame is the figure of the first 24 returns
  (`chordOrbitFinal`), which keeps its linked theorem.

Every point is exact in `ℤ[ζ₅]` or `ℚ(√5)²`, every recorded incidence is decided exactly in
`ℚ(√5)`, and every declared move is checked exactly (`wordArrives`, `orbitArrives`). The
statements are `chordPieces_spec`, `chordOrbit_spec`, `chordOrbit_keys` and, for the three
loops, `wordLoop_figures`, `wordLoop_keys` and `wordLoop_captions`.
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

/-- The name of the centre `c`, `−1` or `+1`. -/
def centreName (c : Zeta5) : String := if c == leftCentre then "−1" else "+1"

/-- The piece of word `i` as text. -/
def pieceText : Nat → String
  | 1 => "[−E, (1 − φ)E]"
  | 2 => "[(1 − φ)E, (3 − 2φ)E]"
  | _ => "[(3 − 2φ)E, E]"

/-- How far word `i` moves its piece along the chord, as text. -/
def shiftText (i : Nat) : String := if i == 3 then "(2φ − 4)E" else "(2φ − 2)E"

/-- The turn declared between key `k` and key `k + 1` of word `i`: about the centre of letter
`k + 1`, by `-1/5` of a full turn for `a` and `b` (clockwise), `1/5` for their inverses. -/
def wordTurn (i k : Nat) : ExactTurn :=
  let l := (wordPiece i).1.getD k .a
  ⟨ZetaFrac.ofZeta l.centre, if l.turn == zeta 1 then 1 / 5 else -1 / 5⟩

/-- Whether the declared turn of every step of word `i` (`wordTurn`, applied exactly in `ℚ(ζ₅)`)
carries both ends of the image of key `k` (`wordPath i`) onto those of key `k + 1`. -/
def wordArrives (i : Nat) : Bool :=
  let path := wordPath i
  (List.range (wordPiece i).1.length).all fun k =>
    let (p, q) := path.getD k (origin, origin)
    let (p', q') := path.getD (k + 1) (origin, origin)
    let lands := fun (a b : Zeta5) =>
      ((wordTurn i k).apply (ZetaFrac.ofZeta a)).any (ZetaFrac.same · (ZetaFrac.ofZeta b))
    lands p p' && lands q q'

/-- The radius of the circle that marks the centre of the last turn. -/
def pivotRadius : Rat := 1 / 5

/-- The first key of the run of keys of word `i` whose last turn is about the same centre as at
key `k` (`k ≥ 1`): it names the circle that marks that centre, so that the circle stays while
consecutive letters turn about one centre and a new run gets a new one. -/
def pivotRunStart (i : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | k + 2 =>
    let w := (wordPiece i).1
    if ((w.getD k .a).centre == (w.getD (k + 1) .a).centre) then pivotRunStart i (k + 1)
    else k + 2

/-- The image of the piece of word `i` after `k` letters, `(wordPath i)[k]`: the actor
`"segment"`. -/
def wordSegment (i k : Nat) : Item :=
  let (p, q) := (wordPath i).getD k (origin, origin)
  Plane.Exact.segment p q |>.role (pieceRole i) |>.width 4
    |>.named s!"the image of the piece of word {i}" |>.withId "segment"

/-- The circle about the centre of the turn declared before key `k` of word `i` (`wordTurn`), from
key `1` on: the actor `"pivot-<first key of its run>"`. -/
def wordPivot (i k : Nat) : Array Item :=
  if k == 0 then #[]
  else
    let c := (wordTurn i (k - 1)).centre
    let left := ZetaFrac.same c (ZetaFrac.ofZeta leftCentre)
    #[Plane.Exact.circle c pivotRadius |>.role (if left then leftRole else rightRole)
      |>.width 2 |>.named s!"a circle about the center {if left then "−1" else "+1"} of the last \
        turn" |>.withId s!"pivot-{pivotRunStart i k}"]

/-- The ends of the image of key `k` of word `i` that lie on the circle of the next letter
(`wordEqualities i`): the actors `"contact-<m>"`. -/
def wordContacts (i k : Nat) : Array Item :=
  ((wordEqualities i).zipIdx.filter fun ((j, _, _), _) => j == k).toArray.map
    fun ((j, z, isLeft), m) =>
      recordSides threePlusPhi z (Plane.Exact.point z
        |>.role (if isLeft then leftRole else rightRole)
        |>.named s!"an end on {if isLeft then "the left" else "the right"} circle before \
          letter {j + 1}") |>.withId s!"contact-{m}"

/-- Where the word strip of word `i` is written (`wordLoopWith … true`): its centre, height and
gap. -/
def wordStripAt : Rat × Rat × Rat := (1 / 4, -14 / 5, 11 / 20)

/-- The mark of the word strip at key `k` of word `i` (`strip`): under the letter that turned the
image into key `k`, from key `1` on. -/
def wordStripMark (i k : Nat) (strip : Bool) : Array Item :=
  if !strip || k == 0 then #[]
  else
    let (cx, y, gap) := wordStripAt
    #[stripMark (wordPiece i).1.length (k - 1) cx y gap (pieceRole i)]

/-- The actors of key `k` of word `i`, in drawing order: the image (`wordSegment`), the circle of
the last turn (`wordPivot`), the marked ends (`wordContacts`) and, with the word strip, its
mark. -/
def wordActors (i k : Nat) (strip : Bool := false) : Array Item :=
  #[wordSegment i k] ++ wordPivot i k ++ wordContacts i k ++ wordStripMark i k strip

/-- The items of word `i` that every key draws, under its actors: the disks and their lens, the
chord thin and the piece of the word dashed. -/
def wordUnder (i : Nat) : Array Item :=
  let (_, p, q) := wordPiece i
  criticalDisks ++
    #[Plane.Exact.segment (-chordEnd) chordEnd |>.faint |>.named "the chord from −E to E",
      Plane.Exact.segment p q |>.role (pieceRole i) |>.width 2 |>.dashed #[9, 6]
        |>.named s!"the piece {pieceText i} of word {i}"]

/-- The items of word `i` that every key draws, over its actors: the centres, and below the disks
which centre each letter turns about and the word, written out, or, with the word strip, letter
by letter. The centres carry no labels of their own: the circle of the last turn lies about them,
and a label beside a centre would overlap the chord, the lens or the other circle at the narrow
width. -/
def wordOver (i : Nat) (strip : Bool := false) : Array Item :=
  let w := (wordPiece i).1
  let (cx, y, gap) := wordStripAt
  #[Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1",
    Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1",
    Plane.Exact.label "a, a⁻¹: about −1" ((-3 / 2 : Rat), (-23 / 10 : Rat)) |>.role leftRole,
    Plane.Exact.label "b, b⁻¹: about +1" ((3 / 2 : Rat), (-23 / 10 : Rat)) |>.role rightRole] ++
  if strip then
    #[Plane.Exact.label s!"word {i}:" (stripX w.length 0 cx gap - gap * 3 / 5, y) .left
      |>.role (pieceRole i) |>.declRef (wordDecl i)] ++
      stripLetters (w.map Letter.text) [] cx y gap (pieceRole i)
  else
    #[Plane.Exact.label s!"word {i}: {wordText i}" ((0 : Rat), (-14 / 5 : Rat))
      |>.role (pieceRole i) |>.declRef (wordDecl i)]

/-- The caption of key `k` of word `i`, without a counter (a page numbers the keys itself): the
piece and the word at the start, then which letter turned the image, which way and about which
centre; the ends that lie on the circle of the next letter; and, at the last key, the landing. -/
def wordCaption (i k : Nat) : String :=
  let (w, _, _) := wordPiece i
  let n := w.length
  let ends := ((wordEqualities i).filter (·.1 == k)).map fun (_, _, isLeft) =>
    if isLeft then "left" else "right"
  let contact := match ends with
    | [] => ""
    | [c] => s!" One end lies on the {c} circle (dot): the disk test of letter {k + 1} holds with \
        equality there."
    | cs => s!" Both ends lie on the {cs.headD "left"} circle (dots): the disk test of letter \
        {k + 1} holds with equality there."
  let body :=
    if k == 0 then
      s!"The piece {pieceText i} of the chord (dashed) and word {i} = {wordText i}, its letters \
        applied from left to right; a copy of the piece is turned."
    else
      let l := w.getD (k - 1) .a
      let way := if l.turn == zeta 1 then "counterclockwise" else "clockwise"
      s!"Letter {k}, {l.text}, turns the image a fifth of a turn {way} about \
        {centreName l.centre} (circled)."
  let landing := if k == n then s!" The image lies on the chord again: the piece moved by \
      {shiftText i}." else ""
  body ++ contact ++ landing

/-- Key `k` of word `i`: the disks, the lens, the chord and the piece; the image after `k`
letters with its marks; the centres and the word. -/
def wordKey (i k : Nat) (strip : Bool := false) : Plane.Figure :=
  { width := figureWidth
    padding := 16
    style := houseStyle
    checks := .fail
    items := wordUnder i ++ wordActors i k strip ++ wordOver i strip
    info := { title := wordCaption i k } }

/-- The ids of the actors of key `k` of word `i`. -/
def wordActorIds (i k : Nat) (strip : Bool := false) : Array String :=
  (wordActors i k strip).filterMap fun it => match it with
    | .shape _ _ info | .group _ info => if info.id.isEmpty then none else some info.id

/-- The actors other than the image that appear and vanish between key `k` and key `k + 1` of
word `i`: the circle of the last turn, the marked ends and the mark of the word strip. -/
def wordFades (i k : Nat) (strip : Bool := false) : Array (String × Move) :=
  let before := wordActorIds i k strip
  let after := wordActorIds i (k + 1) strip
  (after.filter (· != "segment") |>.filter (!before.contains ·)).map (·, Move.appear) ++
    (before.filter (· != "segment") |>.filter (!after.contains ·)).map (·, Move.vanish)

/-- The moves from key `k` to key `k + 1` of word `i`: the image turns by the declared turn
`wordTurn i k`, and the other actors appear and vanish with the keys that show them
(`wordFades`). -/
def wordStep (i k : Nat) (strip : Bool := false) : MotionStep :=
  let t := wordTurn i k
  { moves := #[("segment", Plane.Exact.turnAbout t.centre t.turns)] ++ wordFades i k strip }

/-- Whether, with the word strip, key `k` of word `i` shows exactly the mark under letter `k`
(none at key `0`). -/
def wordStripMarks (i : Nat) : Bool :=
  (List.range ((wordPiece i).1.length + 1)).all fun k =>
    stripIds (wordActors i k true) == if k == 0 then [] else [s!"strip-{k - 1}"]

/-- The keys of the loop of word `i`: `wordKey i k` for `k = 0, …, |w|`. -/
def wordLoopKeys (i : Nat) (strip : Bool) : Array Plane.Figure :=
  ((List.range ((wordPiece i).1.length + 1)).map (wordKey i · strip)).toArray

/-- The steps of the loop of word `i`: `wordStep i k` for `k = 0, …, |w| - 1`. -/
def wordLoopSteps (i : Nat) (strip : Bool) : Array MotionStep :=
  ((List.range (wordPiece i).1.length).map (wordStep i · strip)).toArray

/-- The loop of word `i` (`1`, `2` or `3`) at the critical radius, as a picture of one panel with
a narrow rendition: the image of its piece turned letter by letter until it lies on the chord
again, in `motionPacing`; with the word strip when `strip`. -/
def wordLoopWith (i : Nat) (strip : Bool) : MotionPanels :=
  let n := (wordPiece i).1.length
  { panels := #[{ motion := { keys := wordLoopKeys i strip, steps := wordLoopSteps i strip } }]
    captions := ((List.range (n + 1)).map (wordCaption i)).toArray
    pacing := motionPacing
    info := { title := s!"Word {i} carries its piece back into the chord"
              description := s!"The closed disks of radius R = √(3 + φ) about −1 and 1, their \
                lens and the chord from −E to E. The piece {pieceText i} of word {i} stays, \
                dashed; a copy of it turns a fifth of a turn about −1 or +1 for each letter of \
                {wordText i}, clockwise for a and b, counterclockwise for their inverses, until \
                it lies on the chord again, the piece moved by {shiftText i}. A small circle marks \
                the center of the last turn, and a dot each end that lies on a boundary circle, \
                where the next letter's disk test holds with equality." }
    checks := .fail
    width := figureWidth
    narrowWidth := some narrowWidth }

/-- The loop of word `i`, as the site shows it: without the word strip. -/
def wordLoop (i : Nat) : MotionPanels := wordLoopWith i false

/-- Word 1, `a⁻¹ a⁻¹ b⁻¹ a⁻¹ b⁻¹`, carries the piece `[−E, (1 − φ)E]` back into the chord, moved
by `(2φ − 2)E`: an image of the piece turns a fifth of a turn about `−1` or `+1` per letter. -/
@[figure illustration]
def wordLoop1 : MotionPanels := wordLoop 1

/-- Word 2, `a b a b b`, carries the piece `[(1 − φ)E, (3 − 2φ)E]` back into the chord, moved by
`(2φ − 2)E`: an image of the piece turns a fifth of a turn about `−1` or `+1` per letter. -/
@[figure illustration]
def wordLoop2 : MotionPanels := wordLoop 2

/-- Word 3, `a b a b⁻¹ a⁻¹ b⁻¹`, carries the piece `[(3 − 2φ)E, E]` back into the chord, moved
by `(2φ − 4)E`: an image of the piece turns a fifth of a turn about `−1` or `+1` per letter. -/
@[figure illustration]
def wordLoop3 : MotionPanels := wordLoop 3

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

/-- The point of row `k` (actor `"row-<k>"`): `t_k`, in the colour of the piece holding it. -/
def rowPoint (k : Nat) (w : Nat) (t : QSqrt5) : Item :=
  Plane.Exact.point (tPoint t (rowY k)) |>.role (pieceRole w) |>.size 3 |>.halo false
    |>.named s!"t{subscript k} = {phiText t}, word {w} next"
    |>.incident (if w == 1 then .inside else .outside) "the band of piece 1"
    |>.incident (if w == 2 then .inside else .outside) "the band of piece 2"
    |>.incident (if w == 3 then .inside else .outside) "the band of piece 3"
    |>.withId s!"row-{k}"

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

/-- The figure of the orbit of 0 along the chord at the critical radius, the last key frame of
`chordOrbit`: the parameters t₀ = 0, t₁, …, t₂₄ of the points tₖE, one row per step k from the
top, each point in the colour of the piece that holds it, which is the word applied next; above,
the three pieces of [−1, 1). Each step adds 2φ − 2 modulo 2. -/
def chordOrbitFinal : Plane.Figure where
  width := figureWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := chordOrbitItems
  info := { title := "The orbit of 0 along the chord" }

/-- The number of returns the animation shows one by one; the rows after them appear at once. -/
def orbitHops : Nat := 12

/-- The point that hops (actor `"hop"`), at row `k`, on `t_k`. -/
def orbitHopper (k : Nat) : Item :=
  Plane.Exact.point (tPoint ((chordRows orbitSteps).getD k (0, rat 0)).2 (rowY k)) |>.size 5
    |>.named "the point tE of the orbit, one return per hop" |>.withId "hop"

/-- The items of key `k ≤ orbitHops` of `chordOrbit`: the frame, the axis of steps, the rows before
row `k`, and the point that hops at row `k`. -/
def orbitKeyItems (k : Nat) : Array Item :=
  chordOrbitFrame ++ stepAxis ++
    ((chordRows orbitSteps).extract 0 k).mapIdx (fun j (w, t) => rowPoint j w t) ++
    #[orbitHopper k]

/-- How word `w` moves the parameter, as text. -/
def orbitShiftText (w : Nat) : String := if w == 3 then "2φ − 4" else "2φ − 2"

/-- The caption of key `k` of `chordOrbit`: at the start, the orbit and the word applied first;
after return `k ≤ orbitHops`, the word that moved the point, by how much, the new parameter and
the word applied next; at the last key, the rows shown at once. -/
def orbitCaption (k : Nat) : String :=
  let rows := chordRows orbitSteps
  let (w, t) := rows.getD k (0, rat 0)
  if k == 0 then
    s!"The orbit of 0 along the chord at the critical radius: the parameter t of the point tE, \
      −1 ≤ t < 1, one row per return k, from the top. t₀ = 0 lies in piece {w}: word {w} \
      applies next."
  else if k ≤ orbitHops then
    let w' := (rows.getD (k - 1) (0, rat 0)).1
    s!"Return {k}: word {w'} moved the point by {orbitShiftText w'}, to \
      t{subscript k} = {phiText t}, in piece {w}: word {w} applies next."
  else
    s!"The returns t₀, …, t₂₄, the last {orbitSteps - orbitHops} shown at once. Each point lies in \
      the band of the word applied next, which adds 2φ − 2 modulo 2; the rotation is \
      irrational, so the points never repeat."

/-- Key `k` of `chordOrbit`: the items `orbitKeyItems k` in the frame of `chordOrbitFinal` for
`k ≤ orbitHops`, the figure `chordOrbitFinal` after. -/
def orbitKey (k : Nat) : Plane.Figure :=
  if orbitHops < k then chordOrbitFinal
  else { chordOrbitFinal with items := orbitKeyItems k, info := { title := orbitCaption k } }

/-- The declared moves of step `k` of `chordOrbit`: for `k < orbitHops`, the point hops from
`(t_k, -k/20)` to `(t_{k+1}, -(k+1)/20)`, a slide by `(t_{k+1} - t_k, -1/20)`, and leaves the
point of row `k` behind; at step `orbitHops` it vanishes and the rows from `orbitHops` on
appear. -/
def orbitMoves (k : Nat) : List (String × ExactMove (QSqrt5 × QSqrt5)) :=
  let rows := chordRows orbitSteps
  if k < orbitHops then
    [("hop", .slide ((rows.getD (k + 1) (0, rat 0)).2 - (rows.getD k (0, rat 0)).2,
        rowY (k + 1) - rowY k)), (s!"row-{k}", .appear)]
  else
    [("hop", .vanish)] ++ (List.range (orbitSteps + 1 - orbitHops)).map fun j =>
      (s!"row-{orbitHops + j}", .appear)

/-- The exact anchors of the actors of key `k` of `chordOrbit`: the points of the rows shown and,
up to key `orbitHops`, the point that hops. -/
def orbitActors (k : Nat) : List (ExactActor (QSqrt5 × QSqrt5)) :=
  let rows := chordRows orbitSteps
  let shown := if k ≤ orbitHops then k else orbitSteps + 1
  ((List.range shown).map fun j => ⟨s!"row-{j}", [tPoint (rows.getD j (0, rat 0)).2 (rowY j)]⟩) ++
    (if k ≤ orbitHops then [⟨"hop", [tPoint (rows.getD k (0, rat 0)).2 (rowY k)]⟩] else [])

/-- Whether every declared move of `chordOrbit` carries the actors of one key onto those of the
next, exactly in `ℚ(√5)²`. -/
def orbitArrives : Bool := allArrive (orbitHops + 1) orbitMoves orbitActors

/-- The orbit of 0 along the chord at the critical radius: a point hops from row k at tₖ to row
k + 1 at tₖ₊₁, one return per hop, leaving each row's point in the colour of the word applied
next; after twelve hops the other rows up to t₂₄ appear. The last key frame is the figure of the
first 24 returns, `chordOrbitFinal`. -/
@[figure]
def chordOrbit : MotionPanels where
  panels := #[{ motion := { keys := ((List.range (orbitHops + 2)).map orbitKey).toArray,
                            steps := ((List.range (orbitHops + 1)).map fun k =>
                              exactStep (orbitMoves k)).toArray } }]
  captions := ((List.range (orbitHops + 2)).map orbitCaption).toArray
  pacing := motionPacing
  timing := ((List.range (orbitHops + 1)).map fun k => moveTiming (orbitMoves k)).toArray
  info := { title := "The orbit of 0 along the chord"
            description := "The parameter line −1 ≤ t < 1 of the points tE of the chord, cut \
              into the pieces of the three words, and below it one row per return k. A point \
              hops from t₀ = 0 down the rows, each hop one return: it moves by 2φ − 2 modulo 2 \
              and leaves behind a point in the colour of the word applied next. After twelve \
              hops the rows up to t₂₄ appear at once." }
  checks := .fail
  poster := orbitHops + 1
  width := figureWidth
  narrowWidth := some narrowWidth

end TDCSGFigures
