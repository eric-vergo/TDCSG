/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data
import TDCSGFigures.Style

/-!
# The figure of the front page

`criticalChord`: the two closed disks of radius `R = √(3 + φ)` about `-1` and `1`, the lens they
share, and the chord from `-E` to `E` (`E = ζ - ζ²`) through `0` in the three pieces that the
three words of chapter 3 move. `E` lies on the left circle and `-E` on the right one; the circles
cross at `±(ζ - ζ⁴)`. Every point is exact in `ℤ[ζ₅]` and every incidence the figure records is
decided exactly in `ℚ(√5)` (`criticalChord_spec`).
-/

namespace TDCSGFigures.Front

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- The left circle: the closed disk of radius `R` about `-1`, outlined. -/
def leftDisk : Item :=
  Plane.Exact.disk leftCentre critical |>.noFill |>.role leftRole |>.named "the left circle"
    |>.describedBy "the closed disk of radius R = √(3 + φ) about −1"

/-- The right circle: the closed disk of radius `R` about `1`, outlined. -/
def rightDisk : Item :=
  Plane.Exact.disk rightCentre critical |>.noFill |>.role rightRole |>.named "the right circle"
    |>.describedBy "the closed disk of radius R = √(3 + φ) about 1"

/-- The lens, the intersection of the two disks, a filled region of its own. -/
def lens : Item :=
  Plane.Exact.lens leftCentre rightCentre critical critical |>.role lensRole |>.noOutline
    |>.fillOpacity 0.12 |>.named "the lens"

/-- The radius of the left disk from `-1` to the point `spokeEnd` of its circle, linked to the
theorem that `R` is the critical radius. -/
def radius : Item :=
  Plane.Exact.segment leftCentre spokeEnd |>.role leftRole |>.width 1.5 |>.dashed
    |>.named "a radius R of the left disk"
    |>.declRef `TDCSG.CriticalRadius.criticalRadius_five

/-- The piece of the chord that word `i` moves, from `a` to `b`, linked to the word. -/
def piece (i : Nat) (a b : Zeta5) (word : Lean.Name) : Item :=
  Plane.Exact.segment a b |>.role (pieceRole i) |>.width 5 |>.named s!"the piece of word {i}"
    |>.declRef word

/-- The label `i` of the piece that word `i` moves, beside it. -/
def pieceLabel (i : Nat) (a b : Zeta5) : Item :=
  Plane.Exact.labelBeside s!"{i}" a b |>.role (pieceRole i)

/-- The point `E`, on the left circle (`|E + 1|² = 3 + φ`) and so on the lens's boundary, linked
to that equation. -/
def pointE : Item :=
  Plane.Exact.point chordEnd |>.role leftRole |>.named "E" |>.incident .on "the left circle"
    |>.incident .on "the lens" |>.declRef `TDCSG.Five.norm_embed_pointE_add_one_sq

/-- The point `-E`, on the right circle and so on the lens's boundary. -/
def pointNegE : Item :=
  Plane.Exact.point (-chordEnd) |>.role rightRole |>.named "−E"
    |>.incident .on "the right circle" |>.incident .on "the lens"

/-- A crossing point `c` of the two circles, a corner of the lens. -/
def crossingPoint (c : Zeta5) (name : String) : Item :=
  Plane.Exact.point c |>.named name |>.incident .on "the left circle"
    |>.incident .on "the right circle" |>.incident .on "the lens"

/-- The items, in drawing order. -/
def items : Array Item := #[
  leftDisk, rightDisk, lens, radius,
  Plane.Exact.labelBeside "R = √(3 + φ)" leftCentre spokeEnd |>.role leftRole,
  piece 1 (-chordEnd) firstCut `TDCSG.Five.word₁, pieceLabel 1 (-chordEnd) firstCut,
  piece 2 firstCut secondCut `TDCSG.Five.word₂, pieceLabel 2 firstCut secondCut,
  piece 3 secondCut chordEnd `TDCSG.Five.word₃, pieceLabel 3 secondCut chordEnd,
  Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1",
  Plane.Exact.point origin |>.named "0" |>.incident .on "the piece of word 3",
  pointE, pointNegE,
  crossingPoint crossing "ζ − ζ⁴", crossingPoint (-crossing) "ζ⁴ − ζ",
  Plane.Exact.label "−1" leftCentre .auto |>.role leftRole,
  Plane.Exact.label "+1" rightCentre .auto |>.role rightRole,
  Plane.Exact.label "0" origin .auto,
  Plane.Exact.label "E" chordEnd .auto |>.role leftRole |>.italic,
  Plane.Exact.label "−E" (-chordEnd) .auto |>.role rightRole,
  Plane.Exact.label "ζ − ζ⁴" crossing .auto,
  Plane.Exact.label "ζ⁴ − ζ" (-crossing) .auto,
  Plane.Exact.label "left disk" ((-2 : Rat), (-9 / 10 : Rat)) |>.role leftRole,
  Plane.Exact.label "right disk" ((2 : Rat), (9 / 10 : Rat)) |>.role rightRole,
  Plane.Exact.label "lens" ((0 : Rat), (-11 / 10 : Rat)) |>.role lensRole]

end TDCSGFigures.Front

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact Front

/-- Two closed disks of radius R = √(3 + φ) about −1 and 1, outlined, their lens filled, and the
chord from −E to E through 0 in the three pieces the three words move. E lies on the left circle
and −E on the right circle; the circles cross at ζ − ζ⁴ and ζ⁴ − ζ. -/
@[figure]
def criticalChord : Plane.Figure where
  width := figureWidth
  narrowWidth := some narrowWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := Front.items
  info := { title := "The critical chord between two closed disks" }

/-! ### What the orbits of zero share (`orbitRadius`, in `TDCSGFigures.OrbitLoop`) -/

/-- The house style for orbits: markers without the ring of background colour, since the many
orbit points are drawn without halos. -/
def orbitStyle : Style := { houseStyle with plane := { houseStyle.plane with markerRing := 0 } }

/-- A point recording where it stands relative to the two disks and their lens. -/
def withSides (it : Item) (l r : Side) : Item :=
  it |>.incident l.incidence "the left circle" |>.incident r.incidence "the right circle"
    |>.incident (l.lens r).incidence "the lens"

end TDCSGFigures
