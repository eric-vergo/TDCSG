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
  Plane.Exact.point leftCentre |>.role leftRole |>.named "the centre −1",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the centre 1",
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

/-- What `criticalChord` draws, item for item, and why its records are right. The data are
`E = ζ - ζ²`, the crossing point `ζ - ζ⁴`, the centres `-1` and `1`, the radius
`R = √(3 + φ)` (`3 + φ = 7/2 + √5/2`), `φ⁻¹ = ζ + ζ⁴`, the cuts `-φ⁻¹ E = (1 - φ) E` and
`-φ⁻³ E = (3 - 2φ) E` of the chord, and the point `spokeEnd = -1 + (E + 1) ζ²` that ends the
drawn radius. The items are written out in drawing order, each with its colour (a role or the
ink), its title, its width and dashes, its link to a Lean declaration and the incidences it
records. The records hold exactly in `ℚ(√5)`: `|E + 1|² = 3 + φ` and `|E - 1|² < 3 + φ` (`E` is on
the left circle and inside the right disk, so on the lens's boundary), the same for `-E` with the
sides exchanged, `|±(ζ - ζ⁴) ∓ 1|² = 3 + φ` for both crossing points and both circles,
`|spokeEnd + 1|² = 3 + φ`; `φ⁻¹` is real and between 0 and 1, so the cuts lie between `-E` and
`0` in this order and the third piece passes through `0`. Not stated: how the builders and
modifiers draw, the layout, the lettering, the style's colour values and the pixels. -/
theorem criticalChord_spec :
    chordEnd = Zeta5.pow 1 - Zeta5.pow 2 ∧ crossing = Zeta5.pow 1 - Zeta5.pow 4 ∧
    leftCentre = Zeta5.ofInt (-1) ∧ rightCentre = Zeta5.ofInt 1 ∧ origin = Zeta5.zero ∧
    critical = ⟨⟨7 / 2, 1 / 2⟩⟩ ∧ phiInv = Zeta5.pow 1 + Zeta5.pow 4 ∧
    firstCut = -(phiInv * chordEnd) ∧ secondCut = -(phiInv * phiInv * phiInv * chordEnd) ∧
    spokeEnd = leftCentre + (chordEnd - leftCentre) * Zeta5.pow 2 ∧
    criticalChord.items = #[
      Plane.Exact.disk leftCentre critical |>.noFill |>.role "left" |>.named "the left circle"
        |>.describedBy "the closed disk of radius R = √(3 + φ) about −1",
      Plane.Exact.disk rightCentre critical |>.noFill |>.role "right"
        |>.named "the right circle" |>.describedBy "the closed disk of radius R = √(3 + φ) about 1",
      Plane.Exact.lens leftCentre rightCentre critical critical |>.role "lens" |>.noOutline
        |>.fillOpacity 0.12 |>.named "the lens",
      Plane.Exact.segment leftCentre spokeEnd |>.role "left" |>.width 1.5 |>.dashed
        |>.named "a radius R of the left disk"
        |>.declRef `TDCSG.CriticalRadius.criticalRadius_five,
      Plane.Exact.labelBeside "R = √(3 + φ)" leftCentre spokeEnd |>.role "left",
      Plane.Exact.segment (-chordEnd) firstCut |>.role "piece1" |>.width 5
        |>.named "the piece of word 1" |>.declRef `TDCSG.Five.word₁,
      Plane.Exact.labelBeside "1" (-chordEnd) firstCut |>.role "piece1",
      Plane.Exact.segment firstCut secondCut |>.role "piece2" |>.width 5
        |>.named "the piece of word 2" |>.declRef `TDCSG.Five.word₂,
      Plane.Exact.labelBeside "2" firstCut secondCut |>.role "piece2",
      Plane.Exact.segment secondCut chordEnd |>.role "piece3" |>.width 5
        |>.named "the piece of word 3" |>.declRef `TDCSG.Five.word₃,
      Plane.Exact.labelBeside "3" secondCut chordEnd |>.role "piece3",
      Plane.Exact.point leftCentre |>.role "left" |>.named "the centre −1",
      Plane.Exact.point rightCentre |>.role "right" |>.named "the centre 1",
      Plane.Exact.point origin |>.named "0" |>.incident .on "the piece of word 3",
      Plane.Exact.point chordEnd |>.role "left" |>.named "E" |>.incident .on "the left circle"
        |>.incident .on "the lens" |>.declRef `TDCSG.Five.norm_embed_pointE_add_one_sq,
      Plane.Exact.point (-chordEnd) |>.role "right" |>.named "−E"
        |>.incident .on "the right circle" |>.incident .on "the lens",
      Plane.Exact.point crossing |>.named "ζ − ζ⁴" |>.incident .on "the left circle"
        |>.incident .on "the right circle" |>.incident .on "the lens",
      Plane.Exact.point (-crossing) |>.named "ζ⁴ − ζ" |>.incident .on "the left circle"
        |>.incident .on "the right circle" |>.incident .on "the lens",
      Plane.Exact.label "−1" leftCentre .auto |>.role "left",
      Plane.Exact.label "+1" rightCentre .auto |>.role "right",
      Plane.Exact.label "0" origin .auto,
      Plane.Exact.label "E" chordEnd .auto |>.role "left" |>.italic,
      Plane.Exact.label "−E" (-chordEnd) .auto |>.role "right",
      Plane.Exact.label "ζ − ζ⁴" crossing .auto,
      Plane.Exact.label "ζ⁴ − ζ" (-crossing) .auto,
      Plane.Exact.label "left disk" ((-2 : Rat), (-9 / 10 : Rat)) |>.role "left",
      Plane.Exact.label "right disk" ((2 : Rat), (9 / 10 : Rat)) |>.role "right",
      Plane.Exact.label "lens" ((0 : Rat), (-11 / 10 : Rat)) |>.role "lens"] ∧
    (chordEnd - leftCentre).normSq = critical.radicand ∧
    QSqrt.lt (chordEnd - rightCentre).normSq critical.radicand = true ∧
    (-chordEnd - rightCentre).normSq = critical.radicand ∧
    QSqrt.lt (-chordEnd - leftCentre).normSq critical.radicand = true ∧
    (crossing - leftCentre).normSq = critical.radicand ∧
    (crossing - rightCentre).normSq = critical.radicand ∧
    (-crossing - leftCentre).normSq = critical.radicand ∧
    (-crossing - rightCentre).normSq = critical.radicand ∧
    (spokeEnd - leftCentre).normSq = critical.radicand ∧
    (phiInv.conj == phiInv) = true ∧ QSqrt.lt ⟨0, 0⟩ phiInv.realPart = true ∧
    QSqrt.lt phiInv.realPart ⟨1, 0⟩ = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves criticalChord criticalChord_spec

/-! ### The orbit of zero as the radius grows -/

/-- The radii of the slider below the critical radius, with their labels. -/
def sliderRadii : Array (String × Rat) :=
  #[("1.2", 6 / 5), ("1.5", 3 / 2), ("1.9", 19 / 10), ("1.95", 39 / 20), ("2", 2),
    ("2.05", 41 / 20),    ("2.07", 207 / 100), ("2.08", 52 / 25), ("2.1", 21 / 10)]

/-- The most points of the orbit of zero drawn at the critical radius, where the orbit is
infinite: the first ones the breadth-first search finds. -/
def criticalCap : Nat := 800

/-- The house style for orbits: markers without the ring of background colour, since the many
orbit points are drawn without halos. -/
def orbitStyle : Style := { houseStyle with plane := { houseStyle.plane with markerRing := 0 } }

/-- A point recording where it stands relative to the two disks and their lens. -/
def withSides (it : Item) (l r : Side) : Item :=
  it |>.incident l.incidence "the left circle" |>.incident r.incidence "the right circle"
    |>.incident (l.lens r).incidence "the lens"

/-- The picture of the orbit `o` of zero at radius `r` (`r2` its square, `rText` its value as
text): the two disks outlined, their lens, the centres and every point of `o`, each point and
centre recording where it stands relative to each disk and to the lens as the engine decided
it. -/
def orbitFrame {β : Type} [RealValue β] (r : β) (r2 : RadiusSq) (rText : String) (o : Orbit) :
    Except String Plane.Figure := do
  let (ll, lr) ← sides r2 leftCentre
  let (rl, rr) ← sides r2 rightCentre
  return {
    width := figureWidth
    padding := 16
    style := orbitStyle
    checks := .fail
    items := #[
      Plane.Exact.disk leftCentre r |>.noFill |>.role leftRole |>.named "the left circle"
        |>.describedBy s!"the closed disk of radius {rText} about −1",
      Plane.Exact.disk rightCentre r |>.noFill |>.role rightRole |>.named "the right circle"
        |>.describedBy s!"the closed disk of radius {rText} about 1",
      Plane.Exact.lens leftCentre rightCentre r r |>.role lensRole |>.noOutline
        |>.fillOpacity 0.12 |>.named "the lens"] ++
      o.points.map (fun p => withSides (Plane.Exact.point p.z |>.size 1.5 |>.halo false)
        p.left p.right) ++
      #[withSides (Plane.Exact.point leftCentre |>.role leftRole |>.named "the centre −1") ll lr,
        withSides (Plane.Exact.point rightCentre |>.role rightRole |>.named "the centre 1") rl rr,
        Plane.Exact.label "−1" leftCentre .auto |>.role leftRole,
        Plane.Exact.label "+1" rightCentre .auto |>.role rightRole]
    info := { title := s!"The orbit of 0 at radius {rText}: " ++
      if o.complete then s!"{o.points.size} points" else s!"its first {o.points.size} points" } }

/-- A frame that says why it could not be drawn. -/
def failedFrame (e : String) : Plane.Figure :=
  { items := #[Plane.label s!"not drawn: {e}" ⟨0, 0⟩], checks := .fail }

/-- The frames of the slider: one for each radius of `sliderRadii`, then the critical radius,
where only the first `criticalCap` points are drawn. -/
def sliderFrames : Array (String × Plane.Figure) :=
  let frame := fun {β : Type} [RealValue β] (r : β) (r2 : RadiusSq) (t : String) (cap : Nat) =>
    match orbit r2 origin cap >>= orbitFrame r r2 t with
    | .ok f => f
    | .error e => failedFrame e
  (sliderRadii.map fun (t, r) => (t, frame r (RadiusSq.ofRat r) t 100000)).push
    ("R", frame critical RadiusSq.critical "R = √(3 + φ)" criticalCap)

/-- The orbit of 0 under the two generators for radii from 1.2 to the critical radius R: finite
below R, with 9, 71, 151, 773 and 801 points, and infinite at R, where its first 800 points are
drawn. -/
@[figure]
def orbitRadius : Explorer := Plane.slider "r" sliderFrames

end TDCSGFigures
