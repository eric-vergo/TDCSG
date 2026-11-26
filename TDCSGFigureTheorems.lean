/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import VersoManual
import VersoBlueprint
import PILeanVerso
import TDCSGFigures

open Verso.Genre Verso.Genre.Manual Informal PILeanVerso

set_option verso.code.warnLineLength 100

#doc (Manual) "Figures and their theorems" =>

%%%
tag := "figure-theorems"
number := false
%%%

Every figure of this site is the value of a Lean declaration of the library `TDCSGFigures`, drawn by
PILean from exact data: points of $`\mathbb Z[\zeta]` and reals of $`\mathbb Q(\sqrt5)`, with every
incidence a figure records decided exactly. Under each figure a source line names that declaration
and, when the figure has one, the theorem stated here. Each theorem writes out the figure's items as
the figure's code builds them, so a change to the figure that the theorem does not repeat breaks the
build, and proves the facts the caption relies on, by `rfl` and `decide +kernel`. What a theorem
does not state is said at the end of its doc string: how the builders draw, the layout, the
lettering, the color values and the pixels. PILean attaches each theorem to its figure with
`figure_links`, which accepts only a theorem whose statement names the figure and which depends on
no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

Many figures are animations. Each is drawn from exact key frames, which its stills show; between
two key frames the browser turns or slides the drawn items about the stated centres or along the
stated vectors, and that motion is not part of any statement. What the key frames show, that the
figure shown is made of exactly those key frames, declared moves and captions, and that each
declared turn or slide carries one key frame onto the next exactly, is stated here as a plain
theorem (`TDCSGFigures.wordLoop_keys`, `TDCSGFigures.Lift.framePair_keys`,
`TDCSGFigures.generatorStep_keys` and the other `_keys` theorems). Where an animation replaced a
figure with a linked theorem, its last key frame is that figure, and the theorem stays linked to
the animation: it states that the last key frame is the figure and what the figure draws
(`TDCSGFigures.generatorStep_spec`, `TDCSGFigures.extensionJump_spec`,
`TDCSGFigures.disjointDisks_spec`, `TDCSGFigures.exchangedIntervals_spec`,
`TDCSGFigures.chordOrbit_spec`). The other animations (the word followed letter by letter and the
three words of chapters 2 and 3, the frame pair of chapter 4 and the walk of chapter 7) are
illustrations: no theorem is linked to them.

The theorems are not statements of the proof, and they are not nodes of the dependency graph.

# The figures of the front page

%%%
tag := "theorems-front"
file := "Theorems-front"
%%%

{figref "critical-chord"}[]: the figure `TDCSGFigures.criticalChord`
and its theorem `TDCSGFigures.criticalChord_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Front

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
      Plane.Exact.point leftCentre |>.role "left" |>.named "the center −1",
      Plane.Exact.point rightCentre |>.role "right" |>.named "the center 1",
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

figure_links criticalChord criticalChord_spec

end TDCSGFigures
```

The slider of the orbit of zero, {figref "orbit-radius"}[], has no theorem of its own: its
frames are computed by the exact orbit engine `TDCSGCompute`, and every point records the sides
of the disks that the engine decided.

# The figures of chapter 1

%%%
tag := "theorems-compound"
file := "Theorems-compound"
%%%

{figref "extension-jump"}[]: the animation `TDCSGFigures.extensionJump`, whose last key frame is the
figure of the jump, with its theorem `TDCSGFigures.extensionJump_spec`; the other key frames and
the moves are stated in `TDCSGFigures.extensionJump_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- The animation `extensionJump` and the figure of the jump, its last key frame. The animation has
one panel whose keys are `jumpKey 0`, `jumpKey 1` and `extensionJumpFinal`, and whose steps are
made from the declared moves `jumpMoves`; its poster, the still shown under reduced motion and in
print, is the last key. The figure of the jump, `extensionJumpFinal`, draws the disk `B` of radius
`10` about `c = 0`, the points `p = 9` and `q = 11`, the image `ĥ(p) = 9ζ⁴` of `p` under the turn
through `72°` clockwise (multiplication by `ζ⁴ = e^{-2πi/5}`), and the end `10ζ²` of the drawn
radius. Its items are written out in drawing order, each with its colour, title, width, dashes,
link, recorded incidences and, for those the animation fades in, its id. The facts hold exactly in
`ℚ(√5)`: `|p|² = 81 < 100 < 121 = |q|²` (`p` inside `B`, `q` outside, so the extension turns `p`
and fixes `q`), `|ĥ(p)|² = 81`, `|p - q|² = 4`, `|ĥ(p) - ĥ(q)|² = |9ζ⁴ - 11|² = 301 - 99φ > 100`,
and `|10ζ²|² = 100`. Not stated: how the builders and modifiers draw, the layout, the lettering,
the style's colour values and the pixels. -/
theorem extensionJump_spec :
    extensionJump.panels = #[{ motion :=
      { keys := #[jumpKey 0, jumpKey 1, extensionJumpFinal],
        steps := ((List.range 2).map (exactStep ∘ jumpMoves)).toArray } }] ∧
    extensionJump.poster = 2 ∧
    ballRadius = 10 ∧ nearInside = Zeta5.ofInt 9 ∧ nearOutside = Zeta5.ofInt 11 ∧
    nearInsideImage = nearInside * Zeta5.pow 4 ∧ ballSpoke = Zeta5.ofInt 10 * Zeta5.pow 2 ∧
    origin = Zeta5.zero ∧
    extensionJumpFinal.items = #[
      Plane.Exact.disk origin ballRadius |>.noFill |>.role leftRole |>.named "the disk B"
        |>.describedBy "the closed disk of radius 10 about c = 0" |>.declRef `TDCSG.ballPerm,
      Plane.Exact.arc origin (9 : Rat) 0 (-deg 72) |>.withArrow |>.role leftRole |>.width 1.5
        |>.named "the turn of p through 72° clockwise about c"
        |>.declRef `TDCSG.ballPerm_apply_of_mem |>.withId "arc",
      Plane.Exact.segment origin ballSpoke |>.role leftRole |>.width 1.5 |>.dashed
        |>.named "a radius of B, length 10",
      Plane.Exact.labelBeside "radius 10" origin ballSpoke |>.role leftRole,
      Plane.Exact.angleMark origin 0 (-deg 72) (some 30) |>.role leftRole
        |>.named "the angle of the turn, 72° clockwise" |>.withId "angle",
      Plane.Exact.segment nearInside nearOutside |>.faint |>.dashed |>.named "p to q, length 2"
        |>.withId "gap",
      Plane.Exact.segment nearInsideImage nearOutside |>.faint |>.dashed
        |>.named "ĥ(p) to ĥ(q), length about 11.9" |>.withId "image-gap",
      Plane.label "2" ⟨21 / 2, 0⟩ .above |>.withId "gap-label",
      Plane.label "≈ 11.9" ((PlanePoint.toPoint nearInsideImage).lerp
        (PlanePoint.toPoint nearOutside) 0.62) (.toward (deg 136)) (some 4)
        |>.withId "image-gap-label",
      Plane.Exact.point origin |>.role leftRole |>.named "the center c",
      Plane.Exact.point nearInside |>.role leftRole |>.named "p" |>.incident .inside "the disk B"
        |>.declRef `TDCSG.ballPerm_apply_of_mem |>.withId "p",
      Plane.Exact.point nearOutside |>.named "q = ĥ(q)" |>.incident .outside "the disk B"
        |>.declRef `TDCSG.ballPerm_apply_of_notMem |>.withId "q",
      Plane.Exact.point nearInsideImage |>.role leftRole |>.named "ĥ(p)"
        |>.incident .inside "the disk B" |>.withId "image",
      Plane.Exact.label "c" origin .auto |>.role leftRole,
      Plane.Exact.label "p" nearInside .above |>.role leftRole |>.withId "p-label",
      Plane.Exact.label "q, fixed" nearOutside .belowRight |>.withId "q-label",
      Plane.Exact.label "image of p" nearInsideImage .auto |>.role leftRole
        |>.withId "image-label",
      Plane.Exact.label "72°" origin (.toward (-deg 36)) (some 42) |>.role leftRole
        |>.withId "angle-label",
      Plane.Exact.label "disk B" ((-6 : Rat), (-5 : Rat)) |>.role leftRole] ∧
    QSqrt.lt nearInside.normSq (rat 100) = true ∧ QSqrt.lt (rat 100) nearOutside.normSq = true ∧
    (nearInsideImage.normSq == rat 81) = true ∧
    ((nearInside - nearOutside).normSq == rat 4) = true ∧
    ((nearInsideImage - nearOutside).normSq == rat 301 - phi * rat 99) = true ∧
    QSqrt.lt (rat 100) (nearInsideImage - nearOutside).normSq = true ∧
    (ballSpoke.normSq == rat 100) = true := by
  refine ⟨by unfold extensionJump; with_reducible rfl, by unfold extensionJump; with_reducible rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links extensionJump extensionJump_spec

/-- The key frames of `extensionJump` before the last and its moves. Key `k ≤ 1` draws, in the
frame of the figure of the jump, the disk, its radius, the bar from `8` to `12` across the
boundary circle in two parts and the centre: the part in `B`, from `8` to `10` with `p = 9`
(`jumpInner`), turned by `ζ⁴` about `0` at key `1`, and the part outside, from `10` to `12` with
`q = 11` (`jumpOuter`); at key `0` also the segment from `p` to `q`, its length and the label of
`p`. Step `0` turns the part in `B` by `jumpTurn`, a fifth of a turn clockwise about `0`, while the
segment from `p` to `q` and the labels fade; step `1` fades the bar out and the marks of the figure
of the jump in. Each declared move, applied exactly in `ℚ(ζ₅)` to the anchors of the actors of
one key, gives those of the next (`jumpArrives`). The ends of the parts lie as stated: `|8|² < 100`,
`|10|² = 100` (on the boundary circle, so in the closed disk, and turned), `|12|² > 100`, and the
turn by `ζ⁴` is the extension's turn: it carries `p` to `ĥ(p)`. The captions are written out. Not
stated: how the builders draw, the timing and the frames the browser draws between the key
frames. -/
theorem extensionJump_keys :
    extensionJump.captions = jumpCaptions ∧
    jumpCaptions = #[
      "A closed disk B of radius 10 about c = 0, to be turned through 72° clockwise and extended \
        by the identity. A bar from 8 to 12 crosses the boundary circle at 10: p = 9 lies inside \
        B, q = 11 outside, 2 apart.",
      "The extension ĥ turns the part of the bar in B, its point 10 on the circle included, about \
        c and fixes the part outside: the bar is torn at the circle. p went to ĥ(p) = 9ζ⁴, q \
        stayed.",
      "p and q were 2 apart; ĥ(p) and ĥ(q) = q are about 11.9 apart. However close to the circle \
        p and q are taken, the jump stays, so ĥ is not continuous and is no isometry of the \
        plane."] ∧
    (∀ k, jumpKey k =
      { extensionJumpFinal with
        items := jumpKeyItems k
        info := { title := jumpCaptions.getD k "" } }) ∧
    (∀ k, jumpKeyItems k =
      #[jumpDisk] ++ jumpRadius ++ (if k == 0 then #[jumpGap, jumpGapLabel] else #[]) ++
        #[jumpCentre, jumpInner (if k == 0 then Zeta5.ofInt 1 else zeta 4), jumpOuter,
          jumpCentreLabel] ++ (if k == 0 then #[jumpPLabel] else #[]) ++ #[jumpName]) ∧
    (∀ τ, jumpInner τ =
      ((group #[Plane.Exact.segment (barInner * τ) (barCut * τ) |>.role leftRole |>.width 4
            |>.named "the part of the bar in B, from 8 to 10",
          Plane.Exact.point (nearInside * τ) |>.role leftRole |>.incident .inside "the disk B"
            |>.incident .on "the part of the bar in B, from 8 to 10"])
        |>.named "the part of the bar in B and the point p, turned by ĥ" |>.withId "inner")) ∧
    jumpOuter =
      ((group #[Plane.Exact.segment barCut barOuter |>.width 4
            |>.named "the part of the bar outside B, from 10 to 12",
          Plane.Exact.point nearOutside |>.incident .outside "the disk B"
            |>.incident .on "the part of the bar outside B, from 10 to 12",
          Plane.Exact.label "q, fixed" nearOutside .belowRight])
        |>.named "the part of the bar outside B and the point q, fixed by ĥ" |>.withId "outer") ∧
    barInner = Zeta5.ofInt 8 ∧ barCut = Zeta5.ofInt 10 ∧ barOuter = Zeta5.ofInt 12 ∧
    jumpTurn = ⟨ZetaFrac.ofZeta origin, -1 / 5⟩ ∧
    jumpMoves 0 = [("inner", .turn jumpTurn), ("gap", .vanish), ("gap-label", .vanish),
      ("p-label", .vanish)] ∧
    moveKinds (jumpMoves 1) = [("inner", "vanish"), ("outer", "vanish"), ("arc", "appear"),
      ("angle", "appear"), ("gap", "appear"), ("image-gap", "appear"), ("gap-label", "appear"),
      ("image-gap-label", "appear"), ("p", "appear"), ("q", "appear"), ("image", "appear"),
      ("p-label", "appear"), ("q-label", "appear"), ("image-label", "appear"),
      ("angle-label", "appear")] ∧
    jumpArrives = true ∧
    QSqrt.lt barInner.normSq (rat 100) = true ∧ (barCut.normSq == rat 100) = true ∧
    QSqrt.lt (rat 100) barOuter.normSq = true ∧
    ((jumpTurn.apply (ZetaFrac.ofZeta nearInside)).any
      (ZetaFrac.same · (ZetaFrac.ofZeta nearInsideImage))) = true := by
  refine ⟨by unfold extensionJump; with_reducible rfl, rfl,
    fun _ => by unfold jumpKey; with_reducible rfl,
    fun _ => by unfold jumpKeyItems; with_reducible rfl,
    fun _ => by unfold jumpInner; with_reducible rfl, by unfold jumpOuter; with_reducible rfl, rfl,
    rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

end TDCSGFigures
```

{figref "disjoint-disks"}[]: the animation `TDCSGFigures.disjointDisks`, whose last key frame in
both panels is the figure of the two turns, with its theorem `TDCSGFigures.disjointDisks_spec`;
the other key frames and the moves are stated in `TDCSGFigures.disjointDisks_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- The animation `disjointDisks` and the figure of the two turns, the last key frame of both of
its panels. The animation has two panels on one clock, `disjointPanel true` (`a`, then `b`) and
`disjointPanel false` (`b`, then `a`), whose keys are `disjointKey b k` for `k = 0, …, 3`, the
last one `disjointDisksFinal`; its poster is the last key. The figure of the two turns draws the
radii `r₁ = 4/5` and `r₂ = 7/10` of the disks `B₁` about `-1` and `B₂` about `1`, the points
`x = -1 + φ⁻¹ ζ²` and `y = 1 + φ⁻¹ ζ²` (`φ⁻¹ = ζ + ζ⁴`), and their images `a(x) = -1 + φ⁻¹ ζ` and
`b(y) = 1 + φ⁻¹ ζ`; its items are written out in drawing order. The facts hold exactly:
`r₁ + r₂ < 2`, so the disks are disjoint and the gap runs from `-1 + r₁ = -1/5` to
`1 - r₂ = 3/10`; `|x + 1|² = |y - 1|² = φ⁻²` with `φ⁻² < r₂² < r₁²`; `x` lies outside `B₂` and `y`
outside `B₁`; `a` turns `x` to `a(x)` and fixes `y`, `b` turns `y` to `b(y)` and fixes `x`; `a(x)`
lies in `B₁` and `b(y)` in `B₂`. Not stated: how the builders and modifiers draw, the layout, the
lettering, the style's colour values and the pixels. -/
theorem disjointDisks_spec :
    disjointDisks.panels = #[disjointPanel true, disjointPanel false] ∧
    (∀ b, (disjointPanel b).motion.keys = ((List.range 4).map (disjointKey b)).toArray) ∧
    (∀ b, disjointKey b 3 = disjointDisksFinal) ∧ disjointDisks.poster = 3 ∧
    disjointLeft = 4 / 5 ∧ disjointRight = 7 / 10 ∧
    leftSample = leftCentre + phiInv * Zeta5.pow 2 ∧
    rightSample = rightCentre + phiInv * Zeta5.pow 2 ∧ phiInvReal = ⟨-1 / 2, 1 / 2⟩ ∧
    disjointDisksFinal.items = #[
      Plane.Exact.disk leftCentre disjointLeft |>.noFill |>.role leftRole |>.named "the disk B₁"
        |>.describedBy "the closed disk of radius 4/5 about −1",
      Plane.Exact.disk rightCentre disjointRight |>.noFill |>.role rightRole |>.named "the disk B₂"
        |>.describedBy "the closed disk of radius 7/10 about 1",
      Plane.Exact.segment ((-1 / 5 : Rat), (0 : Rat)) ((3 / 10 : Rat), (0 : Rat)) |>.faint |>.dashed
        |>.named "the gap between B₁ and B₂, of length 1/2"
        |>.declRef `TDCSG.leftDisk_disjoint_rightDisk,
      Plane.label "gap" ⟨1 / 20, 0⟩ .below,
      Plane.Exact.arc leftCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role leftRole
        |>.width 1.5 |>.named "the turn a of B₁, 72° clockwise about −1" |>.declRef `TDCSG.genA
        |>.withId "arc-a",
      Plane.Exact.arc rightCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role rightRole
        |>.width 1.5 |>.named "the turn b of B₂, 72° clockwise about 1" |>.declRef `TDCSG.genB
        |>.withId "arc-b",
      Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1",
      Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1",
      Plane.Exact.point leftSample |>.role leftRole |>.named "x" |>.incident .inside "the disk B₁"
        |>.incident .outside "the disk B₂" |>.withId "x",
      Plane.Exact.point (leftCentre + phiInv * zeta 1) |>.role leftRole |>.named "a(x)"
        |>.incident .inside "the disk B₁" |>.withId "ax",
      Plane.Exact.point rightSample |>.role rightRole |>.named "y" |>.incident .inside "the disk B₂"
        |>.incident .outside "the disk B₁" |>.withId "y",
      Plane.Exact.point (rightCentre + phiInv * zeta 1) |>.role rightRole |>.named "b(y)"
        |>.incident .inside "the disk B₂" |>.withId "by",
      Plane.Exact.label "−1" leftCentre .below |>.role leftRole,
      Plane.Exact.label "+1" rightCentre .below |>.role rightRole,
      Plane.Exact.label "x" leftSample .auto |>.role leftRole |>.withId "x-label",
      Plane.Exact.label "a(x)" (leftCentre + phiInv * zeta 1) .auto |>.role leftRole
        |>.withId "ax-label",
      Plane.Exact.label "y" rightSample .auto |>.role rightRole |>.withId "y-label",
      Plane.Exact.label "b(y)" (rightCentre + phiInv * zeta 1) .auto |>.role rightRole
        |>.withId "by-label",
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
  refine ⟨by unfold disjointDisks; with_reducible rfl,
    fun _ => by unfold disjointPanel; with_reducible rfl,
    fun _ => by unfold disjointKey; rw [if_pos (by decide)],
    by unfold disjointDisks; with_reducible rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links disjointDisks disjointDisks_spec

/-- The key frames of `disjointDisks` before the last and its moves. The panels are titled by
their order. Key `k ≤ 2` of a panel draws, in the frame of the figure of the two turns, the disks,
the gap, the centres and the names, and the two points that move with their labels: `x` turned
by `a` from key `1` on in the panel `a`, then `b` and from key `2` on in the other, `y` turned by
`b` from key `2` on in the first panel and from key `1` on in the other (`disjointX`,
`disjointY`). Step `0` turns `x` by `a` (a fifth of a turn clockwise about `-1`) in the first
panel and `y` by `b` (about `1`) in the other; step `1` the other one; step `2` fades the moving
points out and the marks of the figure of the two turns in. Each declared move, applied exactly in
`ℚ(ζ₅)` to the anchors of the actors of one key, gives those of the next, in both panels
(`disjointArrives`); at key `2` both panels show `x` at `a(x)` and `y` at `b(y)`, the points of the
figure of the two turns, so both orders end in the same picture. The captions are written out.
Not stated: how the builders draw, the timing and the frames the browser draws between the key
frames. -/
theorem disjointDisks_keys :
    disjointDisks.captions = disjointCaptions ∧
    disjointCaptions = #[
      "Two disjoint closed disks, B₁ of radius 4/5 about −1 and B₂ of radius 7/10 about 1, a \
        point x in B₁ and a point y in B₂. Left: a, then b. Right: b, then a.",
      "Left: a turns B₁ a fifth of a turn clockwise about −1, carrying x, and fixes y. Right: b \
        turns B₂ a fifth of a turn clockwise about +1, carrying y, and fixes x.",
      "Left: b turns y; right: a turns x. Both orders end in the same picture: the two turns move \
        disjoint sets of points, so they commute.",
      "The turn a of B₁ and the turn b of B₂, each through 72° clockwise: a moves x to a(x) and \
        fixes y, b moves y to b(y) and fixes x."] ∧
    (∀ b, disjointPanel b =
      { title := if b then "a, then b" else "b, then a"
        motion :=
          { keys := ((List.range 4).map (disjointKey b)).toArray,
            steps := ((List.range 3).map fun k => exactStep (disjointMoves b k)).toArray } }) ∧
    (∀ b k, k ≠ 3 → disjointKey b k =
      { disjointDisksFinal with
        items := disjointKeyItems b k,
        info := { title := disjointCaptions.getD k "" } }) ∧
    (∀ b k, disjointKeyItems b k = disjointBase ++ disjointCentres ++
      #[disjointMoverX (disjointX b k), disjointMoverY (disjointY b k)] ++
      disjointCentreLabels ++ disjointNames) ∧
    (∀ w, disjointMoverX w =
      ((group #[Plane.Exact.point w |>.role leftRole |>.incident .inside "the disk B₁"
            |>.incident .outside "the disk B₂",
          Plane.Exact.label "x" w (.toward (-deg 72)) |>.role leftRole])
        |>.named "the point x of B₁, turned by a" |>.withId "x-moving")) ∧
    (∀ w, disjointMoverY w =
      ((group #[Plane.Exact.point w |>.role rightRole |>.incident .inside "the disk B₂"
            |>.incident .outside "the disk B₁",
          Plane.Exact.label "y" w (.toward (-deg 72)) |>.role rightRole])
        |>.named "the point y of B₂, turned by b" |>.withId "y-moving")) ∧
    (∀ b k, disjointX b k =
      if disjointXTurned b k then Letter.a.rotate leftSample else leftSample) ∧
    (∀ b k, disjointY b k =
      if disjointYTurned b k then Letter.b.rotate rightSample else rightSample) ∧
    (∀ k, disjointXTurned true k = decide (1 ≤ k) ∧ disjointXTurned false k = decide (2 ≤ k)) ∧
    (∀ k, disjointYTurned true k = decide (2 ≤ k) ∧ disjointYTurned false k = decide (1 ≤ k)) ∧
    disjointTurnA = ⟨ZetaFrac.ofZeta leftCentre, -1 / 5⟩ ∧
    disjointTurnB = ⟨ZetaFrac.ofZeta rightCentre, -1 / 5⟩ ∧
    disjointMoves true 0 = [("x-moving", .turn disjointTurnA)] ∧
    disjointMoves true 1 = [("y-moving", .turn disjointTurnB)] ∧
    disjointMoves false 0 = [("y-moving", .turn disjointTurnB)] ∧
    disjointMoves false 1 = [("x-moving", .turn disjointTurnA)] ∧
    (∀ b, moveKinds (disjointMoves b 2) = [("x-moving", "vanish"), ("y-moving", "vanish"),
      ("arc-a", "appear"), ("arc-b", "appear"), ("x", "appear"), ("ax", "appear"), ("y", "appear"),
      ("by", "appear"), ("x-label", "appear"), ("ax-label", "appear"), ("y-label", "appear"),
      ("by-label", "appear")]) ∧
    disjointArrives = true ∧
    (Letter.a.rotate leftSample == leftCentre + phiInv * zeta 1) = true ∧
    (Letter.b.rotate rightSample == rightCentre + phiInv * zeta 1) = true := by
  refine ⟨by unfold disjointDisks; with_reducible rfl, rfl, fun _ => rfl, fun _ _ h => ?_,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, fun b => ?_, ?_⟩
  · simp only [disjointKey, beq_iff_eq, h, if_false]
  · cases b <;> rfl
  repeat' apply And.intro
  all_goals decide +kernel

end TDCSGFigures
```

# The figures of chapter 2

%%%
tag := "theorems-disks"
file := "Theorems-disks"
%%%

{figref "generator-step"}[]: the animation `TDCSGFigures.generatorStep`, whose last key frame is
the figure of one step of the left generator, with its theorem `TDCSGFigures.generatorStep_spec`;
the other key frames and the moves are stated in `TDCSGFigures.generatorStep_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- The animation `generatorStep` and the figure of one step of the left generator, its last key
frame. The animation has one panel whose keys are `generatorKeys`, two keys and then
`generatorStepFinal`, and whose steps are made from the declared moves `generatorMoves`; its
poster, the still shown under reduced motion and in print, is the last key. The figure of the
step draws the radius `3/2` of both disks, `a(0) = -1 + ζ⁴` and the end `(19/10, -6/5)` of the
drawn radius of the right disk; its items are written out in drawing order, each with its colour,
title, width, dashes, link, recorded incidences and, for those the animation fades in, its id.
The facts hold exactly in `ℚ(√5)`: `a` turns `0` to `a(0)` (`0` lies in the left disk);
`|0 ∓ 1|² = 1 < 9/4`, so `0` is inside both disks and the lens; `|a(0) + 1|² = 1 < 9/4` and
`|a(0) - 1|² = 7 - 2φ > 9/4`, so `a(0)` is inside the left disk and outside the right one and the
lens; `|(19/10, -6/5) - 1|² = 9/4`. Not stated: how the builders and modifiers draw, the layout,
the lettering, the style's colour values and the pixels. -/
theorem generatorStep_spec :
    generatorStep.panels = #[{ motion :=
      { keys := generatorKeys,
        steps := ((List.range 2).map (exactStep ∘ generatorMoves)).toArray } }] ∧
    generatorKeys = #[generatorKey 0, generatorKey 1, generatorStepFinal] ∧
    generatorStep.poster = 2 ∧
    aZero = leftCentre + Zeta5.pow 4 ∧ rightSpokeEnd = (19 / 10, -6 / 5) ∧
    r2ThreeHalves = rat (9 / 4) ∧
    generatorStepFinal.items = #[
      Plane.Exact.disk leftCentre (3 / 2 : Rat) |>.noFill |>.role leftRole
        |>.named "the left circle"
        |>.describedBy "the closed disk of radius 3/2 about −1, turned by a" |>.declRef `TDCSG.genA,
      Plane.Exact.disk rightCentre (3 / 2 : Rat) |>.noFill |>.role rightRole
        |>.named "the right circle"
        |>.describedBy "the closed disk of radius 3/2 about 1, turned by b"
        |>.declRef `TDCSG.genB,
      Plane.Exact.lens leftCentre rightCentre (3 / 2 : Rat) (3 / 2 : Rat) |>.role lensRole
        |>.noOutline |>.fillOpacity 0.12 |>.named "the lens",
      Plane.Exact.segment ((1 : Rat), (0 : Rat)) rightSpokeEnd |>.role rightRole |>.width 1.5
        |>.dashed |>.named "a radius of the right disk, length 3/2",
      Plane.Exact.labelBeside "r = 1.5" ((1 : Rat), (0 : Rat)) rightSpokeEnd |>.role rightRole,
      Plane.Exact.segment leftCentre origin |>.role leftRole |>.width 1.5
        |>.named "from −1 to 0",
      Plane.Exact.segment leftCentre aZero |>.role leftRole |>.width 1.5
        |>.named "from −1 to a(0)" |>.withId "image-spoke",
      Plane.Exact.angleMark leftCentre 0 (-deg 72) (some 22) |>.role leftRole
        |>.named "72° clockwise" |>.withId "angle",
      Plane.Exact.label "72°" leftCentre (.toward (-deg 112)) (some 26) |>.role leftRole |>.size 12
        |>.withId "angle-label",
      Plane.Exact.arc leftCentre (1 : Rat) (deg 0) (-deg 72) |>.withArrow |>.role leftRole
        |>.width 2 |>.dashed |>.named "a turns 0 through 72° clockwise about −1"
        |>.declRef `TDCSG.diskRotation |>.withId "arc",
      Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1",
      Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1",
      Plane.Exact.point origin |>.named "0" |>.incident .inside "the left circle"
        |>.incident .inside "the right circle" |>.incident .inside "the lens" |>.withId "origin",
      Plane.Exact.point aZero |>.role leftRole |>.named "a(0) = −1 + ζ⁴"
        |>.incident .inside "the left circle" |>.incident .outside "the right circle"
        |>.incident .outside "the lens" |>.declRef `TDCSG.genA |>.withId "image",
      Plane.Exact.label "−1" leftCentre .above |>.role leftRole,
      Plane.Exact.label "+1" rightCentre .above |>.role rightRole,
      Plane.Exact.label "0" origin .aboveRight,
      Plane.Exact.label "a(0)" aZero .below |>.role leftRole |>.withId "image-label",
      Plane.Exact.label "left disk" ((-8 / 5 : Rat), (3 / 4 : Rat)) |>.role leftRole,
      Plane.Exact.label "right disk" ((8 / 5 : Rat), (3 / 4 : Rat)) |>.role rightRole,
      Plane.Exact.label "lens" ((0 : Rat), (5 / 8 : Rat)) |>.role lensRole |>.size 13] ∧
    (Letter.a.act r2ThreeHalves origin == aZero) = true ∧
    QSqrt.lt (origin - leftCentre).normSq r2ThreeHalves = true ∧
    QSqrt.lt (origin - rightCentre).normSq r2ThreeHalves = true ∧
    ((aZero - leftCentre).normSq == rat 1) = true ∧
    ((aZero - rightCentre).normSq == rat 7 - phi * rat 2) = true ∧
    QSqrt.lt r2ThreeHalves (aZero - rightCentre).normSq = true ∧
    decide ((19 / 10 - 1 : Rat) * (19 / 10 - 1) + (-6 / 5) * (-6 / 5) = 9 / 4) = true := by
  refine ⟨by unfold generatorStep; with_reducible rfl,
    by unfold generatorKeys; with_reducible rfl, by unfold generatorStep; with_reducible rfl, rfl,
    rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links generatorStep generatorStep_spec

/-- The key frames of `generatorStep` before the last and its moves. Key `k ≤ 1` draws, in the
frame of the figure of the step, its disks, lens, radius, centres and names and, in place of its
marks of the turn: the content of the left disk (`turningContent`), the segment from the first
sample to `-1` and the samples `turnedSamples`, `0` among them, before the turn (key `0`) and their
images `turnedImages` after it (key `1`), each recording that it lies inside the left disk; and the
points `fixedSamples` outside it (`fixedContent`). Step `0` turns the content of the disk by
`generatorTurn`, a fifth of a turn clockwise about `-1`; step `1` fades it and the points outside
out and the marks of the figure of the step in. The declared turn, applied exactly in `ℚ(ζ₅)` to
the anchors of the actors of key `0`, gives those of key `1` (`generatorArrives`). The samples
are what the generator does with them: each of `turnedSamples` lies in the closed left disk of
radius `3/2` and `a` carries it to its image, the first to `a(0)`; each of `fixedSamples` lies
outside it and `a` fixes it. The captions are written out. Not stated: how the builders draw, the
timing and the frames the browser draws between the key frames. -/
theorem generatorStep_keys :
    generatorStep.captions = generatorCaptions ∧
    generatorCaptions = #[
      "The left generator a acts on its closed disk of radius 1.5 about −1. The points inside the \
        disk, the origin among them (drawn in the color of the left disk), turn with it; the \
        points outside it stay where they are.",
      "a turns the disk a fifth of a turn clockwise about −1: the origin goes to a(0) = −1 + ζ⁴, \
        and the points outside the left disk have not moved.",
      "One step of the left generator: a turns the origin through 72° clockwise about −1, along \
        the dashed arc, to a(0). The origin lies in both disks, a(0) in the left disk only."] ∧
    (∀ k, generatorKey k =
      { generatorStepFinal with
        items := generatorKeyItems k,
        info := { title := generatorCaptions.getD k "" } }) ∧
    (∀ k, generatorKeyItems k = generatorBase ++
      #[turningContent (if k == 0 then turnedSamples else turnedImages), fixedContent] ++
      generatorCentres ++ generatorLabels ++ generatorNames) ∧
    (∀ zs, turningContent zs =
      ((group (#[Plane.Exact.segment (zs.headD origin) leftCentre |>.role leftRole |>.width 1.5,
          Plane.Exact.point (zs.headD origin) |>.role leftRole] ++
        (zs.drop 1).toArray.map fun w =>
          Plane.Exact.point w |>.role leftRole |>.size 3 |>.incident .inside "the left circle"))
        |>.named "points of the left disk, which a turns" |>.withId "disk")) ∧
    fixedContent =
      (group (fixedSamples.toArray.map fun w =>
          Plane.Exact.point w |>.size 3 |>.incident .outside "the left circle")
        |>.named "points outside the left disk, which a fixes" |>.withId "outside") ∧
    turnedSamples =
      [origin, leftCentre + phiInv * zeta 3, zeta 4 - Zeta5.ofInt 2, leftCentre + zeta 2 - zeta 3] ∧
    fixedSamples = [phiInv, leftCentre + (Zeta5.ofInt 1 + phiInv) * zeta 2,
      leftCentre + (Zeta5.ofInt 1 + phiInv) * zeta 3] ∧
    turnedImages = turnedSamples.map Letter.a.rotate ∧
    generatorTurn = ⟨ZetaFrac.ofZeta leftCentre, -1 / 5⟩ ∧
    generatorMoves 0 = [("disk", .turn generatorTurn)] ∧
    moveKinds (generatorMoves 1) = [("disk", "vanish"), ("outside", "vanish"),
      ("image-spoke", "appear"), ("angle", "appear"), ("angle-label", "appear"), ("arc", "appear"),
      ("origin", "appear"), ("image", "appear"), ("image-label", "appear")] ∧
    generatorArrives = true ∧
    turnedSamples.all (Letter.a.covers r2ThreeHalves) = true ∧
    (turnedSamples.map (Letter.a.act r2ThreeHalves) == turnedImages) = true ∧
    (turnedImages.headD origin == aZero) = true ∧
    fixedSamples.all (fun z => !Letter.a.covers r2ThreeHalves z) = true ∧
    (fixedSamples.map (Letter.a.act r2ThreeHalves) == fixedSamples) = true := by
  refine ⟨by unfold generatorStep; with_reducible rfl, rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

end TDCSGFigures
```

{figref "word-steps"}[]: the animation `TDCSGFigures.wordSteps`, an illustration, and the data of
its key frames, `TDCSGFigures.wordSteps_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- The animation `wordSteps` and the data its key frames are drawn from. It has one panel whose
keys are `stepKey k`, `k = 0, …, 4`, and whose steps are made from the declared moves `stepMoves`.
Every key draws `stepBase` (written out: the two disks of radius `2.1`, their lens, the centres
recording where they stand, and the names), then the circle about the centre of the last turn
(`stepPivot`), at key `4` the segment from `-1` to `z₃` (`stepReach`), the points left behind,
faint and labelled (`stepTrail`, each recording exactly where it stands relative to the two disks
and the lens), and the point `z_k` (`stepMover`). The points are
`z₀ = 0, z₁ = -1 + ζ⁴ = a(0), z₂ = b(z₁), z₃ = b(z₂), z₄ = a(z₃) = z₃`, written out in the basis
`1, ζ, ζ², ζ³`; the letters `a, b, b` find their point in their closed disk of radius `2.1` and
the last `a` does not (`|z₃ + 1|² > 441/100`), so it fixes `z₃`. Step `k` turns the point by
`stepTurn k`, about the centre of letter `k + 1` by `-1/5` of a full turn, when that letter acts,
and fades the circles, the points left behind and the segment in and out; each declared move,
applied exactly in `ℚ(ζ₅)` to the anchors of the actors of one key, gives those of the next
(`stepsArrive`), so every turn carries `z_k` onto `z_{k+1}`. The captions are written out. Not
stated: how the builders draw, the timing and the frames the browser draws between the key
frames. -/
theorem wordSteps_keys :
    wordSteps.panels = #[{ motion :=
      { keys := ((List.range 5).map stepKey).toArray,
        steps := ((List.range 4).map (exactStep ∘ stepMoves)).toArray } }] ∧
    wordSteps.captions = stepCaptions ∧
    stepCaptions = #[
      "z₀ = 0, in both disks. The word a b b a is applied to it at radius 2.1, letter by letter \
        from left to right.",
      "Letter 1, a: z₀ lies in the left disk, so a turns it a fifth of a turn clockwise about −1 \
        (circled), to z₁.",
      "Letter 2, b: z₁ lies in the right disk, so b turns it a fifth of a turn clockwise about +1 \
        (circled), to z₂.",
      "Letter 3, b: z₂ lies in the right disk, so b turns it again, to z₃.",
      "Letter 4, a: z₃ lies outside the left disk, farther than 2.1 from −1 (dashed), so a leaves \
        it where it is: z₄ = z₃."] ∧
    stepWord = [.a, .b, .b, .a] ∧ r2Step = rat (441 / 100) ∧
    stepBase = #[
      Plane.Exact.disk leftCentre (21 / 10 : Rat) |>.noFill |>.role leftRole
        |>.named "the left circle"
        |>.describedBy "the closed disk of radius 2.1 about −1, turned by a" |>.declRef `TDCSG.genA,
      Plane.Exact.disk rightCentre (21 / 10 : Rat) |>.noFill |>.role rightRole
        |>.named "the right circle"
        |>.describedBy "the closed disk of radius 2.1 about 1, turned by b" |>.declRef `TDCSG.genB,
      Plane.Exact.lens leftCentre rightCentre (21 / 10 : Rat) (21 / 10 : Rat) |>.role lensRole
        |>.noOutline
        |>.fillOpacity 0.12 |>.named "the lens",
      withSidesStep leftCentre (Plane.Exact.point leftCentre |>.role leftRole
        |>.named "the center −1"),
      withSidesStep rightCentre
        (Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1"),
      Plane.Exact.label "−1" leftCentre .left (some 24) |>.role leftRole,
      Plane.Exact.label "+1" rightCentre .right (some 24) |>.role rightRole,
      Plane.Exact.label "left disk, radius 2.1" ((-1 : Rat), (-5 / 2 : Rat)) |>.role leftRole,
      Plane.Exact.label "right disk, radius 2.1" ((1 : Rat), (5 / 2 : Rat)) |>.role rightRole] ∧
    (∀ k, stepKey k =
      { width := figureWidth, padding := 16, style := houseStyle, checks := .fail,
        items := stepKeyItems k,
        info := { title := s!"The point {stepName k} of 0 under a b b a at radius 2.1" } }) ∧
    (∀ k, stepKeyItems k =
      stepBase ++ stepPivot k ++ stepReach k ++ (stepTrailIndices k).toArray.map stepTrail ++
        #[stepMover k]) ∧
    (∀ k, stepPoint k = stepPoints.getD k origin) ∧
    (∀ k, stepMover k = (Plane.Exact.point (stepPoint k) |>.size 5
      |>.named "the point followed through the word" |>.withId "point")) ∧
    (∀ j, stepTrail j =
      ((group #[withSidesStep (stepPoint j) (Plane.Exact.point (stepPoint j) |>.faint),
          Plane.Exact.label (stepName j) (stepPoint j) .auto])
        |>.named (stepName j) |>.withId s!"trail-{j}")) ∧
    (∀ k, stepTrailIndices k = (List.range k).filter fun j => !(stepPoint j == stepPoint k)) ∧
    (∀ k, stepPivot k = if k == 0 || 3 < k then #[] else
      let c := (stepWord.getD (k - 1) .a).centre
      let left := c == leftCentre
      #[Plane.Exact.circle c stepPivotRadius |>.role (if left then leftRole else rightRole)
        |>.width 2 |>.named s!"a circle about the center {if left then "−1" else "+1"} of the \
          last turn" |>.withId (if left then "pivot-left" else "pivot-right")]) ∧
    (∀ k, stepReach k = if k == 4 then
      #[Plane.Exact.segment leftCentre (stepPoint 3) |>.role leftRole |>.width 1.5 |>.dashed
        |>.named "from −1 to z₃, longer than 2.1" |>.withId "reach"] else #[]) ∧
    stepPivotRadius = 1 / 5 ∧
    (stepPoints == [⟨#[0, 0, 0, 0]⟩, ⟨#[-2, -1, -1, -1]⟩, ⟨#[3, 2, 2, 3]⟩, ⟨#[1, 0, 1, -2]⟩,
      ⟨#[1, 0, 1, -2]⟩]) = true ∧
    ((stepWord.zip stepPoints).map fun (l, z) => l.covers r2Step z) = [true, true, true, false] ∧
    QSqrt.lt r2Step ((stepPoints.getD 3 origin) - leftCentre).normSq = true ∧
    (∀ k, stepTurn k = ⟨ZetaFrac.ofZeta (stepWord.getD k .a).centre, -1 / 5⟩) ∧
    (stepWord.all fun l => l.turn == zeta 4) = true ∧
    (∀ k, stepPivotId k =
      if (stepWord.getD k .a).centre == leftCentre then "pivot-left" else "pivot-right") ∧
    (List.range 3).map stepPivotId = ["pivot-left", "pivot-right", "pivot-right"] ∧
    stepMoves 0 =
      [("point", .turn (stepTurn 0)), (stepPivotId 0, .appear), ("trail-0", .appear)] ∧
    stepMoves 1 = [("point", .turn (stepTurn 1)), (stepPivotId 1, .appear), ("trail-1", .appear),
      (stepPivotId 0, .vanish)] ∧
    stepMoves 2 = [("point", .turn (stepTurn 2)), ("trail-2", .appear)] ∧
    stepMoves 3 = [("reach", .appear), (stepPivotId 2, .vanish)] ∧
    stepsArrive = true := by
  refine ⟨by unfold wordSteps; with_reducible rfl, by unfold wordSteps; with_reducible rfl, rfl,
    rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, fun _ => rfl, ?_, fun _ => rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  all_goals decide +kernel

end TDCSGFigures
```

# The figure of Part I

%%%
tag := "theorems-part-one"
file := "Theorems-part-one"
%%%

{figref "radius-line-infinite"}[]: the figure `TDCSGFigures.radiusLineInfinite`
and its theorem `TDCSGFigures.radiusLineInfinite_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

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

figure_links radiusLineInfinite radiusLineInfinite_spec

end TDCSGFigures
```

# The figures of chapter 3

%%%
tag := "theorems-chord"
file := "Theorems-chord"
%%%

{figref "chord-pieces"}[]: the figure `TDCSGFigures.chordPieces`
and its theorem `TDCSGFigures.chordPieces_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

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

figure_links chordPieces chordPieces_spec

end TDCSGFigures
```

{figref "word-trace"}[], {figref "word-trace-2"}[] and {figref "word-trace-3"}[]: the animations
`TDCSGFigures.wordLoop1`, `TDCSGFigures.wordLoop2` and `TDCSGFigures.wordLoop3`, illustrations:
what they are made of (`TDCSGFigures.wordLoop_figures`), the data of their key frames
(`TDCSGFigures.wordLoop_keys`) and their captions (`TDCSGFigures.wordLoop_captions`).

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- The three loops and the data their key frames are drawn from. The figures are `wordLoop 1`,
`wordLoop 2`, `wordLoop 3`, the loop without the word strip (`wordLoopWith i false`): one panel
whose keys are `wordKey i k` and whose steps are `wordStep i k`, with the captions
`wordCaption i k`.
Key `k` draws, over the disks, their lens, the chord and the piece (`wordUnder`), the image
`[w_k(p), w_k(q)]` of the piece `[p, q]` after `k` letters (`wordSegment`, read from `wordPath i`,
here written out in the basis `1, ζ, ζ², ζ³`), the circle about the centre of the turn before it
(`wordPivot`) and the ends lying on a boundary circle before the next letter (`wordContacts`, from
`wordEqualities i`). Step `k` turns the image by the declared turn `wordTurn i k` and fades the
other marks in and out (`wordFades`); that declared turn, applied exactly in `ℚ(ζ₅)`, carries both
ends of image `k` onto those of image `k + 1` (`wordArrives`). Before every letter both current
ends lie in the letter's closed disk of radius `R` (`wordChecks`), so the letter turns the whole
segment, as in `TDCSG.Five.applyWord_chord`; the tests that hold with equality are those before
letters 3, 4 of word 1, letters 2, 3 of word 2 and letters 1, 2, 5, 6 of word 3. The caption of key
`k ≥ 1` names letter `k`, its turn and its direction. The last images are the pieces moved by
`(2φ - 2)E` (words 1, 2) and `(2φ - 4)E` (word 3). Not stated: how the builders draw, the timing
and the frames the browser draws between the key frames. -/
theorem wordLoop_figures :
    wordLoop1 = wordLoop 1 ∧ wordLoop2 = wordLoop 2 ∧ wordLoop3 = wordLoop 3 ∧
    (∀ i, wordLoop i = wordLoopWith i false) ∧
    (∀ i, (wordLoopWith i false).panels =
      #[{ motion := { keys := wordLoopKeys i false, steps := wordLoopSteps i false } }]) ∧
    (∀ i, wordLoopKeys i false =
      ((List.range ((wordPiece i).1.length + 1)).map (wordKey i · false)).toArray) ∧
    (∀ i, wordLoopSteps i false =
      ((List.range (wordPiece i).1.length).map (wordStep i · false)).toArray) ∧
    (∀ i, (wordLoopWith i false).captions =
      ((List.range ((wordPiece i).1.length + 1)).map (wordCaption i)).toArray) ∧
    (∀ i k, (wordKey i k false).items =
      wordUnder i ++ (#[wordSegment i k] ++ wordPivot i k ++ wordContacts i k ++ #[]) ++
        wordOver i false) ∧
    (∀ i k, wordSegment i k =
      (Plane.Exact.segment ((wordPath i).getD k (origin, origin)).1
        ((wordPath i).getD k (origin, origin)).2 |>.role (pieceRole i) |>.width 4
        |>.named s!"the image of the piece of word {i}" |>.withId "segment")) ∧
    (∀ i k, wordStep i k false =
      { moves := #[("segment", Plane.Exact.turnAbout (wordTurn i k).centre (wordTurn i k).turns)] ++
          wordFades i k false }) := by
  exact ⟨by unfold wordLoop1; with_reducible rfl, by unfold wordLoop2; with_reducible rfl,
    by unfold wordLoop3; with_reducible rfl, fun _ => by unfold wordLoop; with_reducible rfl,
    fun _ => by unfold wordLoopWith; with_reducible rfl, fun _ => rfl, fun _ => rfl,
    fun _ => by unfold wordLoopWith; with_reducible rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩

/-- The data of the key frames of the three loops (see `wordLoop_figures`). -/
theorem wordLoop_keys :
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
    wordArrives 1 = true ∧ wordArrives 2 = true ∧ wordArrives 3 = true ∧
    (wordEqualities 1).map (·.1) = [2, 3] ∧ (wordEqualities 2).map (·.1) = [1, 2] ∧
    (wordEqualities 3).map (·.1) = [0, 1, 4, 5] ∧
    ((wordPath 1).getLast? == some (-chordEnd + (phiInv + phiInv) * chordEnd,
      cutF + (phiInv + phiInv) * chordEnd)) = true ∧
    ((wordPath 2).getLast? == some (cutF + (phiInv + phiInv) * chordEnd,
      cutG + (phiInv + phiInv) * chordEnd)) = true ∧
    ((wordPath 3).getLast? == some (cutG + (phiInv + phiInv) * chordEnd - Zeta5.ofInt 2 * chordEnd,
      chordEnd + (phiInv + phiInv) * chordEnd - Zeta5.ofInt 2 * chordEnd)) = true := by
  repeat' apply And.intro
  all_goals decide +kernel

/-- The caption of every key of the three loops, written as a function of the key's data: the
piece and the word at the start; after letter `k`, the letter, the direction of its turn and its
centre; the ends that lie on the circle of the next letter (`wordEqualities`); and at the last key
the landing and the move of the piece. -/
theorem wordLoop_captions :
    [1, 2, 3].map pieceText = ["[−E, (1 − φ)E]", "[(1 − φ)E, (3 − 2φ)E]", "[(3 − 2φ)E, E]"] ∧
    (∀ i, shiftText i = if i == 3 then "(2φ − 4)E" else "(2φ − 2)E") ∧
    (∀ c, centreName c = if c == leftCentre then "−1" else "+1") ∧
    (∀ i, wordText i = " ".intercalate ((wordPiece i).1.map Letter.text)) ∧
    (∀ i k, wordCaption i k =
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
  body ++ contact ++ landing) := by
  exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end TDCSGFigures
```

{figref "exchanged-intervals"}[]: the animation `TDCSGFigures.exchangedIntervals`, whose last key
frame is the figure of the two rows, with its theorem `TDCSGFigures.exchangedIntervals_spec`, the
exact endpoint order before and after the return; the other key frames and the slides are stated
in `TDCSGFigures.exchangedIntervals_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Exact PILean.Plane

/-- The animation `exchangedIntervals` and the figure of the two rows, its last key frame. The
animation has one panel whose keys are `intervalKey k`, `k = 0, …, 4`, the last one
`exchangedIntervalsFinal`, and whose steps are made from the declared moves `intervalMoves`; its
poster is the last key. The figure draws the pieces of the row before the return (height `1/2`)
and of the row after (height `0`), each a segment from `(returnInterval i after).1` to
`(returnInterval i after).2` with its number above it, the pieces after the return with their
ids, and the names of the rows and of the ends. The two rows tile the same interval `[-1, 1]`:
before the return in the order `1, 2, 3`, after it in the order `3, 1, 2`. Not stated: how the
builders draw, the layout, the lettering, the style's colour values and the pixels. -/
theorem exchangedIntervals_spec :
    exchangedIntervals.panels = #[{ motion :=
      { keys := ((List.range 5).map intervalKey).toArray,
        steps := ((List.range 4).map fun k => exactStep (intervalMoves k)).toArray } }] ∧
    intervalKey 4 = exchangedIntervalsFinal ∧ exchangedIntervals.poster = 4 ∧
    exchangedIntervalsFinal.items =
      ((#[false, true].flatMap fun after => #[1, 2, 3].flatMap fun i => intervalBand i after) ++
        intervalNames) ∧
    intervalNames = #[
        Plane.Exact.label "before" ((-5 / 4 : Rat), (1 / 2 : Rat)) .left,
        Plane.Exact.label "after" ((-5 / 4 : Rat), (0 : Rat)) .left,
        Plane.Exact.label "−1" ((-1 : Rat), (0 : Rat)) .below,
        Plane.Exact.label "1" ((1 : Rat), (0 : Rat)) .below] ∧
    (∀ i after, intervalBand i after =
      let (a, b) := returnInterval i after
      let y := intervalRowY after
      let tag := fun (it : Item) (id : String) => if after then it.withId id else it
      #[tag (Plane.Exact.segment (a, y) (b, y) |>.width 5 |>.role (pieceRole i)
          |>.named s!"piece {i}, {if after then "after" else "before"} the word") s!"after-{i}",
        tag (Plane.Exact.label (toString i) ((a + b) * rat (1 / 2), y) .above
          |>.role (pieceRole i)) s!"after-label-{i}"]) ∧
    (∀ after, intervalRowY after = rat (if after then (0 : Rat) else 1 / 2)) ∧
    (∀ i after, returnInterval i after =
      let shift := if !after then rat 0 else phi * rat 2 - rat (if i == 3 then 4 else 2)
      (pieceEnds[i - 1]! + shift, pieceEnds[i]! + shift)) ∧
    pieceEnds = #[rat (-1), rat 1 - phi, rat 3 - phi * rat 2, rat 1] ∧
    (returnInterval 1 false).1 = rat (-1) ∧ (returnInterval 3 false).2 = rat 1 ∧
    (returnInterval 1 false).2 = (returnInterval 2 false).1 ∧
    (returnInterval 2 false).2 = (returnInterval 3 false).1 ∧
    (returnInterval 3 true).1 = rat (-1) ∧ (returnInterval 2 true).2 = rat 1 ∧
    (returnInterval 3 true).2 = (returnInterval 1 true).1 ∧
    (returnInterval 1 true).2 = (returnInterval 2 true).1 := by
  refine ⟨by unfold exchangedIntervals; with_reducible rfl,
    by unfold intervalKey; rw [if_pos (by decide)],
    by unfold exchangedIntervals; with_reducible rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links exchangedIntervals exchangedIntervals_spec

/-- The key frames of `exchangedIntervals` before the last and its slides. Key `k ≤ 3` draws, in
the frame of the figure of the two rows, the row before the return, the names, and a copy of each
piece (`intervalCopy`): pieces `1, …, k` at their places in the row after the return, the others
still on the row before. Step `k < 3` slides the copy of piece `k + 1` by `intervalSlide (k + 1)`,
`(2φ - 2, -1/2)` for pieces `1` and `2` and `(2φ - 4, -1/2)` for piece `3`: the move of its word
along the chord, as the return map `chordStep` applies word `i` to the midpoint of piece `i`, and
the drop from one row to the other. Step `3` fades the copies out and the row after in. Each
declared slide, applied exactly in `ℚ(√5)²` to the ends of the copies of one key, gives those of
the next (`intervalArrives`). The captions are written out. Not stated: how the builders draw, the
timing and the frames the browser draws between the key frames. -/
theorem exchangedIntervals_keys :
    exchangedIntervals.captions = intervalCaptions ∧
    intervalCaptions = #[
      "The three pieces of [−1, 1) before one return, in the order 1, 2, 3 (top row). The word \
        of each piece moves it along the chord.",
      "Word 1 moves piece 1, −1 ≤ t ≤ 1 − φ, by 2φ − 2 to the right.",
      "Word 2 moves piece 2, 1 − φ < t < 3 − 2φ, by 2φ − 2 to the right, beside the image of \
        piece 1.",
      "Word 3 moves piece 3, 3 − 2φ ≤ t < 1, by 2φ − 4 to the left, to the left end of the \
        interval.",
      "After one return the pieces read 3, 1, 2 on the same interval. Joined into a circle of \
        circumference two, the three moves are one rotation by 2φ − 2 = 2/φ."] ∧
    (∀ k, k ≤ 3 → intervalKey k = 
      { exchangedIntervalsFinal with
        items := intervalKeyItems k,
        info := { title := intervalCaptions.getD k "" } }) ∧
    (∀ k, intervalKeyItems k = (#[1, 2, 3].flatMap fun i => intervalBand i false) ++
      #[1, 2, 3].map (fun i => intervalCopy i (decide (i ≤ k))) ++ intervalNames) ∧
    (∀ i moved, intervalCopy i moved =
      let (a, b) := returnInterval i moved
      let y := intervalRowY moved
      Plane.Exact.segment (a, y) (b, y) |>.width 5 |>.role (pieceRole i)
        |>.named s!"a copy of piece {i}, moved by word {i}" |>.withId s!"piece-{i}") ∧
    (∀ k, k < 3 → intervalMoves k = [(s!"piece-{k + 1}", .slide (intervalSlide (k + 1)))]) ∧
    moveKinds (intervalMoves 3) = [("piece-1", "vanish"), ("after-1", "appear"),
      ("after-label-1", "appear"), ("piece-2", "vanish"), ("after-2", "appear"),
      ("after-label-2", "appear"), ("piece-3", "vanish"), ("after-3", "appear"),
      ("after-label-3", "appear")] ∧
    (∀ i, intervalSlide i = ((returnInterval i true).1 - (returnInterval i false).1,
      intervalRowY true - intervalRowY false)) ∧
    [1, 2, 3].all (fun i => let v := intervalSlide i
      v.1 == phi * rat 2 - rat (if i == 3 then 4 else 2) && v.2 == rat (-1 / 2)) = true ∧
    [1, 2, 3].all (fun i =>
      let m := ((returnInterval i false).1 + (returnInterval i false).2) * rat (1 / 2)
      (chordStep m).1 == i && (chordStep m).2 - m == (intervalSlide i).1) = true ∧
    intervalArrives = true := by
  refine ⟨by unfold exchangedIntervals; with_reducible rfl, rfl, fun k hk => ?_, fun _ => rfl,
    fun _ _ => rfl, fun k hk => ?_, ?_, fun _ => rfl, ?_⟩
  · simp only [intervalKey, show ¬3 < k by omega, if_false]
  · simp only [intervalMoves, hk, if_true]
  all_goals first | decide +kernel | (repeat' apply And.intro) <;> decide +kernel

end TDCSGFigures
```

{figref "chord-orbit"}[]: the animation `TDCSGFigures.chordOrbit`, whose last key frame is the
figure of the first 24 returns, with its theorem `TDCSGFigures.chordOrbit_spec`; the other key
frames and the hops are stated in `TDCSGFigures.chordOrbit_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- The animation `chordOrbit` and the figure of the first 24 returns, its last key frame. The
animation has one panel whose keys are `orbitKey k`, `k = 0, …, orbitHops + 1` (`orbitHops = 12`),
the last one `chordOrbitFinal`, and whose steps are made from the declared moves `orbitMoves`; its
poster is the last key. What `chordOrbitFinal` draws, item for item, and why: the frame
(`chordOrbitFrame`, written out: the bands of the three pieces, the pieces of `[-1, 1]` with their
labels, the end `-1` in the range and the end `1` not, the axis with ticks at
`-1, 1 - φ, 3 - 2φ, 1` and its name), the axis of steps (`stepAxis`, written out: the step number
`k` downwards, ticks at `k = 0, 6, 12, 18, 24` and its name), then one point per row
`k = 0, …, 24` at `(t_k, -k/20)` (`rowPoint`, written out, with its id), in the colour of word
`w_k` and recording that it lies in the band of piece `w_k` and outside the other two. The rows
are written out: `t_k = a + b√5` with the word applied next. The facts hold exactly in `ℚ(√5)`:
every `t_k` lies in `[-1, 1)` and in the piece of its word (`t ≤ 1 - φ` for word 1,
`1 - φ < t < 3 - 2φ` for word 2, `t ≥ 3 - 2φ` for word 3), `t_(k+1) = t_k + 2φ - 2` for words 1, 2
and `t_k + 2φ - 4` for word 3, and the 25 values are pairwise distinct. Not stated: how the
builders and modifiers draw, the layout, the lettering, the style's colour values and the
pixels. -/
theorem chordOrbit_spec :
    chordOrbit.panels = #[{ motion :=
      { keys := ((List.range (orbitHops + 2)).map orbitKey).toArray,
        steps := ((List.range (orbitHops + 1)).map fun k =>
          exactStep (orbitMoves k)).toArray } }] ∧
    orbitHops = 12 ∧ orbitKey (orbitHops + 1) = chordOrbitFinal ∧
    chordOrbit.poster = orbitHops + 1 ∧ chordOrbitFinal.items = chordOrbitItems ∧
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
        |>.incident (if w == 3 then .inside else .outside) "the band of piece 3"
        |>.withId s!"row-{k}")) ∧
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
      Plane.Exact.tickAt (tPoint pieceEnds[3]! axisY)
        (tPoint pieceEnds[0]! axisY) (tPoint pieceEnds[3]! axisY),
      Plane.Exact.label "−1" (tPoint pieceEnds[0]! axisY) .below |>.size 13,
      Plane.Exact.label "1 − φ" (tPoint pieceEnds[1]! axisY) .belowLeft |>.size 13,
      Plane.Exact.label "3 − 2φ" (tPoint pieceEnds[2]! axisY) .belowRight |>.size 13,
        Plane.Exact.label "1" (tPoint pieceEnds[3]! axisY) .below |>.size 13,
      Plane.Exact.label "t, the point tE of the chord" (tPoint (rat 0) (axisY - rat (3 / 20)))
        .below] ∧
    stepAxisX = rat (-11 / 10) ∧ stepTicks = [0, 6, 12, 18, 24] ∧
    stepAxis = #[
      Plane.Exact.segment (tPoint stepAxisX (rowY 0)) (tPoint stepAxisX (rowY orbitSteps))
        |>.named "the step number k, one row per step"] ++
      (stepTicks.toArray.map fun k => Plane.Exact.tickAt (tPoint stepAxisX (rowY k))
        (tPoint stepAxisX (rowY 0)) (tPoint stepAxisX (rowY orbitSteps))) ++
      (stepTicks.toArray.map fun k =>
        Plane.Exact.label s!"{k}" (tPoint stepAxisX (rowY k)) .left) ++
      #[Plane.Exact.label "step k" (tPoint (stepAxisX - rat (1 / 5)) (rowY 12)) .left] ∧
    chordOrbitItems = chordOrbitFrame ++ stepAxis ++
      (chordRows orbitSteps).mapIdx (fun k (w, t) => rowPoint k w t) ∧
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
  refine ⟨by unfold chordOrbit; with_reducible rfl, rfl,
    by unfold orbitKey; rw [if_pos (by decide)], by unfold chordOrbit; with_reducible rfl, rfl, rfl,
    rfl, fun _ => rfl, rfl, rfl, fun _ => rfl,
    fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links chordOrbit chordOrbit_spec

/-- The key frames of `chordOrbit` before the last and its hops. Key `k ≤ orbitHops` draws, in the
frame of the figure of the returns, the frame, the axis of steps, the points of rows `0, …, k - 1`
and the point that hops at row `k`, on `t_k` (`orbitHopper`). Step `k < orbitHops` slides it by
`(t_{k+1} - t_k, -1/20)`, one return: the move `2φ - 2` or `2φ - 4` of the word applied at `t_k`
(`chordStep`) and one row down, and fades in the point of row `k` that it leaves; step
`orbitHops` fades it out and the rows from `orbitHops` on in. Each declared move, applied exactly
in `ℚ(√5)²` to the anchors of the actors of one key, gives those of the next (`orbitArrives`). The
captions, built from the rows (`orbitCaption`), are written out. Not stated: how the builders
draw, the timing and the frames the browser draws between the key frames. -/
theorem chordOrbit_keys :
    (∀ k, k ≤ orbitHops → orbitKey k = 
      { chordOrbitFinal with
        items := orbitKeyItems k,
        info := { title := orbitCaption k } }) ∧
    (∀ k, orbitKeyItems k = chordOrbitFrame ++ stepAxis ++
      ((chordRows orbitSteps).extract 0 k).mapIdx (fun j (w, t) => rowPoint j w t) ++
      #[orbitHopper k]) ∧
    (∀ k, orbitHopper k =
      (Plane.Exact.point (tPoint ((chordRows orbitSteps).getD k (0, rat 0)).2 (rowY k)) |>.size 5
        |>.named "the point tE of the orbit, one return per hop" |>.withId "hop")) ∧
    (∀ k, k < orbitHops → orbitMoves k =
      [("hop", .slide (((chordRows orbitSteps).getD (k + 1) (0, rat 0)).2 -
          ((chordRows orbitSteps).getD k (0, rat 0)).2, rowY (k + 1) - rowY k)),
        (s!"row-{k}", .appear)]) ∧
    moveKinds (orbitMoves orbitHops) = [("hop", "vanish")] ++
      (List.range 13).map (fun j => (s!"row-{12 + j}", "appear")) ∧
    (List.range orbitHops).all (fun k =>
      let (w, t) := (chordRows orbitSteps).getD k (0, rat 0)
      ((chordRows orbitSteps).getD (k + 1) (0, rat 0)).2 - t == (chordStep t).2 - t &&
        (chordStep t).1 == w) = true ∧
    orbitArrives = true ∧
    chordOrbit.captions = ((List.range (orbitHops + 2)).map orbitCaption).toArray ∧
    (∀ w, orbitShiftText w = if w == 3 then "2φ − 4" else "2φ − 2") ∧
    (∀ k, orbitCaption k =
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
      irrational, so the points never repeat.") := by
  refine ⟨fun k hk => ?_, fun _ => rfl, fun _ => rfl, fun k hk => ?_, ?_, ?_, ?_,
    by unfold chordOrbit; with_reducible rfl, fun _ => rfl, fun _ => rfl⟩
  · simp only [orbitKey, show ¬orbitHops < k by omega, if_false]
  · simp only [orbitMoves, hk, if_true]
  all_goals decide +kernel

end TDCSGFigures
```


# The figure of Part II

%%%
tag := "theorems-part-two"
file := "Theorems-part-two"
%%%

{figref "radius-line-finite"}[]: the figure `TDCSGFigures.radiusLineFinite`
and its theorem `TDCSGFigures.radiusLineFinite_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

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

figure_links radiusLineFinite radiusLineFinite_spec

end TDCSGFigures
```

# The figures of chapter 4

%%%
tag := "theorems-lift"
file := "Theorems-lift"
%%%

{figref "unit-steps"}[]: the figure `TDCSGFigures.Lift.unitSteps`
and its theorem `TDCSGFigures.Lift.unitSteps_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Lift

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- What `unitSteps` draws, item for item, and why its records are right. The data are the window
centre `x = 1/2`, its radius `r/2 = 39/40`, the point `rimPoint = x + (39/40)(3/5, -4/5)` of its
circle that ends the drawn radius, and the unit steps `ζʲ = P(eⱼ)`. The items are written out in
drawing order, the steps and their ends by the builders `activeStep`, `inactiveStep`,
`activeEnd`, `inactiveEnd` and `endLabel`, whose definitions are stated: a step ending in the
window is solid in the colour of right centres, one ending outside is dashed and faint. The steps
drawn as ending in the window are exactly those whose labels `eⱼ` pass the exact window test
`|ζʲ - 1/2|² ≤ (39/40)²` (`activeSteps = [0, 1, 4]`); `ζ` and `ζ⁴` pass it with a margin
`(39/40)² - |ζ - 1/2|²` between `0` and `0.01`, and `ζ²` (like `ζ³`) fails it. The radius ends on
the window's circle and `0` lies inside it. Not stated: how the builders and modifiers
draw, the layout, the lettering, the style's colour values and the pixels. -/
theorem unitSteps_spec :
    centrePoint = (1 / 2, 0) ∧ halfRadius = 39 / 40 ∧
    rimPoint = (1 / 2 + 39 / 40 * (3 / 5), -(39 / 40 * (4 / 5))) ∧
    (∀ j, activeStep j = (Plane.Exact.segment origin (zeta j) |>.role "right" |>.width 2.5
      |>.named s!"the step from 0 to {zetaName j} = P({basisName j}), ending in the window"
      |>.declRef `TDCSG.Five.Label.proj_basis)) ∧
    (∀ j, inactiveStep j = (Plane.Exact.segment origin (zeta j) |>.faint |>.dashed
      |>.named s!"the step from 0 to {zetaName j} = P({basisName j}), ending outside the window"
      |>.declRef `TDCSG.Five.Label.proj_basis)) ∧
    (∀ j, activeEnd j = (Plane.Exact.point (zeta j) |>.role "right" |>.size 5
      |>.named s!"P({basisName j}) = {zetaName j}, label {basisName j}, weight 1"
      |>.incident .inside "the window")) ∧
    (∀ j, inactiveEnd j = (Plane.Exact.point (zeta j) |>.faint |>.marker .ring |>.size 5
      |>.named s!"P({basisName j}) = {zetaName j}, label {basisName j}, weight 1"
      |>.incident .outside "the window")) ∧
    (∀ j, endLabel j true =
      (Plane.Exact.label s!"{basisName j} ↦ {zetaName j}" (zeta j) .auto |>.role "right")) ∧
    (∀ j, endLabel j false =
      (Plane.Exact.label s!"{basisName j} ↦ {zetaName j}" (zeta j) .auto |>.faint)) ∧
    unitSteps.items = #[
      Plane.Exact.disk centrePoint halfRadius |>.role "window" |>.fillOpacity 0.07
        |>.named "the window" |>.describedBy "the closed disk |w − x| ≤ r/2, x = 1/2, r = 1.95"
        |>.declRef `TDCSG.Five.InWindow,
      Plane.Exact.segment centrePoint rimPoint |>.role "window" |>.width 1.5 |>.dashed
        |>.named "a radius r/2 = 0.975 of the window",
      Plane.Exact.labelBeside "r/2 = 0.975" centrePoint rimPoint |>.role "window",
      activeStep 0, activeStep 1, inactiveStep 2, inactiveStep 3, activeStep 4,
      activeEnd 0, activeEnd 1, inactiveEnd 2, inactiveEnd 3, activeEnd 4,
      Plane.Exact.point origin |>.role "left" |>.size 5
        |>.named "the current left center P(0) = 0, label 0, weight 0"
        |>.incident .inside "the window",
      Plane.Exact.point centrePoint |>.role "window" |>.marker .cross
        |>.named "the window center x = 1/2" |>.incident .inside "the window"
        |>.incident .on "the step from 0 to 1 = P(e₀), ending in the window",
      endLabel 0 true, endLabel 1 true, endLabel 2 false, endLabel 3 false, endLabel 4 true,
      Plane.Exact.label "0" origin .auto |>.role "left",
      Plane.Exact.label "x = 1/2" centrePoint .auto |>.role "window",
      Plane.Exact.label "window |w − x| ≤ r/2" ((6 / 5 : Rat), (-11 / 10 : Rat))
        |>.role "window"] ∧
    activeSteps = [0, 1, 4] ∧
    (39 / 40 * (3 / 5) : Rat) ^ 2 + (39 / 40 * (4 / 5)) ^ 2 = (39 / 40) ^ 2 ∧
    windowDistSq (zeta 1) = windowDistSq (zeta 4) ∧
    QSqrt.lt (windowDistSq (zeta 1)) halfRadiusSq = true ∧
    QSqrt.lt (halfRadiusSq - windowDistSq (zeta 1)) (rat (1 / 100)) = true ∧
    QSqrt.lt halfRadiusSq (windowDistSq (zeta 2)) = true ∧
    inWindow radiusSq centreX zeroLabel = true := by
  refine ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links unitSteps unitSteps_spec

end TDCSGFigures.Lift
```

{figref "change-of-frame"}[]: the animation `TDCSGFigures.Lift.framePair`, an illustration, and the
data of its key frames, `TDCSGFigures.Lift.framePair_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Lift

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- The frame pair and the data its key frames are drawn from. The figure is the motion of the
default configuration (`FramePairConfig.motion`): the word `a a b a b a a b b a b b` applied to
`z = 0` at `r = 1.95`, without the word strip; its two panels' keys are the key figures
`FramePairConfig.keys`, its steps are made by `panelStep` from the declared moves
`FramePairConfig.frameSteps`, and its captions are `FramePairConfig.keyCaption` of each key.
The states after `0, 1, …, 12` letters are computed exactly: the labels `n` of the current left
centre and the direction indices `j`, written out; the letters `3`, `5` and `10` do not act, every
other letter does (the exact disk test `Early.Letter.covers`); every state satisfies the framing
equation `2 (x - P(n)) = ζʲ (y + 1)` of `TDCSG.Five.Framed` exactly. The sixteen keys, written out,
are one per state and one more, showing the ring, for each letter that does not act; the caption
of each key begins with its letter and what it does. Every declared move, a fifth of a turn of
the point about the centre of the letter's halved disk on the left, of the body of centres and
riding disks about the active centre on the right, or a ring appearing or vanishing, carries the
items of one key onto those of the next exactly in `ℚ(ζ₅)`, and each ring lies about the centre
of its letter's disk in both panels, a centre outside the window (`FramePairConfig.allArrive`,
`ringsPlaced`; the general statements are `TDCSG.Five.halved_genA`, `TDCSG.Five.halved_genB` and
`TDCSG.Five.framePicture_genA_genB`). Not stated: how the builders draw, the layout, the timing
and the frames the browser draws between the key frames. -/
theorem framePair_keys :
    framePair = ({} : FramePairConfig).motion ∧
    ({} : FramePairConfig).word = word ∧ ({} : FramePairConfig).radius = radius ∧
    ({} : FramePairConfig).strip = false ∧
    word = [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] ∧ radius = 39 / 20 ∧
    framePair.panels =
      #[{ title := "Traditional view",
          motion := { keys := ({} : FramePairConfig).leftKeys,
                      steps := ({} : FramePairConfig).leftSteps } },
        { title := "Moving frame",
          motion := { keys := ({} : FramePairConfig).rightKeys,
                      steps := ({} : FramePairConfig).rightSteps } }] ∧
    (∀ cfg : FramePairConfig, cfg.leftKeys = cfg.keys.map fun p => { p.1 with view := none }) ∧
    (∀ cfg : FramePairConfig, cfg.rightKeys = cfg.keys.map fun p => { p.2 with view := none }) ∧
    (∀ cfg : FramePairConfig, cfg.leftSteps = cfg.frameSteps.toArray.mapIdx fun j s =>
      let now := cfg.stripMarkIds j
      let next := cfg.stripMarkIds (j + 1)
      panelStep s.leftTurn s.leftTurning (s.appearLeft ++ next.filter (!now.contains ·))
        (s.vanishLeft ++ now.filter (!next.contains ·))) ∧
    (∀ cfg : FramePairConfig, cfg.rightSteps = cfg.frameSteps.toArray.map fun s =>
      panelStep s.rightTurn s.rightTurning s.appearRight s.vanishRight) ∧
    (∀ t turning appear vanish, panelStep t turning appear vanish =
      let turns : Array (String × Move) := match t with
        | some t => turning.toArray.map fun id => (id, Plane.Exact.turnAbout t.centre t.turns)
        | none => #[]
      let moves := turns ++ appear.toArray.map (·, Move.appear) ++
        vanish.toArray.map (·, Move.vanish)
      if moves.isEmpty then MotionStep.idle else { moves }) ∧
    framePair.captions =
      ((List.range ({} : FramePairConfig).keyCount).map ({} : FramePairConfig).keyCaption).toArray ∧
    (states.map (·.n) == [#[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0],
      #[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0], #[1, -1, 0, 0, 0],
      #[1, 0, -1, 0, 0], #[1, 0, -1, 0, 0], #[1, 0, 0, -1, 0], #[1, 0, 0, 0, -1]]) = true ∧
    states.map (·.j) = [0, 1, 2, 2, 3, 3, 4, 0, 1, 2, 2, 3, 4] ∧
    states.map (·.acted) =
      [true, true, true, false, true, false, true, true, true, true, false, true, true] ∧
    states.all State.framed = true ∧
    (({} : FramePairConfig).keyRefs.map fun r => (r.state, r.mark)) =
      [(0, false), (1, false), (2, false), (3, true), (3, false), (4, false), (5, true),
        (5, false), (6, false), (7, false), (8, false), (9, false), (10, true), (10, false),
        (11, false), (12, false)] ∧
    ((List.range 16).zip ["Start:", "Letter 1, a, acts:", "Letter 2, a, acts:",
        "Letter 3, b, does not act:", "Letter 3, b, did not act:", "Letter 4, a, acts:",
        "Letter 5, b, does not act:", "Letter 5, b, did not act:", "Letter 6, a, acts:",
        "Letter 7, a, acts:", "Letter 8, b, acts:", "Letter 9, b, acts:",
        "Letter 10, a, does not act:", "Letter 10, a, did not act:", "Letter 11, b, acts:",
        "Letter 12, b, acts:"]).all (fun (j, h) =>
      (({} : FramePairConfig).keyCaption j).startsWith h) = true ∧
    ({} : FramePairConfig).keyCount = 16 ∧ ({} : FramePairConfig).allArrive = true ∧
    ({} : FramePairConfig).ringsPlaced = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ _ _ _ => rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

end TDCSGFigures.Lift
```

# The figures of chapter 5

%%%
tag := "theorems-lens"
file := "Theorems-lens"
%%%

{figref "lens-estimate"}[]: the figure `TDCSGFigures.Lens.lensEstimate`
and its theorem `TDCSGFigures.Lens.lensEstimate_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Lens

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- What `lensEstimate` draws, item for item, and why its records are right. The data are the
half radius `r/2 = 9/10`, `c₁ = Re ζ`, `s² = 1 - c₁²`, `h² = (r/2)² - 1/4`, the tip
`(c₁/2 + √(h² s²), √(s²/4) - √(h² c₁²))`, `u = ζ` and its foot `(c₁, 0)`,
`v* = (1 + ζ - ζ²)/2`, `κ`, `η` and the two half-planes as the rectangles
`[a, 1.75] × [-1.1, 2.4]` of the shown box, outlined; the margin `η` between the two lines is
drawn as a dimension line. The items are written out in drawing order. The records hold exactly:
the tip lies on both circles (`tipFacts`: the cross terms of `|tip|²` and `|tip - u|²` cancel
and the rest is `(r/2)²`) and left of `κ - η`; `|u|² = 1 > (9/10)²` puts `0` and `u` outside
each other's disk; `v*` lies at distance `R/2 > r/2` from `0` and `u`, on `Re v = κ` and right
of `κ - η`; the tip's real part is at most `κ - 2η`. Not stated: how the builders and modifiers
draw, the layout, the lettering, the style's colour values and the pixels. -/
theorem lensEstimate_spec :
    tip (9 / 10) = ⟨{ base := cosine * rat (1 / 2), roots := [(1, hSq (9 / 10) * sineSq)] },
      { roots := [(1, sineSq * rat (1 / 4)), (-1, hSq (9 / 10) * (cosine * cosine))] }⟩ ∧
    cosine = (zeta 1).realPart ∧ sineSq = rat 1 - cosine * cosine ∧
    vStar = ⟨Zeta5.ofInt 1 + zeta 1 - zeta 2, 2⟩ ∧
    lensEstimate.items = #[
      Plane.Exact.polygon (halfPlane (cut (rat (4 * (9 / 10) * (9 / 10))))) |>.faint |>.filled
        |>.width 1 |>.dashed |>.fillOpacity 0.16 |>.named "the half-plane Re v ≥ κ − η"
        |>.describedBy "where the lens estimate puts no point of the lens, at r = 1.8"
        |>.declRef `TDCSG.Five.div_two_lt_norm_sub_of_le_re,
      Plane.Exact.polygon (halfPlane kappa) |>.faint |>.filled |>.width 1 |>.fillOpacity 0.18
        |>.named "the half-plane Re v ≥ κ"
        |>.describedBy "κ = (2φ + 1)/4 = (1 + L)/2, L = φ − 1/2",
      Plane.Exact.line origin rightCentre |>.faint |>.width 1 |>.named "the real axis",
      Plane.Exact.disk origin (9 / 10 : Rat) |>.noFill |>.role "window"
        |>.named "the circle |v| = r/2" |>.describedBy "the closed disk |v| ≤ r/2, r = 1.8",
      Plane.Exact.disk (zeta 1) (9 / 10 : Rat) |>.noFill |>.role "window" |>.dashed
        |>.named "the circle |v − u| = r/2"
        |>.describedBy "the closed disk |v − u| ≤ r/2 about u = ζ, r = 1.8",
      Plane.Exact.lens origin (zeta 1) (9 / 10 : Rat) (9 / 10 : Rat) |>.role "lens" |>.noOutline
        |>.fillOpacity 0.12 |>.named "the lens",
      Plane.Exact.segment uSurd ⟨Surd.ofQ cosine, Surd.ofQ ⟨0, 0⟩⟩ |>.faint |>.width 1
        |>.dashed #[2, 3] |>.named "the foot of u on the real axis",
      Plane.Exact.segment (cut (rat (4 * (9 / 10) * (9 / 10))), marginY) (kappa, marginY)
        |>.width 1 |>.named "the margin η = (3 + φ − r²)/16 between the cuts κ − η and κ"
        |>.declRef `TDCSG.Five.IsGoodLevel,
      Plane.Exact.tickAt (cut (rat (4 * (9 / 10) * (9 / 10))), marginY)
        (cut (rat (4 * (9 / 10) * (9 / 10))), marginY) (kappa, marginY),
      Plane.Exact.tickAt (kappa, marginY) (cut (rat (4 * (9 / 10) * (9 / 10))), marginY)
        (kappa, marginY),
      Plane.Exact.labelBeside "η" (cut (rat (4 * (9 / 10) * (9 / 10))), marginY)
        (kappa, marginY),
      Plane.segment ⟨0, 0⟩ (radiusEnd (RealValue.toFloat (9 / 10 : Rat))) |>.role "window"
        |>.width 1.5 |>.dashed |>.named "a radius r/2 of the disk |v| ≤ r/2",
      Plane.labelBeside "r/2" ⟨0, 0⟩ (radiusEnd (RealValue.toFloat (9 / 10 : Rat)))
        |>.role "window",
      Plane.Exact.point origin |>.role "window" |>.named "0, the center of |v| ≤ r/2"
        |>.incident .inside "the circle |v| = r/2"
        |>.incident (otherSide (rat (9 / 10 * (9 / 10)))).incidence "the circle |v − u| = r/2"
        |>.incident (Side.lens .inside (otherSide (rat (9 / 10 * (9 / 10))))).incidence
          "the lens",
      Plane.Exact.point (zeta 1) |>.role "window" |>.named "u = ζ, the center of |v − u| ≤ r/2"
        |>.incident .inside "the circle |v − u| = r/2"
        |>.incident (otherSide (rat (9 / 10 * (9 / 10)))).incidence "the circle |v| = r/2"
        |>.incident (Side.lens .inside (otherSide (rat (9 / 10 * (9 / 10))))).incidence
          "the lens",
      Plane.Exact.point ((cosine, ⟨0, 0⟩) : QSqrt5 × QSqrt5) |>.faint |>.size 3
        |>.named "c₁ = Re u = (φ − 1)/2 on the real axis" |>.incident .on "the real axis",
      Plane.Exact.point (tip (9 / 10)) |>.size 5
        |>.named "the tip of the lens: its corner of largest real part"
        |>.incident .on "the circle |v| = r/2" |>.incident .on "the circle |v − u| = r/2"
        |>.incident .on "the lens" |>.incident .outside "the half-plane Re v ≥ κ − η"
        |>.incident .outside "the half-plane Re v ≥ κ",
      Plane.Exact.point vStar
        |>.named "v∗ = 1 + t u, t = 1/2 − c₁, at distance R/2 from 0 and u"
        |>.incident .outside "the circle |v| = r/2" |>.incident .outside "the circle |v − u| = r/2"
        |>.incident .outside "the lens" |>.incident .on "the half-plane Re v ≥ κ"
          |>.incident .inside "the half-plane Re v ≥ κ − η",
      Plane.Exact.label "v∗" vStar .auto,
      Plane.Exact.label "0" origin .auto |>.role "window",
      Plane.Exact.label "u = ζ" (zeta 1) .auto |>.role "window",
      Plane.Exact.label "c₁" ((cosine, ⟨0, 0⟩) : QSqrt5 × QSqrt5) .auto,
      Plane.label "tip" (PlanePoint.toPoint (tip (9 / 10))) .auto,
      Plane.Exact.label "lens" ((rat (1 / 10), rat (11 / 20)) : QSqrt5 × QSqrt5) |>.role "lens",
      Plane.Exact.label "|v| ≤ r/2" ((rat (3 / 10), rat (-11 / 20)) : QSqrt5 × QSqrt5)
        |>.role "window",
      Plane.Exact.label "|v − u| ≤ r/2" ((rat (9 / 20), rat (3 / 2)) : QSqrt5 × QSqrt5)
        |>.role "window",
      Plane.Exact.label "Re v ≥ κ" ((kappa, cutLabelY) : QSqrt5 × QSqrt5) .right,
      Plane.Exact.label "Re v ≥ κ − η →"
        ((cut (rat (4 * (9 / 10) * (9 / 10))), cutLabelY) : QSqrt5 × QSqrt5) .left] ∧
    tipFacts (9 / 10) = true ∧ tipReLe (9 / 10) = true ∧
    (otherSide (rat (9 / 10 * (9 / 10))) == .outside) = true ∧
    (vStar.normSq == criticalSq * rat (1 / 4)) = true ∧
    ((vStar - ZetaFrac.ofZeta (zeta 1)).normSq == criticalSq * rat (1 / 4)) = true ∧
    (vStar.realPart == kappa) = true ∧
    QSqrt.lt (rat (9 / 10 * (9 / 10))) (criticalSq * rat (1 / 4)) = true ∧
    QSqrt.lt (cut (rat (4 * (9 / 10) * (9 / 10)))) kappa = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links lensEstimate lensEstimate_spec

end TDCSGFigures.Lens
```

{figref "lens-radius"}[]: the figure `TDCSGFigures.Lens.lensRadius`
and its theorem `TDCSGFigures.Lens.lensRadius_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Lens

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- What `lensRadius` shows. It is the slider of `sliderFrames`: the lens picture `frameAt ρ` at
the half radii `ρ = 9/10, 1, 26/25, 53/50` (`r = 1.8, 2, 2.08, 2.12`), then `frameCritical` at
`R`. At every radius below `R` the tip lies on both circles and left of `κ - η` (`tipFacts`), its
real part is at most `κ - 2η` (`tipReLe`), and `v*` lies outside both disks; at `R` the tip is
`v*`, on both circles of radius `R/2` with real part `κ`, where `η = 0`. The disk `|v| ≤ r/2`
stays left of `κ - η` at the first three radii and crosses it at `2.12`. Not stated: the items of
each frame (built by `lensItems` from these data), the layout and the pixels. -/
theorem lensRadius_spec :
    lensRadius = Plane.slider "r" sliderFrames ∧
    sliderFrames = (sliderRadii.map fun (ρ, t) => (t, frameAt ρ t (ρ == 9 / 10) false)).push
      ("R", frameCritical) ∧
    sliderRadii = #[(9 / 10, "1.8"), (1, "2"), (26 / 25, "2.08"), (53 / 50, "2.12")] ∧
    sliderRadii.all (fun (ρ, _) => tipFacts ρ && tipReLe ρ &&
      QSqrt.lt (rat (ρ * ρ)) (criticalSq * rat (1 / 4))) = true ∧
    (vStar.normSq == criticalSq * rat (1 / 4)) = true ∧
    ((vStar - ZetaFrac.ofZeta (zeta 1)).normSq == criticalSq * rat (1 / 4)) = true ∧
    (vStar.realPart == kappa) = true ∧ (margin criticalSq == rat 0) = true ∧
    (sliderRadii.map fun (ρ, _) => QSqrt.lt (rat ρ) (cut (rat (4 * ρ * ρ)))) =
      #[true, true, true, false] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links lensRadius lensRadius_spec

end TDCSGFigures.Lens
```

# The figures of chapter 6

%%%
tag := "theorems-levels"
file := "Theorems-levels"
%%%

{figref "terminal-crossing"}[]: the figure `TDCSGFigures.Levels.terminalCrossing`
and its theorem `TDCSGFigures.Levels.terminalCrossing_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Levels

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- What `terminalCrossing` draws, item for item, and why its records are right. The data are
`r = 53/25`, `x = 59/125`, `n = (4, -3, 1, 1, -3)` and the leaf `n + e₀`; the items are written
out in drawing order, those of the four neighbours `n + eₖ` and the four candidates `n + e₀ - eₖ`
(`k = 1, …, 4`) by the builders `neighbourEdge`, `rejectedStep`, `neighbourPoint`,
`neighbourLabel`, `candidatePoint` and `candidateLabel`, whose definitions are stated. The
records hold exactly: `n` has weight zero and its level `n₀ = 4` is good at `r = 2.12`,
`x = 0.472`; `n`, the leaf and every `n + eₖ` lie inside the window and every `n + e₀ - eₖ`
outside it (`windowSide`, from `|q P(m) - p|² ≤ q² r²/4` for `x = p/q`), so the leaf has no
neighbour but `n`; the leaf's real part `8 - 4φ` exceeds the cut `Re x + κ - η`, and
`P(n) = 7 - 4φ` is real. Not stated: how the builders and modifiers draw, the layout, the
lettering, the style's colour values and the pixels. -/
theorem terminalCrossing_spec :
    crossN = #[4, -3, 1, 1, -3] ∧ leaf = shift crossN 0 1 ∧ crossX = 59 / 125 ∧
    crossRadius = 53 / 25 ∧ crossCut = rat crossX + kappa - margin crossRadiusSq ∧
    (∀ k, neighbourEdge k = (Plane.Exact.segment (proj crossN) (proj (shift crossN k 1))
      |>.role "right" |>.width 1.5 |>.named s!"the edge from n to n + e{sub k}")) ∧
    (∀ k, rejectedStep k = (Plane.Exact.segment (proj leaf) (proj (shift leaf k (-1)))
      |>.faint |>.width 1.5 |>.dashed
      |>.named s!"the rejected step from n + e₀ to n + e₀ − e{sub k}")) ∧
    (∀ k, neighbourPoint k = (Plane.Exact.point (proj (shift crossN k 1)) |>.role "right"
      |>.marker .square
      |>.named s!"n + e{sub k} = {labelText (shift crossN k 1)}, weight 1, a neighbour of n"
      |>.incident (windowSide (shift crossN k 1)).incidence "the window")) ∧
    (∀ k, neighbourLabel k =
      (Plane.Exact.label s!"n + e{sub k}" (proj (shift crossN k 1)) .auto |>.role "right")) ∧
    (∀ k, candidatePoint k = (Plane.Exact.point (proj (shift leaf k (-1))) |>.faint
      |>.marker .ring
      |>.named s!"n + e₀ − e{sub k} = {labelText (shift leaf k (-1))}, weight 0, outside the window"
      |>.incident (windowSide (shift leaf k (-1))).incidence "the window")) ∧
    (∀ k p, candidateLabel k p =
      Plane.Exact.label s!"n + e₀ − e{sub k}" (proj (shift leaf k (-1))) p) ∧
    terminalCrossing.items = #[
      Plane.Exact.polygon crossHalfPlane |>.faint |>.filled |>.noOutline |>.fillOpacity 0.16
        |>.named "the half-plane Re w ≥ Re x + κ − η"
        |>.describedBy "beyond the cut of the lens estimate, turned to the direction j = 0"
        |>.declRef `TDCSG.Five.div_two_lt_norm_sub_of_le_re,
      Plane.Exact.disk crossXPoint (53 / 50 : Rat) |>.role "window" |>.fillOpacity 0.07
        |>.named "the window" |>.describedBy "the closed disk |w − x| ≤ r/2, r = 2.12, x = 0.472"
        |>.declRef `TDCSG.Five.InWindow,
      Plane.Exact.segment crossXPoint crossRim |>.role "window" |>.width 1.5 |>.dashed
        |>.named "a radius r/2 = 1.06 of the window",
      Plane.Exact.labelBeside "r/2" crossXPoint crossRim |>.role "window",
      neighbourEdge 1, neighbourEdge 2, neighbourEdge 3, neighbourEdge 4,
      rejectedStep 1, rejectedStep 2, rejectedStep 3, rejectedStep 4,
      Plane.Exact.segment (proj crossN) (proj leaf) |>.width 3.5
        |>.named "the edge from n to n + e₀: it raises n₀ from the good level 4 to 5"
        |>.declRef `TDCSG.Five.IsGoodLevel.leaf,
      Plane.Exact.polygon zoomBox |>.width 1 |>.named "the square enlarged in the next figure",
      neighbourPoint 1, neighbourLabel 1, neighbourPoint 2, neighbourLabel 2,
      neighbourPoint 3, neighbourLabel 3, neighbourPoint 4, neighbourLabel 4,
      candidatePoint 1, candidateLabel 1 .belowLeft, candidatePoint 2, candidateLabel 2 .below,
      candidatePoint 3, candidateLabel 3 .above, candidatePoint 4, candidateLabel 4 .aboveLeft,
      Plane.Exact.point (proj crossN) |>.role "left" |>.size 5
        |>.named s!"n = {labelText crossN}, weight 0, P(n) = 7 − 4φ, at the good level n₀ = 4"
        |>.incident (windowSide crossN).incidence "the window",
      Plane.Exact.point (proj leaf) |>.role "right" |>.marker .square |>.size 5
        |>.named s!"the leaf n + e₀ = {labelText leaf}, weight 1, P = 8 − 4φ"
        |>.incident (windowSide leaf).incidence "the window"
        |>.incident .inside "the half-plane Re w ≥ Re x + κ − η",
      Plane.Exact.label "n" (proj crossN) (.toward (Plane.deg 100)) (some 10) |>.role "left"
        |>.italic,
      Plane.Exact.label "n₀ = 4 → 5" ((rat (21 / 20), rat (2 / 25)) : QSqrt5 × QSqrt5),
      Plane.Exact.label "window" ((rat 0, rat (6 / 5)) : QSqrt5 × QSqrt5)
        |>.role "window",
      Plane.Exact.label "Re w ≥ Re x + κ − η" ((crossCut, rat (5 / 4)) : QSqrt5 × QSqrt5) .right
        |>.size 12] ∧
    weight crossN = 0 ∧ isGoodLevel crossRadiusSq crossX 0 4 = some true ∧
    (windowSide crossN == .inside && windowSide leaf == .inside) = true ∧
    [1, 2, 3, 4].all (fun k => windowSide (shift crossN k 1) == .inside) = true ∧
    [1, 2, 3, 4].all (fun k => windowSide (shift leaf k (-1)) == .outside) = true ∧
    QSqrt.lt crossCut (proj leaf).realPart = true ∧
    ((proj crossN).realPart == ⟨5, -2⟩ && (proj crossN).conj == proj crossN &&
      (proj leaf).realPart == ⟨6, -2⟩) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ _ => rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links terminalCrossing terminalCrossing_spec

end TDCSGFigures.Levels
```

{figref "terminal-zoom"}[]: the figure `TDCSGFigures.Levels.terminalZoom`
and its theorem `TDCSGFigures.Levels.terminalZoom_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Levels

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- What `terminalZoom` draws, item for item, and the distances it makes visible. The items are
written out in drawing order. The leaf `P(n + e₀) = 8 - 4φ` lies between `0.0045` and `0.0046`
beyond the cut `Re x + κ - η` and between `0.0041` and `0.0042` inside the window's edge
`x + r/2 = 1.532` on the real axis, so the scale bar of length `0.005` measures both gaps; at the
scale of `terminalCrossing` each is below a pixel. Not stated: the arc's angular extent (a
floating-point choice), how the builders draw, the layout and the pixels. -/
theorem terminalZoom_spec :
    leafQ = ((proj leaf).realPart, rat 0) ∧ edgeStart = (rat (1511 / 1000), rat 0) ∧
    terminalZoom.items = #[
      Plane.Exact.polygon [(crossCut, rat (-13 / 2000)), (rat (1542 / 1000), rat (-13 / 2000)),
          (rat (1542 / 1000), rat (13 / 2000)), (crossCut, rat (13 / 2000))]
        |>.faint |>.filled |>.noOutline |>.fillOpacity 0.16
        |>.named "the half-plane Re w ≥ Re x + κ − η",
      Plane.Exact.arc crossXPoint (53 / 50 : Rat) (-arcHalfAngle) arcHalfAngle |>.role "window"
        |>.named "the window's circle |w − x| = r/2",
      Plane.Exact.segment edgeStart leafQ |>.width 3.5 |>.named "the edge from n to n + e₀",
      Plane.Exact.segment ((rat (1516 / 1000), rat (-5 / 1000)) : QSqrt5 × QSqrt5)
          (rat (1521 / 1000), rat (-5 / 1000)) |>.width 2 |>.named "a scale bar of length 0.005",
      Plane.Exact.point leafQ |>.role "right" |>.marker .square |>.size 6
        |>.named "the leaf n + e₀, P = 8 − 4φ ≈ 1.52786",
      Plane.Exact.label "n + e₀ (leaf)" leafQ .above |>.role "right",
      Plane.Exact.label "0.005" ((rat (15185 / 10000), rat (-5 / 1000)) : QSqrt5 × QSqrt5)
        .above,
      Plane.Exact.label "edge from n" ((rat (1518 / 1000), rat 0) : QSqrt5 × QSqrt5) .below,
      Plane.Exact.label "the cut" ((crossCut, rat (11 / 2000)) : QSqrt5 × QSqrt5) .left,
      Plane.Exact.label "Re w = Re x + κ − η" ((crossCut, rat (2 / 625)) : QSqrt5 × QSqrt5) .left
        |>.size 13,
      Plane.Exact.label "window edge" ((rat (15322 / 10000), rat (-1 / 200)) :
        QSqrt5 × QSqrt5) .right |>.role "window"] ∧
    QSqrt.lt (rat (45 / 10000)) ((proj leaf).realPart - crossCut) = true ∧
    QSqrt.lt ((proj leaf).realPart - crossCut) (rat (46 / 10000)) = true ∧
    QSqrt.lt (rat (41 / 10000)) (rat (crossX + 53 / 50) - (proj leaf).realPart) = true ∧
    QSqrt.lt (rat (crossX + 53 / 50) - (proj leaf).realPart) (rat (42 / 10000)) = true := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links terminalZoom terminalZoom_spec

end TDCSGFigures.Levels
```

{figref "level-phases"}[]: the figure `TDCSGFigures.Levels.levelPhases`
and its theorem `TDCSGFigures.Levels.levelPhases_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Levels

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- What `levelPhases` plots, and why. Its one panel holds two series of markers, in this order:
the levels of `-13, …, 9` that are not good, in grey, and the good ones, in green; each marker is
at `(m, phaseAt m)`, the rational ball centre at precision `64` of the exact reduced phase
`t - ⌊t + 1/2⌋`, `t = phase/L` in `ℚ(√5)`, decided for every level drawn. The good levels among
them are exactly `-10`, `-2`, `3`, by the exact test `isGoodLevel` (`TDCSG.Five.IsGoodLevel`);
`-10` is the only good level from `-13` to `-3` and `3` the only one from `3` to `9`, so they are
the candidates for `lo` and `hi` in the range drawn, and `-2` lies in the gap between the search
ranges `m ≤ -3` and `m ≥ 3`. Not stated: the bands, lines and texts (`notes`), the axes, the
layout and the pixels. -/
theorem levelPhases_spec :
    levelPhases.panels.map (·.series) = #[#[
      .scatterOfSamples "not good" (notGood.map sample) (some notGoodGrey) (radius := some 3),
      .scatterOfSamples "good" ((levels.filter good).map sample) (some goodGreen)
        (radius := some 6)]] ∧
    levels = (List.range 23).map (fun (i : Nat) => (i : Int) - 13) ∧
    sample = (fun (m : Int) => ((m : Rat), phaseAt m)) ∧
    levels.filter good = [-10, -2, 3] ∧
    notGood = [-13, -12, -11, -9, -8, -7, -6, -5, -4, -3, -1, 0, 1, 2, 4, 5, 6, 7, 8, 9] ∧
    goodInGap = [-2] ∧ walls = [-10, 3] ∧
    (levels.filter fun m => good m && m ≤ -3) = [-10] ∧
    (levels.filter fun m => good m && 3 ≤ m) = [3] ∧
    levels.all (fun m => (reducedPhase m).isSome) = true := by
  refine ⟨by simp [levelPhases], rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links levelPhases levelPhases_spec

end TDCSGFigures.Levels
```

# The figures of chapter 7

%%%
tag := "theorems-confinement"
file := "Theorems-confinement"
%%%

{figref "component-of-zero"}[]: the figure `TDCSGFigures.Confinement.componentOfZero`
and its theorem `TDCSGFigures.Confinement.componentOfZero_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Confinement

open PILean PILean.Plane PILean.Exact TDCSGFigures

set_option maxHeartbeats 4000000 in
/-- What `componentOfZero` draws, and why its records are right. The items are the window, then
an edge `edgeItem n m` for each edge of `compEdges`, a point `labelPoint n` for each label of
`compLabels`, the window centre and the labels with the legend, in this order; the builders'
definitions are stated. The component of `0` found by the exact search (`component`, every window
test decided in `ℚ(√5)`) is the list of 18 labels written out, and its edges are the 18 written
out, each from a weight-zero label `n` to `n + eⱼ`; every label lies inside the window, so each
point's record holds. Every coordinate of every label is `-1`, `0` or `1`, and in each coordinate
`j` the good levels nearest the gap `|m| ≤ 2` are those the caption states (`wallText`), with every
label strictly inside the slab `lo < nⱼ ≤ hi` they bound. Not stated: how the builders and modifiers
draw, the layout, the lettering, the style's colour values and the pixels. -/
theorem componentOfZero_spec :
    (∀ n m, edgeItem n m = (Plane.Exact.segment (proj n) (proj m) |>.width 1.5
      |>.named s!"the edge from {labelText n} to {labelText m}"
      |>.declRef `TDCSG.Five.centerGraph)) ∧
    (∀ n rel w, labelPoint n rel w = (if weight n == 0 then
      (Plane.Exact.point (proj n) |>.size 4.5
        |>.named s!"the label {labelText n}, weight {weight n}"
        |>.incident rel w |>.role "left")
      else (Plane.Exact.point (proj n) |>.size 4.5
        |>.named s!"the label {labelText n}, weight {weight n}" |>.incident rel w |>.role "right"
        |>.marker .square))) ∧
    componentOfZero.items = #[
      Plane.Exact.disk ((compX, 0) : Rat × Rat) (39 / 40 : Rat) |>.role "window"
        |>.fillOpacity 0.07 |>.named "the window"
        |>.describedBy "the closed disk |w − x| ≤ r/2, r = 1.95, x = 1/2"
        |>.declRef `TDCSG.Five.InWindow] ++
      (compEdges.toArray.map fun (n, m) => edgeItem n m) ++
      (compLabels.toArray.map fun n => labelPoint n .inside "the window") ++ #[
      Plane.Exact.point ((compX, 0) : Rat × Rat) |>.role "window" |>.marker .cross
        |>.named "the window center x = 1/2" |>.incident .inside "the window"
        |>.incident .on "the edge from (0, 0, 0, 0, 0) to (1, 0, 0, 0, 0)",
      Plane.Exact.label "0" origin (.toward (Plane.deg 200)) |>.role "left",
      Plane.Exact.label "e₀" rightCentre .auto |>.role "right",
      Plane.Exact.label "dots: weight 0 (left centers)" ((1 / 2 : Rat), (-9 / 8 : Rat))
        |>.role "left",
      Plane.Exact.label "squares: weight 1 (right centers)" ((1 / 2 : Rat), (-5 / 4 : Rat))
        |>.role "right",
      Plane.Exact.label "×: the window center x = 1/2" ((1 / 2 : Rat), (-11 / 8 : Rat))
        |>.role "window"] ∧
    compLabels = [#[0, 0, 0, 0, 0], #[1, 0, 0, 0, 0], #[0, 1, 0, 0, 0], #[0, 0, 0, 0, 1],
      #[0, 0, 0, -1, 1], #[0, 0, 1, -1, 1], #[0, -1, 1, -1, 1], #[1, -1, 1, -1, 1],
      #[1, -1, 1, -1, 0], #[1, -1, 1, 0, 0], #[1, -1, 0, 0, 0], #[0, 1, -1, 0, 0],
      #[0, 1, -1, 1, 0], #[0, 1, -1, 1, -1], #[1, 1, -1, 1, -1], #[1, 0, -1, 1, -1],
      #[1, 0, 0, 1, -1], #[1, 0, 0, 0, -1]] ∧
    compEdges = [(#[0, 0, 0, 0, 0], #[1, 0, 0, 0, 0]), (#[0, 0, 0, 0, 0], #[0, 1, 0, 0, 0]),
      (#[0, 0, 0, 0, 0], #[0, 0, 0, 0, 1]), (#[0, 0, 0, -1, 1], #[0, 0, 1, -1, 1]),
      (#[0, 0, 0, -1, 1], #[0, 0, 0, 0, 1]), (#[0, -1, 1, -1, 1], #[1, -1, 1, -1, 1]),
      (#[0, -1, 1, -1, 1], #[0, 0, 1, -1, 1]), (#[1, -1, 1, -1, 0], #[1, -1, 1, 0, 0]),
      (#[1, -1, 1, -1, 0], #[1, -1, 1, -1, 1]), (#[1, -1, 0, 0, 0], #[1, 0, 0, 0, 0]),
      (#[1, -1, 0, 0, 0], #[1, -1, 1, 0, 0]), (#[0, 1, -1, 0, 0], #[0, 1, 0, 0, 0]),
      (#[0, 1, -1, 0, 0], #[0, 1, -1, 1, 0]), (#[0, 1, -1, 1, -1], #[1, 1, -1, 1, -1]),
      (#[0, 1, -1, 1, -1], #[0, 1, -1, 1, 0]), (#[1, 0, -1, 1, -1], #[1, 1, -1, 1, -1]),
      (#[1, 0, -1, 1, -1], #[1, 0, 0, 1, -1]), (#[1, 0, 0, 0, -1], #[1, 0, 0, 1, -1]),
      (#[1, 0, 0, 0, -1], #[1, 0, 0, 0, 0])] ∧
    compLabels.all (fun n => inWindow compRadiusSq compX n) = true ∧
    compEdges.all (fun (n, m) => weight n == 0 &&
      (List.range 5).any fun j => m == shift n j 1) = true ∧
    compLabels.all (fun n => n.all fun c => -1 ≤ c && c ≤ 1) = true ∧
    [wallText 0, wallText 1, wallText 2, wallText 3, wallText 4] =
      ["n₀: −4, 4", "n₁: −3, 10", "n₂: −7, 6", "n₃: −7, 6", "n₄: −3, 10"] ∧
    (List.range 5).all (fun j => match nearestWalls j with
      | (some lo, some hi) => compLabels.all fun n => lo < n[j]! && n[j]! ≤ hi
      | _ => false) = true := by
  refine ⟨fun _ _ => rfl, fun n _ _ => ?_, rfl, ?_⟩
  · unfold labelPoint
    split <;> rfl
  repeat' apply And.intro
  all_goals decide +kernel

figure_links componentOfZero componentOfZero_spec

end TDCSGFigures.Confinement
```

{figref "walk-to-leaf"}[]: the animation `TDCSGFigures.Confinement.walkToLeaf`, an illustration,
and the data of its key frames, `TDCSGFigures.Confinement.walkToLeaf_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Confinement

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- The animation `walkToLeaf` and the data its key frames are drawn from. It has one panel whose
keys are `walkKey k`, `k = 0, …, 16`, and whose steps are made from the declared moves
`walkMoves`. Key `k` draws the window, the edges and labels of the path `path` up to `path[k]`
(`walkShown`), from key `15` on the candidates `n + eₖ` (`k ≠ 2`) of the leaf with their spokes,
at key `16` the step back, and a circle about `P(walkAt k)`, the label where the walk is: `path[k]`
up to the leaf, the leaf at key `15`, `n + e₂` at key `16`. Step `k` slides the circle from
`P(walkAt k)` to `P(walkAt (k + 1))` when they differ, by `±ζʲ` for a step `±eⱼ` of the path, and
fades in what the next key shows first; each declared slide, applied exactly in `ℚ(ζ₅)` to the
anchors of the actors of one key, gives those of the next (`walkArrives`). The data are checked
exactly at `r = 2.13`, `x = 1/5`: the path starts at `0`, consecutive labels differ by one unit
vector, every label lies in the window, so the path is a path of the centre graph; `n` has weight
zero, its level `n₂ = -5` is good, and its candidates `n + e₀`, `n + e₁`, `n + e₃`, `n + e₄` lie
outside the window, so `n + e₂` is its only neighbour. The captions are written out. Not stated:
how the builders draw, the layout, the timing and the frames the browser draws between the key
frames. -/
theorem walkToLeaf_keys :
    walkToLeaf.panels = #[{ motion :=
      { keys := ((List.range walkKeyCount).map walkKey).toArray,
        steps := ((List.range (walkKeyCount - 1)).map fun k =>
          exactStep (walkMoves k)).toArray } }] ∧
    walkKeyCount = 17 ∧
    (∀ k, walkAt k = if k ≤ path.length - 1 then path.getD k zeroLabel
      else if k == path.length then leafN else beforeLeaf) ∧
    (∀ k, walkShown k = min (k + 1) path.length) ∧
    (∀ k, walker k = (Plane.Exact.circle (proj (walkAt k)) walkerRadius |>.width 2
      |>.named "a circle about the label where the walk is" |>.withId "walker")) ∧
    walkerRadius = 1 / 20 ∧
    (∀ k, walkKey k =
  let shown := walkShown k
  let ps := path.take shown
  let steps := ps.zip ps.tail
  let candidates := decide (path.length ≤ k)
  let back := decide (path.length + 1 ≤ k)
  let window := "the window"
  { width := figureWidth
    view := some walkView
    padding := 16
    style := partTwoStyle
    checks := .fail
    items := #[
      Plane.Exact.disk ((walkX, 0) : Rat × Rat) (213 / 200 : Rat) |>.role windowRole
        |>.fillOpacity 0.07 |>.named window
        |>.describedBy "the closed disk |w − x| ≤ r/2, r = 2.13, x = 1/5"
        |>.declRef `TDCSG.Five.InWindow,
      Plane.Exact.point ((walkX, 0) : Rat × Rat) |>.role windowRole |>.marker .cross
        |>.named "the window center x = 1/5" |>.incident .inside window] ++
      (steps.toArray.mapIdx fun i (a, b) =>
        let last := b == leafN
        Plane.Exact.segment (proj a) (proj b) |>.width (if last then 3.5 else 1.5)
          |>.named (if last then
              "the step from n + e₂ to n: it lowers n₂ from −4 to the good level −5"
            else s!"the step from {labelText a} to {labelText b}")
          |>.declRef (if last then `TDCSG.Five.leaf_of_crossing else `TDCSG.Five.centerGraph)
          |>.withId s!"edge-{i}") ++
      (if candidates then (List.range 5).toArray.filterMap fun j =>
        if j == 2 then none else
          some (Plane.Exact.segment (proj leafN) (proj (shift leafN j 1)) |>.faint |>.dashed
            |>.named s!"the rejected step from n to n + e{sub j}" |>.withId s!"reject-{j}")
        else #[]) ++
      (ps.toArray.mapIdx fun i n =>
        labelPoint n (walkSide n) window walkMarkerSize |>.withId s!"label-{i}") ++
      (if candidates then (List.range 5).toArray.filterMap fun j =>
        if j == 2 then none else
          let m := shift leafN j 1
          some (Plane.Exact.point (proj m) |>.faint |>.marker .ring |>.size walkMarkerSize
            |>.named s!"n + e{sub j} = {labelText m}, outside the window"
            |>.incident (walkSide m) window |>.withId s!"candidate-{j}") else #[]) ++
      (if back then #[Plane.Exact.arrow (proj leafN) (proj beforeLeaf) |>.width 2
          |>.named "the only step from n: back to n + e₂"
          |>.declRef `SimpleGraph.Reachable.mem_or_exists_adj_of_leaf |>.withId "back"]
        else #[]) ++
      #[walker k] ++ #[
      Plane.Exact.label "0" origin (.toward (Plane.deg 200)) (some 14) |>.role leftRole,
      Plane.Exact.label "window" ((rat (1 / 5), rat (23 / 20)) : QSqrt5 × QSqrt5)
        |>.role windowRole,
      Plane.Exact.label "dots: weight 0 (left centers)"
        ((rat (2 / 5), rat (-29 / 20)) : QSqrt5 × QSqrt5) |>.role leftRole,
      Plane.Exact.label "squares: weight 1 (right centers)"
        ((rat (2 / 5), rat (-8 / 5)) : QSqrt5 × QSqrt5) |>.role rightRole,
      Plane.Exact.label "×: the window center x = 1/5"
        ((rat (2 / 5), rat (-7 / 4)) : QSqrt5 × QSqrt5) |>.role windowRole] ++
      (if shown ≥ path.length - 1 then #[Plane.Exact.label "n + e₂" (proj beforeLeaf) .auto
        |>.role rightRole |>.withId "name-before"] else #[]) ++
      (if shown ≥ path.length then #[Plane.Exact.label "n" (proj leafN)
          (.toward (Plane.deg (-36))) (some 14) |>.role leftRole
          |>.withId "name-leaf",
        Plane.Exact.label "n₂ = −5 at n: a good level"
          ((rat (2 / 5), rat (-19 / 10)) : QSqrt5 × QSqrt5) |>.role goodRole
          |>.withId "good-level"] else #[]) ++
      (if candidates then (List.range 5).toArray.filterMap fun j =>
        if j == 2 then none else
          some (Plane.Exact.label s!"n + e{sub j}" (proj (shift leafN j 1)) .auto |>.faint
            |>.withId s!"candidate-label-{j}")
        else #[])
    info := { title := s!"The walk at key {k}" } }) ∧
    (∀ k, walkNameIds k =
  (if path.length - 2 ≤ k then ["name-before"] else []) ++
    (if path.length - 1 ≤ k then ["name-leaf", "good-level"] else []) ++
    (if path.length ≤ k then [0, 1, 3, 4].map (s!"candidate-label-{·}") else [])) ∧
    (∀ k, walkMoves k =
  let slide :=
    ("walker", ExactMove.slide (ZetaFrac.ofZeta (proj (walkAt (k + 1)) - proj (walkAt k))))
  let names := ((walkNameIds (k + 1)).filter (!(walkNameIds k).contains ·)).map (·, .appear)
  if k + 1 < path.length then
    [slide, (s!"edge-{k}", .appear), (s!"label-{k + 1}", .appear)] ++ names
  else if k + 1 == path.length then
    ([0, 1, 3, 4].map (s!"reject-{·}", .appear)) ++
      ([0, 1, 3, 4].map (s!"candidate-{·}", .appear)) ++ names
  else [slide, ("back", .appear)]) ∧
    (List.range (path.length - 1)).all (fun k =>
      let (j, s) := stepDir (path.getD k zeroLabel) (path.getD (k + 1) zeroLabel)
      proj (path.getD (k + 1) zeroLabel) - proj (path.getD k zeroLabel) ==
        Zeta5.ofInt s * zeta j && (s == 1 || s == -1)) = true ∧
    (proj beforeLeaf - proj leafN == zeta 2) = true ∧
    walkArrives = true ∧
    leafN = #[0, 3, -5, 4, -2] ∧ beforeLeaf = shift leafN 2 1 ∧ path.length = 15 ∧
    path.head? = some zeroLabel ∧ path.getLast? = some leafN ∧
    path.all (fun n => inWindow walkRadiusSq walkX n) = true ∧
    (path.zip path.tail).all (fun (a, b) => (List.range 5).any fun j =>
      b == shift a j 1 || b == shift a j (-1)) = true ∧
    weight leafN = 0 ∧ isGoodLevel walkRadiusSq walkX 2 (-5) = some true ∧
    [0, 1, 3, 4].all (fun j => !inWindow walkRadiusSq walkX (shift leafN j 1)) = true ∧
    walkToLeaf.captions = ((List.range walkKeyCount).map walkCaption).toArray ∧
    (∀ k, stepText k =
  let (j, sgn) := stepDir (path.getD k zeroLabel) (path.getD (k + 1) zeroLabel)
  s!"{if sgn == 1 then "+" else "−"} e{sub j}") ∧
    (∀ k, walkCaption k =
  let n := path.getD k zeroLabel
  if k == 0 then
    "A walk in the center graph at r = 2.13, x = 1/5, from the label 0, along a path that a \
      breadth-first search found; the circle marks where the walk is. Each step adds or removes \
      one unit vector eⱼ, and every label lies in the window."
  else if k + 2 < path.length then
    s!"Move {k}: {stepText (k - 1)}, to {labelText n}; n₂ = {intText (n.getD 2 0)}."
  else if k + 2 == path.length then
    s!"Move {k}: {stepText (k - 1)}, to n + e₂ = {labelText n}: n₂ has fallen from 0 to −4."
  else if k + 1 == path.length then
    s!"Move {k}: {stepText (k - 1)}, into n = {labelText n}: the step crosses the good level −5 \
      of n₂."
  else if k == path.length then
    "n is a leaf: its other candidates n + eₖ, k ≠ 2, lie outside the window (open rings at the \
      ends of dashed spokes)."
  else
    "From the leaf n the only step leads back to n + e₂, as the one-step lemma requires.") := by
  refine ⟨by unfold walkToLeaf; with_reducible rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals first
    | (intro _; unfold walkAt; with_reducible rfl)
    | (intro _; unfold walkShown; with_reducible rfl)
    | (intro _; unfold walker; with_reducible rfl)
    | (intro _; unfold walkKey; with_reducible rfl)
    | (intro _; unfold walkNameIds; with_reducible rfl)
    | (intro _; unfold walkMoves; with_reducible rfl)
    | (intro _; unfold stepText; with_reducible rfl)
    | (intro _; unfold walkCaption; with_reducible rfl)
    | (unfold walkToLeaf; with_reducible rfl)
    | decide +kernel

end TDCSGFigures.Confinement
```

{figref "coordinate-box"}[] records the bounds of the component used in the worked example.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open Confinement

/-- Every displayed row has two good levels enclosing all the observed coordinates. -/
theorem coordinateBox_spec :
    coordinateBox.items = (Array.range 5).flatMap coordinateRow ∧
    (List.range 5).all (fun j => match nearestWalls j with
      | (some lo, some hi) => isGoodLevel compRadiusSq compX j lo == some true &&
        isGoodLevel compRadiusSq compX j hi == some true &&
        compLabels.all fun n => lo < n[j]! && n[j]! ≤ hi
      | _ => false) = true := by
  exact ⟨rfl, by decide +kernel⟩

figure_links coordinateBox coordinateBox_spec

end TDCSGFigures
```

# The figure of chapter 8

%%%
tag := "theorems-main"
file := "Theorems-main"
%%%

{figref "threshold-classification"}[] joins the two halves at the exact critical radius.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- Both rays meet at the same abscissa, excluded on the finite row and included on the
infinite row. -/
theorem radiusThreshold_spec :
    axisR = .root ⟨⟨7 / 2, 1 / 2⟩⟩ ∧
    radiusThreshold.items = radiusLineItems true true ∧
    radiusThreshold.items[3]! = (Plane.Exact.point (axisAt axisR finiteRow) |>.marker .ring
      |>.role finiteRole |>.named "R, not a radius of the finite half") ∧
    radiusThreshold.items[4]! = (Plane.Exact.point (axisAt axisR infiniteRow)
      |>.role infiniteRole |>.named "R, a radius of the infinite half") := by
  exact ⟨rfl, rfl, rfl, rfl⟩

figure_links radiusThreshold radiusThreshold_spec

end TDCSGFigures
```

# The figures of chapter 9

%%%
tag := "theorems-other-orders"
file := "Theorems-other-orders"
%%%

{figref "order-eight"}[]: the figure `TDCSGFigures.orderEight`
and its theorem `TDCSGFigures.orderEight_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

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
      Plane.Exact.point (centre8 (-1)) |>.role leftRole |>.named "the center −1",
      Plane.Exact.point (centre8 1) |>.role rightRole |>.named "the center 1",
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

figure_links orderEight orderEight_spec

end TDCSGFigures
```

{figref "order-ten"}[]: the figure `TDCSGFigures.orderTen`
and its theorem `TDCSGFigures.orderTen_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

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
      Plane.Exact.point (centre10 (-1)) |>.role leftRole |>.named "the center −1",
      Plane.Exact.point (centre10 1) |>.role rightRole |>.named "the center 1",
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

figure_links orderTen orderTen_spec

end TDCSGFigures
```

{figref "order-twelve"}[]: the figure `TDCSGFigures.orderTwelve`
and its theorem `TDCSGFigures.orderTwelve_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

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
      Plane.Exact.point (centre12 (-1)) |>.role leftRole |>.named "the center −1",
      Plane.Exact.point (centre12 1) |>.role rightRole |>.named "the center 1",
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

figure_links orderTwelve orderTwelve_spec

end TDCSGFigures
```
