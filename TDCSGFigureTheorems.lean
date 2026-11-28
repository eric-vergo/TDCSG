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
stated vectors, and that motion is not part of any statement. In the two animations in which the
radius grows (the orbit of zero and the lens), the circles, the lens and what depends on the
radius pass instead through exact pictures at stated radii between the key frames, and the browser
interpolates between consecutive ones; those pictures are stated, the interpolation is not. What
the key frames show, that the figure shown is made of exactly those key frames, declared moves and
captions, and that each declared turn or slide carries one key frame onto the next exactly, is
stated here as a plain
theorem (`TDCSGFigures.wordLoop_keys`, `TDCSGFigures.Lift.framePair_keys`,
`TDCSGFigures.generatorStep_keys` and the other `_keys` theorems, and for two illustrations
`TDCSGFigures.wordSteps_spec` and `TDCSGFigures.Confinement.walkToLeaf_spec`, named `_spec`,
though they are not linked).
The phases winding round of chapter 6 are an exception to the exactness of the drawing: on its
circle the points are placed, in floating point, from rationals within `2⁻⁶²` of the exact phases,
and each turn is a rational within `2⁻⁶²` of `φ - 1`, which
`TDCSGFigures.Levels.levelWinding_keys` states. Each actor an animation moves is
drawn at the exact anchors its arrival check reads. The captions are written out, or, where they
are built from the data (the orbit on the chord, the walk, the component of zero, the phases
winding round), stated as functions of the data; the kernel does not reduce the string functions
they are built with, so their words are pinned by `#guard` lines in `TDCSGTests.Motions`; the test
driver requires that PILean's engine finds no error in any animation. Where an animation stands in
place of a
figure with a linked theorem, its last key frame is that figure, and the theorem stays linked to
the animation: it states that the last key frame is the figure and what the figure draws
(`TDCSGFigures.generatorStep_spec`, `TDCSGFigures.extensionJump_spec`,
`TDCSGFigures.disjointDisks_spec`, `TDCSGFigures.exchangedIntervals_spec`,
`TDCSGFigures.chordOrbit_spec`, `TDCSGFigures.Levels.terminalCrossing_spec`,
`TDCSGFigures.Confinement.componentOfZero_spec`); the lens of chapter 5 is linked to its theorem
`TDCSGFigures.Lens.lensRadius_spec`, which states its key frames and the pictures between them.
The other animations (the
orbit of zero on the front page, the word followed letter by letter and the three words of
chapters 2 and 3, the frame pair of chapter 4, the phases winding round of chapter 6 and the walk
of chapter 7) are illustrations: no
theorem is linked to them. The orbits of zero are computed by the exact orbit engine, which the
kernel does not run here; their sizes and how they contain one another are pinned by `#guard`
lines in `TDCSGTests.Motions` (`TDCSGFigures.orbitRadius_keys`).

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

{figref "orbit-radius"}[]: the animation `TDCSGFigures.orbitRadius`, an illustration, and the data
of its key frames, `TDCSGFigures.orbitRadius_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.OrbitLoop

/-- The animation `orbitRadius` and the data its key frames are drawn from, written out; an
illustration, to which this theorem is not linked. It is the loop of `figureConfig`: one panel
whose keys are `key os k`, `k = 0, …, 5`, for the radii `r = 1.5, 1.9, 1.95, 2.05, 2.1` and the
critical radius `R` (`radius`), and whose steps are made from the declared moves `moves`, the
circles and the lens morphed (`step`) through the exact pictures `between` at 5 radii between two
keys (`samples = 6`), with `r²` evenly spaced; its poster is the last key, at `R`. The orbits `os`
are those of the orbit engine (`orbits`, `orbitAt`, `TDCSGFigures.orbit`): complete at the rational
radii, and at `R` the first `cap = 1000` points of its breadth-first search from `0`. Key `k` draws
the circles of radius `r` about `-1` and `1` and their lens (`diskActors`), the points of its orbit
in the groups `pointGroup os j k` of the points first drawn at key `j ≤ k` (`newPoints`, the
points of the orbit of key `j` that are not in the orbit of key `j - 1`), each recording where it
stands relative to the disks and the lens as the engine decides it (`dot`), the centres
(`centres`) and the line under the disks (`valueLabel`, `valueText`), in row `k % 2`, so that two
lines never overlap. Step `j` declares no move of
any point: the line under the disks changes and the group of key `j + 1`, if any, appears
(`moves`). The facts about the orbits themselves come from the engine, which the kernel does not
run here; they are `#guard` lines of `TDCSGTests.Motions`: the orbits have 9, 9, 71, 151, 801 and
1000 points, the first five are complete, each contains the one before it (an instance of
`TDCSG.orbit_mono`), the 801 points at `r = 2.1` are among the first 997 at `R`, the groups up to
each key are the points of its orbit, each once, every declared move arrives exactly
(`GrowthConfig.arrives`), the engine decides the side of every point drawn, and the captions and
the lines under the disks are written out word for word. That the orbit at `R` is infinite is
`TDCSG.CriticalRadius.infinite_orbit_zero_five`. Not stated: how the builders draw, the timing, and
the frames the browser draws between the key frames and the samples. -/
theorem orbitRadius_keys :
    orbitRadius = figureConfig.motion ∧
    figureConfig.radii =
      #[("1.5", 3 / 2), ("1.9", 19 / 10), ("1.95", 39 / 20), ("2.05", 41 / 20), ("2.1", 21 / 10)] ∧
    figureConfig.cap = 1000 ∧ figureConfig.samples = 6 ∧ figureConfig.keyCount = 6 ∧
    (∀ cfg : GrowthConfig, cfg.motion.panels = #[{ motion :=
      { keys := ((List.range cfg.keyCount).map (cfg.key cfg.orbits)).toArray,
        steps := ((List.range (cfg.keyCount - 1)).map (GrowthConfig.step cfg.orbits)).toArray,
        between := cfg.between, morphSamples := cfg.samples } }]) ∧
    (∀ cfg : GrowthConfig, cfg.motion.captions =
      ((List.range cfg.keyCount).map (cfg.caption cfg.orbits)).toArray) ∧
    (∀ cfg : GrowthConfig, cfg.motion.poster = cfg.keyCount - 1) ∧
    (∀ cfg : GrowthConfig, cfg.motion.checks = .fail) ∧
    (∀ (cfg : GrowthConfig) (k : Nat), cfg.radius k = (
  match cfg.radii[k]? with
  | some (t, r) => .rat t r
  | none => .critical
    : Radius)) ∧
    (∀ cfg : GrowthConfig, cfg.orbits = (
  ((List.range cfg.keyCount).map fun k =>
    let ρ := cfg.radius k
    orbitAt ρ (match ρ with | .critical => cfg.cap | .rat .. => 100000)).toArray
    : Array Orbit)) ∧
    (∀ (ρ : Radius) (cap : Nat), orbitAt ρ cap = (
  match orbit ρ.sq origin cap with
  | .ok o => o
  | .error _ => { points := #[], complete := false }
    : Orbit)) ∧
    (∀ (os : Array Orbit) (k : Nat), GrowthConfig.newPoints os k = (
  let here := (os.getD k default).points
  if k == 0 then here.map (·.z)
  else
    let before := (os.getD (k - 1) default).points
    (here.filter fun p => !before.any (·.z == p.z)).map (·.z)
    : Array Zeta5)) ∧
    (∀ (cfg : GrowthConfig) (os : Array Orbit) (j k : Nat), cfg.pointGroup os j k = (
  (group ((GrowthConfig.newPoints os j).map (dot (cfg.radius k).sq)))
    |>.named s!"the points of the orbit first drawn at r = {(cfg.radius j).text}"
    |>.actor s!"orbit-{j}"
    : Item)) ∧
    (∀ (os : Array Orbit) (k : Nat), GrowthConfig.groupsUpTo os k = (
  (List.range (k + 1)).filter fun j => !(GrowthConfig.newPoints os j).isEmpty
    : List Nat)) ∧
    (∀ (r2 : RadiusSq) (z : Zeta5), dot r2 z = (
  let it := Plane.Exact.point z |>.size 1.5 |>.halo false
  match sides r2 z with
  | .ok (l, r) => withSides it l r
  | .error _ => it
    : Item)) ∧
    (∀ (r : SqrtOf QSqrt5), diskActors r = (
#[
  Plane.Exact.disk leftCentre r |>.noFill |>.role leftRole |>.named "the left circle"
    |>.describedBy "the closed disk of radius r about −1" |>.actor "left-disk",
  Plane.Exact.disk rightCentre r |>.noFill |>.role rightRole |>.named "the right circle"
    |>.describedBy "the closed disk of radius r about 1" |>.actor "right-disk",
  Plane.Exact.lens leftCentre rightCentre r r |>.role lensRole |>.noOutline
    |>.fillOpacity 0.12 |>.named "the lens" |>.actor "lens"]
    : Array Item)) ∧
    (∀ (r2 : RadiusSq), centres r2 = (
  let side := fun (c : Zeta5) (it : Item) => match sides r2 c with
    | .ok (l, r) => withSides it l r
    | .error _ => it
  #[side leftCentre (Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1"),
    side rightCentre (Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1")]
    : Array Item)) ∧
    (∀ (cfg : GrowthConfig) (os : Array Orbit) (k : Nat), cfg.valueText os k = (
  let n := (os.getD k default).points.size
  match cfg.radius k with
  | .rat t _ => s!"r = {t}: {n} points"
  | .critical => s!"r = R: infinite, the first {n} shown"
    : String)) ∧
    (∀ (cfg : GrowthConfig) (os : Array Orbit) (k : Nat), cfg.valueLabel os k = (
  Plane.Exact.label (cfg.valueText os k) ((0 : Rat), valueY - (k % 2 : Nat) * 3 / 10)
    |>.actor s!"value-{k}"
    : Item)) ∧ valueY = -27 / 10 ∧
    (∀ (cfg : GrowthConfig) (os : Array Orbit) (k : Nat), cfg.key os k = (
  let ρ := cfg.radius k
  { width := figureWidth
    padding := 16
    style := orbitStyle
    checks := .fail
    items := diskActors ρ.value ++
      ((GrowthConfig.groupsUpTo os k).map (cfg.pointGroup os · k)).toArray ++
      centres ρ.sq ++ #[cfg.valueLabel os k]
    info := { title := s!"The orbit of 0 at r = {ρ.text}" } }
    : Plane.Figure)) ∧
    (∀ (os : Array Orbit) (j : Nat), GrowthConfig.moves os j = (
  [(s!"value-{j}", .vanish), (s!"value-{j + 1}", .appear)] ++
    (if (GrowthConfig.newPoints os (j + 1)).isEmpty then []
      else [(s!"orbit-{j + 1}", .appear)])
    : List (String × ExactMove ZetaFrac))) ∧
    (∀ (os : Array Orbit) (j : Nat), GrowthConfig.step os j = (
  let s := exactStep (GrowthConfig.moves os j)
  { s with moves := #[("left-disk", .morph), ("right-disk", .morph), ("lens", .morph)] ++ s.moves }
    : MotionStep)) ∧
    (∀ (os : Array Orbit) (k : Nat), GrowthConfig.actors os k = (
  ((GrowthConfig.groupsUpTo os k).map fun j =>
    ⟨s!"orbit-{j}", (GrowthConfig.newPoints os j).toList.map ZetaFrac.ofZeta⟩) ++
    [⟨s!"value-{k}", []⟩]
    : List (ExactActor ZetaFrac))) ∧
    (∀ (cfg : GrowthConfig) (j : Nat) (q : Rat), cfg.between j q = (
  let a := (cfg.radius j).sqValue
  let b := (cfg.radius (j + 1)).sqValue
  some { width := figureWidth, padding := 16, style := orbitStyle, checks := .fail,
         items := diskActors
           (⟨a * TDCSGFigures.rat (1 - q) + b * TDCSGFigures.rat q⟩ : SqrtOf QSqrt5) }
    : Option Plane.Figure)) ∧
    (∀ (cfg : GrowthConfig) (os : Array Orbit) (k : Nat), cfg.caption os k = (
  let n := (os.getD k default).points.size
  let prev := (os.getD (k - 1) default).points.size
  match cfg.radius k with
  | .rat t _ =>
    if k == 0 then
      s!"The orbit of 0 under the two moves at r = {t}, computed exactly: {n} points. As r \
        grows the closed disks grow and the orbit can only grow: from one radius shown to the next \
        the circles grow and the points the orbit gains fade in. The orbit is exact only at the \
        radii shown."
    else if n == prev then
      s!"r = {t}: the disks are larger, and the orbit is the same {n} points."
    else s!"r = {t}: {n} points; the {n - prev} new ones have faded in, and the {prev} points \
      of the orbit at r = {(cfg.radius (k - 1)).text} are among them."
  | .critical =>
    s!"r = R = √(3 + φ): the orbit is infinite, and only the first {n} of its points that a \
      breadth-first search from 0 finds are drawn; the {prev} points of the orbit at \
      r = {(cfg.radius (k - 1)).text} are among them."
    : String)) ∧
    (∀ ρ : Radius, ρ.sqValue = (
  match ρ with
  | .rat _ r => TDCSGFigures.rat (r * r)
  | .critical => threePlusPhi
    : QSqrt5)) ∧
    (∀ ρ : Radius, ρ.sq = (
  match ρ with
  | .rat _ r => .ofRat r
  | .critical => .critical
    : RadiusSq)) ∧
    RadiusSq.critical = ⟨#[3, 0, -1, -1], 1⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl,
    fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

end TDCSGFigures
```

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

/-- The key frames of `extensionJump` before the last and its moves, written out. Key `k ≤ 1`
draws, in the frame of the figure of the jump, the disk, its radius, the bar from `8` to `12`
across the boundary circle in two parts and the centre: the part in `B`, from `8` to `10` with
`p = 9` (`jumpInner`), turned by `ζ⁴` about `0` at key `1`, and the part outside, from `10` to `12`
with `q = 11` (`jumpOuter`); at key `0` also the segment from `p` to `q`, its length and the label
of `p`. Each part is drawn at its anchors (`jumpInnerAnchors`, `jumpOuterAnchors`), and the exact
actors of the keys (`jumpActors`) are those anchors: the arrival check reads the points the keys
draw, and every actor that moves has anchors. Step `0` turns the part in `B` by `jumpTurn`, a
fifth of a turn clockwise about `0`, while the segment from `p` to `q` and the labels fade; step
`1` fades the bar out and the marks of the figure of the jump in. Each declared move, applied
exactly in `ℚ(ζ₅)` to the anchors of the actors of one key, gives those of the next
(`jumpArrives`). The ends of the parts lie as stated: `|8|² < 100`, `|10|² = 100` (on the
boundary circle, so in the closed disk, and turned), `|12|² > 100`, and the turn carries `p` to
`ĥ(p)`. The captions are written out. Not stated: how the builders draw, the timing and the frames
the browser draws between the key frames. -/
theorem extensionJump_keys :
    extensionJump.captions = jumpCaptions ∧
    (jumpCaptions = (
#[
  "A closed disk B of radius 10 about c = 0, to be turned through 72° clockwise and extended by \
    the identity. A bar from 8 to 12 crosses the boundary circle at 10: p = 9 lies inside B, \
    q = 11 outside, 2 apart.",
  "The extension turns the part of the bar in B, its point 10 on the circle included, about c and \
    fixes the part outside: the bar is torn at the circle. p went to its image 9ζ⁴, q stayed.",
  "p and q were 2 apart; their images, 9ζ⁴ and q itself, are about 11.9 apart. However close to \
    the circle p and q are taken, the jump stays, so the extension is not continuous and is no \
    isometry of the plane."]
    : Array String)) ∧
    (∀ (k : Nat), jumpKey k = (
  { extensionJumpFinal with items := jumpKeyItems k, info := { title := jumpCaptions.getD k "" } }
    : Plane.Figure)) ∧
    (∀ (k : Nat), jumpKeyItems k = (
  #[jumpDisk] ++ jumpRadius ++ (if k == 0 then #[jumpGap, jumpGapLabel] else #[]) ++
    #[jumpCentre, jumpInner (if k == 0 then Zeta5.ofInt 1 else zeta 4), jumpOuter,
      jumpCentreLabel] ++ (if k == 0 then #[jumpPLabel] else #[]) ++ #[jumpName]
    : Array Item)) ∧
    (∀ (τ : Zeta5), jumpInnerAnchors τ = (
  [barInner * τ, barCut * τ, nearInside * τ].map ZetaFrac.ofZeta
    : List ZetaFrac)) ∧
    (∀ (τ : Zeta5), jumpInner τ = (
  let a := fun (i : Nat) => (jumpInnerAnchors τ).getD i (ZetaFrac.ofZeta origin)
  (group #[Plane.Exact.segment (a 0) (a 1) |>.role leftRole |>.width 4
        |>.named "the part of the bar in B, from 8 to 10",
      Plane.Exact.point (a 2) |>.role leftRole |>.incident .inside "the disk B"
        |>.incident .on "the part of the bar in B, from 8 to 10"])
    |>.named "the part of the bar in B and the point p, turned by ĥ" |>.withId "inner"
    : Item)) ∧
    (jumpOuterAnchors = (
  [barCut, barOuter, nearOutside, nearOutside].map ZetaFrac.ofZeta
    : List ZetaFrac)) ∧
    (jumpOuter = (
  let a := fun (i : Nat) => jumpOuterAnchors.getD i (ZetaFrac.ofZeta origin)
  (group #[Plane.Exact.segment (a 0) (a 1) |>.width 4
        |>.named "the part of the bar outside B, from 10 to 12",
      Plane.Exact.point (a 2) |>.incident .outside "the disk B"
        |>.incident .on "the part of the bar outside B, from 10 to 12",
      Plane.Exact.label "q, fixed" (a 3) .belowRight])
    |>.named "the part of the bar outside B and the point q, fixed by ĥ" |>.withId "outer"
    : Item)) ∧
    (barInner = (
Zeta5.ofInt 8
    : Zeta5)) ∧
    (barCut = (
Zeta5.ofInt 10
    : Zeta5)) ∧
    (barOuter = (
Zeta5.ofInt 12
    : Zeta5)) ∧
    (jumpTurn = (
⟨ZetaFrac.ofZeta origin, -1 / 5⟩
    : ExactTurn)) ∧
    (∀ (k : Nat), jumpActors k = (
  let z := ZetaFrac.ofZeta
  let τ := if k == 0 then Zeta5.ofInt 1 else zeta 4
  if k ≤ 1 then
    [⟨"inner", jumpInnerAnchors τ⟩, ⟨"outer", jumpOuterAnchors⟩] ++
    (if k == 0 then [⟨"gap", [z nearInside, z nearOutside]⟩, ⟨"gap-label", []⟩,
      ⟨"p-label", [z nearInside]⟩] else [])
  else
    [⟨"arc", [z nearInside, z nearInsideImage]⟩, ⟨"angle", [z origin]⟩,
      ⟨"gap", [z nearInside, z nearOutside]⟩, ⟨"image-gap", [z nearInsideImage, z nearOutside]⟩,
      ⟨"gap-label", []⟩, ⟨"image-gap-label", []⟩, ⟨"p", [z nearInside]⟩, ⟨"q", [z nearOutside]⟩,
      ⟨"image", [z nearInsideImage]⟩, ⟨"p-label", [z nearInside]⟩,
      ⟨"q-label", [z nearOutside]⟩, ⟨"image-label", [z nearInsideImage]⟩,
      ⟨"angle-label", [z origin]⟩]
    : List (ExactActor ZetaFrac))) ∧
    jumpMoves 0 = [("inner", .turn jumpTurn), ("gap", .vanish), ("gap-label", .vanish),
      ("p-label", .vanish)] ∧
    moveKinds (jumpMoves 1) = [("inner", "vanish"), ("outer", "vanish"), ("arc", "appear"),
      ("angle", "appear"), ("gap", "appear"), ("image-gap", "appear"), ("gap-label", "appear"),
      ("image-gap-label", "appear"), ("p", "appear"), ("q", "appear"), ("image", "appear"),
      ("p-label", "appear"), ("q-label", "appear"), ("image-label", "appear"),
      ("angle-label", "appear")] ∧
    (jumpInnerAnchors (Zeta5.ofInt 1)).length = 3 ∧ (jumpInnerAnchors (zeta 4)).length = 3 ∧
    jumpOuterAnchors.length = 4 ∧
    declaredTurns 2 jumpMoves = [-1 / 5] ∧ turnsAreFifths = true ∧
    jumpArrives = true ∧
    QSqrt.lt barInner.normSq (rat 100) = true ∧ (barCut.normSq == rat 100) = true ∧
    QSqrt.lt (rat 100) barOuter.normSq = true ∧
    ((jumpTurn.apply (ZetaFrac.ofZeta nearInside)).any
      (ZetaFrac.same · (ZetaFrac.ofZeta nearInsideImage))) = true := by
  repeat' apply And.intro
  all_goals first
    | (intros; unfold extensionJump; with_reducible rfl)
    | (intros; unfold jumpCaptions; with_reducible rfl)
    | (intros; unfold jumpKey; with_reducible rfl)
    | (intros; unfold jumpKeyItems; with_reducible rfl)
    | (intros; unfold jumpInnerAnchors; with_reducible rfl)
    | (intros; unfold jumpInner; with_reducible rfl)
    | (intros; unfold jumpOuterAnchors; with_reducible rfl)
    | (intros; unfold jumpOuter; with_reducible rfl)
    | (intros; unfold barInner; with_reducible rfl)
    | (intros; unfold barCut; with_reducible rfl)
    | (intros; unfold barOuter; with_reducible rfl)
    | (intros; unfold jumpTurn; with_reducible rfl)
    | (intros; unfold jumpActors; with_reducible rfl)
    | decide +kernel
    | (simp only [generatorMoves]; done)
    | (simp only [stepMoves]; done)
    | (simp only [jumpMoves]; done)
    | (simp only [disjointMoves]; done)

end TDCSGFigures
```

{figref "disjoint-disks"}[]: the animation `TDCSGFigures.disjointDisks`, whose last key frame is
the figure of the two turns, with its theorem `TDCSGFigures.disjointDisks_spec`;
the other key frames and the moves are stated in `TDCSGFigures.disjointDisks_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- The animation `disjointDisks` and the figure of the two turns, its last key frame. The animation
has one panel whose keys are `disjointKeys`, three keys with the two orders side by side and then
`disjointDisksFinal` at full size, and whose steps are made from the declared moves `disjointMoves`;
its poster, the still shown under reduced motion and in print, is the last key. The figure of the
two turns draws the radii `r₁ = 4/5` and `r₂ = 7/10` of the disks `B₁` about `-1` and `B₂` about
`1`, the points `x = -1 + φ⁻¹ ζ²` and `y = 1 + φ⁻¹ ζ²` (`φ⁻¹ = ζ + ζ⁴`), and their images
`a(x) = -1 + φ⁻¹ ζ` and `b(y) = 1 + φ⁻¹ ζ`; its items are written out in drawing order, each with
its id, since the animation fades all of them in. The facts hold exactly: `r₁ + r₂ < 2`, so the
disks are disjoint and the gap runs from `-1 + r₁ = -1/5` to `1 - r₂ = 3/10`;
`|x + 1|² = |y - 1|² = φ⁻²` with `φ⁻² < r₂² < r₁²`; `x` lies outside `B₂` and `y` outside `B₁`; `a`
turns `x` to `a(x)` and fixes `y`, `b` turns `y` to `b(y)` and fixes `x`; `a(x)` lies in `B₁` and
`b(y)` in `B₂`. Not stated: how the builders and modifiers draw, the layout, the lettering, the
style's colour values and the pixels. -/
theorem disjointDisks_spec :
    disjointDisks.panels = #[{ motion :=
      { keys := disjointKeys,
        steps := ((List.range 3).map (exactStep ∘ disjointMoves)).toArray } }] ∧
    disjointKeys = #[disjointKey 0, disjointKey 1, disjointKey 2, disjointDisksFinal] ∧
    disjointDisks.poster = 3 ∧
    disjointLeft = 4 / 5 ∧ disjointRight = 7 / 10 ∧
    leftSample = leftCentre + phiInv * Zeta5.pow 2 ∧
    rightSample = rightCentre + phiInv * Zeta5.pow 2 ∧ phiInvReal = ⟨-1 / 2, 1 / 2⟩ ∧
    disjointDisksFinal.items = #[
      Plane.Exact.disk leftCentre disjointLeft |>.noFill |>.role leftRole |>.named "the disk B₁"
        |>.describedBy "the closed disk of radius 4/5 about −1" |>.withId "B1",
      Plane.Exact.disk rightCentre disjointRight |>.noFill |>.role rightRole |>.named "the disk B₂"
        |>.describedBy "the closed disk of radius 7/10 about 1" |>.withId "B2",
      Plane.Exact.segment ((-1 / 5 : Rat), (0 : Rat)) ((3 / 10 : Rat), (0 : Rat)) |>.faint |>.dashed
        |>.named "the gap between B₁ and B₂, of length 1/2"
        |>.declRef `TDCSG.leftDisk_disjoint_rightDisk |>.withId "gap",
      Plane.label "gap" ⟨1 / 20, 0⟩ .below |>.withId "gap-label",
      Plane.Exact.arc leftCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role leftRole
        |>.width 1.5 |>.named "the turn a of B₁, 72° clockwise about −1" |>.declRef `TDCSG.genA
        |>.withId "arc-a",
      Plane.Exact.arc rightCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role rightRole
        |>.width 1.5 |>.named "the turn b of B₂, 72° clockwise about 1" |>.declRef `TDCSG.genB
        |>.withId "arc-b",
      Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1"
        |>.withId "centre-left",
      Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1"
        |>.withId "centre-right",
      Plane.Exact.point leftSample |>.role leftRole |>.named "x" |>.incident .inside "the disk B₁"
        |>.incident .outside "the disk B₂" |>.withId "x",
      Plane.Exact.point (leftCentre + phiInv * zeta 1) |>.role leftRole |>.named "a(x)"
        |>.incident .inside "the disk B₁" |>.withId "ax",
      Plane.Exact.point rightSample |>.role rightRole |>.named "y" |>.incident .inside "the disk B₂"
        |>.incident .outside "the disk B₁" |>.withId "y",
      Plane.Exact.point (rightCentre + phiInv * zeta 1) |>.role rightRole |>.named "b(y)"
        |>.incident .inside "the disk B₂" |>.withId "by",
      Plane.Exact.label "−1" leftCentre .below |>.role leftRole |>.withId "centre-label-left",
      Plane.Exact.label "+1" rightCentre .below |>.role rightRole |>.withId "centre-label-right",
      Plane.Exact.label "x" leftSample .auto |>.role leftRole |>.withId "x-label",
      Plane.Exact.label "a(x)" (leftCentre + phiInv * zeta 1) .auto |>.role leftRole
        |>.withId "ax-label",
      Plane.Exact.label "y" rightSample .auto |>.role rightRole |>.withId "y-label",
      Plane.Exact.label "b(y)" (rightCentre + phiInv * zeta 1) .auto |>.role rightRole
        |>.withId "by-label",
      Plane.Exact.label "B₁, radius 4/5" ((-1 : Rat), (-1 : Rat)) |>.role leftRole
        |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two |>.withId "name-B1",
      Plane.Exact.label "B₂, radius 7/10" ((1 : Rat), (-1 : Rat)) |>.role rightRole
        |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two |>.withId "name-B2"] ∧
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
  refine ⟨by unfold disjointDisks; with_reducible rfl, by unfold disjointKeys; with_reducible rfl,
    by unfold disjointDisks; with_reducible rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links disjointDisks disjointDisks_spec

/-- The key frames of `disjointDisks` before the last and its moves, written out. Key `k ≤ 2`
draws, in the frame of the figure of the two turns, two copies of the disks at two fifths of the
size (`disjointScene`, the point `p` drawn at `disjointHalf`, `2p/5` moved left or right), titled
by their order, `a`, then `b` on the left and `b`, then `a` on the right, each with its two points
that move and their labels (`disjointMover`): `x` turned by `a` from key `1` on in the copy of `a`,
then `b` and from key `2` on in the other, `y` turned by `b` from key `2` on in the first and from
key `1` on in the other (`disjointX`, `disjointY`). Every item is drawn at its anchors
(`disjointSceneAnchors`, `disjointMoverAnchors`), and the exact actors of the keys
(`disjointActors`) are those anchors. Step `0` turns `x` by `a` (a fifth of a turn clockwise about
the copy of `-1`) in the first copy and `y` by `b` (about the copy of `1`) in the other; step `1`
the other point of each; step `2` fades the copies out and the figure of the two turns in, at full
size. Each declared move, applied exactly in `ℚ(ζ₅)` to the anchors of the actors of one key, gives
those of the next (`disjointArrives`); at key `2` both copies show `x` at `a(x)` and `y` at
`b(y)`, the points of the figure of the two turns, so both orders end in the same picture. The
captions are written out. Not stated: how the builders draw, the timing and the frames the browser
draws between the key frames. -/
theorem disjointDisks_keys :
    disjointDisks.captions = disjointCaptions ∧
    (disjointCaptions = (
#[
  "Two disjoint closed disks, B₁ of radius 4/5 about −1 and B₂ of radius 7/10 about 1, with a \
    point x in B₁ and a point y in B₂, drawn twice at two fifths of the size: on the left a, \
    then b; on the right b, then a.",
  "Left: a turns B₁ a fifth of a turn clockwise about −1, carrying x, and fixes y. Right: b turns \
    B₂ a fifth of a turn clockwise about +1, carrying y, and fixes x.",
  "Left: b turns y; right: a turns x. Both orders end in the same picture: the two turns move \
    disjoint sets of points, so they commute.",
  "Both orders give this: the turn a of B₁ and the turn b of B₂, each through 72° clockwise; a \
    moves x to a(x) and fixes y, b moves y to b(y) and fixes x."]
    : Array String)) ∧
    (∀ (k : Nat), disjointKey k = (
  { disjointDisksFinal with
    items := disjointKeyItems k
    info := { title := disjointCaptions.getD k "" } }
    : Plane.Figure)) ∧
    (∀ (k : Nat), disjointKeyItems k = (
  #[true, false].flatMap fun b =>
    #[disjointScene b, disjointTitle b, disjointMover b true k, disjointMover b false k]
    : Array Item)) ∧
    (∀ (aFirst : Bool), disjointShift aFirst = (
if aFirst then -19 else 19
    : Int)) ∧
    (∀ (aFirst : Bool) (p : Zeta5), disjointHalf aFirst p = (
  ⟨Zeta5.ofInt 8 * p + Zeta5.ofInt (disjointShift aFirst), 20⟩
    : ZetaFrac)) ∧
    (∀ (aFirst : Bool), disjointTag aFirst = (
if aFirst then "ab" else "ba"
    : String)) ∧
    (∀ (aFirst : Bool), disjointSceneAnchors aFirst = (
  [leftCentre, rightCentre, leftCentre, rightCentre].map (disjointHalf aFirst)
    : List ZetaFrac)) ∧
    (∀ (aFirst : Bool), disjointScene aFirst = (
  let a := fun (i : Nat) => (disjointSceneAnchors aFirst).getD i (ZetaFrac.ofZeta origin)
  let t := disjointTag aFirst
  (group #[Plane.Exact.disk (a 0) (8 / 25 : Rat) |>.noFill |>.role leftRole
        |>.named s!"the disk B₁, order {t}",
      Plane.Exact.disk (a 1) (7 / 25 : Rat) |>.noFill |>.role rightRole
        |>.named s!"the disk B₂, order {t}",
      Plane.Exact.point (a 2) |>.role leftRole, Plane.Exact.point (a 3) |>.role rightRole])
    |>.named s!"the two disks, {if aFirst then "a, then b" else "b, then a"}"
    |>.withId s!"scene-{t}"
    : Item)) ∧
    (∀ (aFirst : Bool), disjointTitle aFirst = (
  Plane.Exact.label (if aFirst then "a, then b" else "b, then a")
    (((if aFirst then -97 / 100 else 93 / 100 : Rat)), (1 / 2 : Rat))
    |>.withId s!"title-{disjointTag aFirst}"
    : Item)) ∧
    (∀ (aFirst : Bool) (k : Nat), disjointXTurned aFirst k = (
if aFirst then 1 ≤ k else 2 ≤ k
    : Bool)) ∧
    (∀ (aFirst : Bool) (k : Nat), disjointYTurned aFirst k = (
if aFirst then 2 ≤ k else 1 ≤ k
    : Bool)) ∧
    (∀ (aFirst : Bool) (k : Nat), disjointX aFirst k = (
  if disjointXTurned aFirst k then Letter.a.rotate leftSample else leftSample
    : Zeta5)) ∧
    (∀ (aFirst : Bool) (k : Nat), disjointY aFirst k = (
  if disjointYTurned aFirst k then Letter.b.rotate rightSample else rightSample
    : Zeta5)) ∧
    (∀ (aFirst isX : Bool) (k : Nat), disjointMoverAnchors aFirst isX k = (
  let p := disjointHalf aFirst (if isX then disjointX aFirst k else disjointY aFirst k)
  [p, p]
    : List ZetaFrac)) ∧
    (∀ (aFirst isX : Bool) (k : Nat), disjointMover aFirst isX k = (
  let a := fun (i : Nat) => (disjointMoverAnchors aFirst isX k).getD i (ZetaFrac.ofZeta origin)
  let t := disjointTag aFirst
  let role := if isX then leftRole else rightRole
  (group #[Plane.Exact.point (a 0) |>.role role
        |>.incident .inside s!"the disk {if isX then "B₁" else "B₂"}, order {t}",
      Plane.Exact.label (if isX then "x" else "y") (a 1) (.toward (-deg 72)) |>.role role])
    |>.named s!"the point {if isX then "x" else "y"}, order {t}"
    |>.withId s!"{t}-{if isX then "x" else "y"}"
    : Item)) ∧
    (∀ (aFirst : Bool), disjointTurnA aFirst = (
⟨disjointHalf aFirst leftCentre, Letter.a.turns⟩
    : ExactTurn)) ∧
    (∀ (aFirst : Bool), disjointTurnB aFirst = (
  ⟨disjointHalf aFirst rightCentre, Letter.b.turns⟩
    : ExactTurn)) ∧
    (disjointFinalIds = (
  ["B1", "B2", "gap", "gap-label", "arc-a", "arc-b", "centre-left", "centre-right", "x", "ax",
    "y", "by", "centre-label-left", "centre-label-right", "x-label", "ax-label", "y-label",
    "by-label", "name-B1", "name-B2"]
    : List String)) ∧
    (∀ (k : Nat), disjointActors k = (
  if k ≤ 2 then
    [true, false].flatMap fun b =>
      let t := disjointTag b
      [⟨s!"scene-{t}", disjointSceneAnchors b⟩, ⟨s!"title-{t}", []⟩,
        ⟨s!"{t}-x", disjointMoverAnchors b true k⟩, ⟨s!"{t}-y", disjointMoverAnchors b false k⟩]
  else disjointFinalIds.map fun id => ⟨id, []⟩
    : List (ExactActor ZetaFrac))) ∧
    disjointMoves 0 =
      [("ab-x", .turn (disjointTurnA true)), ("ba-y", .turn (disjointTurnB false))] ∧
    disjointMoves 1 =
      [("ab-y", .turn (disjointTurnB true)), ("ba-x", .turn (disjointTurnA false))] ∧
    moveKinds (disjointMoves 2) = (["scene-ab", "title-ab", "ab-x", "ab-y", "scene-ba", "title-ba",
      "ba-x", "ba-y"].map (·, "vanish")) ++ disjointFinalIds.map (·, "appear") ∧
    [true, false].all (fun b => (List.range 3).all fun k =>
      (disjointMoverAnchors b true k).length == 2 && (disjointMoverAnchors b false k).length == 2 &&
        (disjointSceneAnchors b).length == 4) = true ∧
    declaredTurns 3 disjointMoves = [-1 / 5, -1 / 5, -1 / 5, -1 / 5] ∧
    Letter.a.turns = -1 / 5 ∧ Letter.b.turns = -1 / 5 ∧ turnsAreFifths = true ∧
    disjointArrives = true ∧
    (disjointX true 2 == disjointX false 2 && disjointY true 2 == disjointY false 2) = true ∧
    (Letter.a.rotate leftSample == leftCentre + phiInv * zeta 1) = true ∧
    (Letter.b.rotate rightSample == rightCentre + phiInv * zeta 1) = true := by
  repeat' apply And.intro
  all_goals first
    | (intros; unfold disjointDisks; with_reducible rfl)
    | (intros; unfold disjointCaptions; with_reducible rfl)
    | (intros; unfold disjointKey; with_reducible rfl)
    | (intros; unfold disjointKeyItems; with_reducible rfl)
    | (intros; unfold disjointShift; with_reducible rfl)
    | (intros; unfold disjointHalf; with_reducible rfl)
    | (intros; unfold disjointTag; with_reducible rfl)
    | (intros; unfold disjointSceneAnchors; with_reducible rfl)
    | (intros; unfold disjointScene; with_reducible rfl)
    | (intros; unfold disjointTitle; with_reducible rfl)
    | (intros; unfold disjointXTurned; with_reducible rfl)
    | (intros; unfold disjointYTurned; with_reducible rfl)
    | (intros; unfold disjointX; with_reducible rfl)
    | (intros; unfold disjointY; with_reducible rfl)
    | (intros; unfold disjointMoverAnchors; with_reducible rfl)
    | (intros; unfold disjointMover; with_reducible rfl)
    | (intros; unfold disjointTurnA; with_reducible rfl)
    | (intros; unfold disjointTurnB; with_reducible rfl)
    | (intros; unfold disjointFinalIds; with_reducible rfl)
    | (intros; unfold disjointActors; with_reducible rfl)
    | decide +kernel
    | (simp only [generatorMoves]; done)
    | (simp only [stepMoves]; done)
    | (simp only [jumpMoves]; done)
    | (simp only [disjointMoves]; done)

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

/-- The key frames of `generatorStep` before the last and its moves, written out. Key `k ≤ 1`
draws, in the frame of the figure of the step, its disks, lens, radius, centres and names and, in
place of its marks of the turn: the content of the left disk (`turningContent`), the segment from
the first sample to `-1` and the samples `turnedSamples`, `0` among them, before the turn (key `0`)
and their images `turnedImages` after it (key `1`), each recording that it lies inside the left
disk; and the points `fixedSamples` outside it (`fixedContent`). Both are drawn at their anchors
(`turningAnchors`, `fixedAnchors`), and the exact actors of the keys (`generatorActors`) are those
anchors: the arrival check reads the points the keys draw, and every actor that moves has anchors.
Step `0` turns the content of the disk by `generatorTurn`, a fifth of a turn clockwise about `-1`;
step `1` fades it and the points outside out and the marks of the figure of the step in. The
declared turn, applied exactly in `ℚ(ζ₅)` to the anchors of key `0`, gives those of key `1`
(`generatorArrives`). The samples are what the generator does with them: each of `turnedSamples`
lies in the closed left disk of radius `3/2` and `a` carries it to its image, the first to `a(0)`;
each of `fixedSamples` lies outside it and `a` fixes it. The captions are written out. Not stated:
how the builders draw, the timing and the frames the browser draws between the key frames. -/
theorem generatorStep_keys :
    generatorStep.captions = generatorCaptions ∧
    (generatorCaptions = (
#[
  "The left generator a acts on its closed disk of radius 1.5 about −1. The points inside the \
    disk, the origin among them (drawn in the color of the left disk), turn with it; the points \
    outside it stay where they are.",
  "a turns the disk a fifth of a turn clockwise about −1: the origin goes to a(0) = −1 + ζ⁴, \
    and the points outside the left disk have not moved.",
  "One step of the left generator: a turns the origin through 72° clockwise about −1, along the \
    dashed arc, to a(0). The origin lies in both disks, a(0) in the left disk only."]
    : Array String)) ∧
    (∀ (k : Nat), generatorKey k = (
  { generatorStepFinal with items := generatorKeyItems k,
                            info := { title := generatorCaptions.getD k "" } }
    : Plane.Figure)) ∧
    (∀ (k : Nat), generatorSamples k = (
if k == 0 then turnedSamples else turnedImages
    : List Zeta5)) ∧
    (∀ (k : Nat), generatorKeyItems k = (
  generatorBase ++
    #[turningContent (generatorSamples k), fixedContent] ++
    generatorCentres ++ generatorLabels ++ generatorNames
    : Array Item)) ∧
    (turnedSamples = (
  [origin, leftCentre + phiInv * zeta 3, zeta 4 - Zeta5.ofInt 2, leftCentre + zeta 2 - zeta 3]
    : List Zeta5)) ∧
    (fixedSamples = (
  [phiInv, leftCentre + (Zeta5.ofInt 1 + phiInv) * zeta 2,
    leftCentre + (Zeta5.ofInt 1 + phiInv) * zeta 3]
    : List Zeta5)) ∧
    (turnedImages = (
turnedSamples.map Letter.a.rotate
    : List Zeta5)) ∧
    (∀ (zs : List Zeta5), turningAnchors zs = (
  let z := ZetaFrac.ofZeta (zs.headD origin)
  [z, ZetaFrac.ofZeta leftCentre] ++ zs.map ZetaFrac.ofZeta
    : List ZetaFrac)) ∧
    (∀ (as : List ZetaFrac), turningContentAt as = (
  let o := ZetaFrac.ofZeta origin
  (group (#[Plane.Exact.segment (as.getD 0 o) (as.getD 1 o) |>.role leftRole |>.width 1.5,
      Plane.Exact.point (as.getD 2 o) |>.role leftRole] ++
    (as.drop 3).toArray.map fun w =>
      Plane.Exact.point w |>.role leftRole |>.size 3 |>.incident .inside "the left circle"))
    |>.named "points of the left disk, which a turns" |>.withId "disk"
    : Item)) ∧
    (∀ (zs : List Zeta5), turningContent zs = (
turningContentAt (turningAnchors zs)
    : Item)) ∧
    (fixedAnchors = (
fixedSamples.map ZetaFrac.ofZeta
    : List ZetaFrac)) ∧
    (fixedContent = (
  group (fixedAnchors.toArray.map fun w =>
      Plane.Exact.point w |>.size 3 |>.incident .outside "the left circle")
    |>.named "points outside the left disk, which a fixes" |>.withId "outside"
    : Item)) ∧
    (generatorTurn = (
⟨ZetaFrac.ofZeta leftCentre, Letter.a.turns⟩
    : ExactTurn)) ∧
    (∀ (k : Nat), generatorActors k = (
  let z := ZetaFrac.ofZeta
  if k ≤ 1 then
    [⟨"disk", turningAnchors (generatorSamples k)⟩, ⟨"outside", fixedAnchors⟩]
  else
    [⟨"image-spoke", [z leftCentre, z aZero]⟩, ⟨"angle", [z leftCentre]⟩,
      ⟨"angle-label", [z leftCentre]⟩, ⟨"arc", [z origin, z aZero]⟩, ⟨"origin", [z origin]⟩,
      ⟨"image", [z aZero]⟩, ⟨"image-label", [z aZero]⟩]
    : List (ExactActor ZetaFrac))) ∧
    generatorMoves 0 = [("disk", .turn generatorTurn)] ∧
    moveKinds (generatorMoves 1) = [("disk", "vanish"), ("outside", "vanish"),
      ("image-spoke", "appear"), ("angle", "appear"), ("angle-label", "appear"), ("arc", "appear"),
      ("origin", "appear"), ("image", "appear"), ("image-label", "appear")] ∧
    (turningAnchors turnedSamples).length = 6 ∧ (turningAnchors turnedImages).length = 6 ∧
    fixedAnchors.length = 3 ∧
    declaredTurns 2 generatorMoves = [-1 / 5] ∧ Letter.a.turns = -1 / 5 ∧ turnsAreFifths = true ∧
    generatorArrives = true ∧
    turnedSamples.all (Letter.a.covers r2ThreeHalves) = true ∧
    (turnedSamples.map (Letter.a.act r2ThreeHalves) == turnedImages) = true ∧
    (turnedImages.headD origin == aZero) = true ∧
    fixedSamples.all (fun z => !Letter.a.covers r2ThreeHalves z) = true ∧
    (fixedSamples.map (Letter.a.act r2ThreeHalves) == fixedSamples) = true := by
  repeat' apply And.intro
  all_goals first
    | (intros; unfold generatorStep; with_reducible rfl)
    | (intros; unfold generatorCaptions; with_reducible rfl)
    | (intros; unfold generatorKey; with_reducible rfl)
    | (intros; unfold generatorSamples; with_reducible rfl)
    | (intros; unfold generatorKeyItems; with_reducible rfl)
    | (intros; unfold turnedSamples; with_reducible rfl)
    | (intros; unfold fixedSamples; with_reducible rfl)
    | (intros; unfold turnedImages; with_reducible rfl)
    | (intros; unfold turningAnchors; with_reducible rfl)
    | (intros; unfold turningContentAt; with_reducible rfl)
    | (intros; unfold turningContent; with_reducible rfl)
    | (intros; unfold fixedAnchors; with_reducible rfl)
    | (intros; unfold fixedContent; with_reducible rfl)
    | (intros; unfold generatorTurn; with_reducible rfl)
    | (intros; unfold generatorActors; with_reducible rfl)
    | decide +kernel
    | (simp only [generatorMoves]; done)
    | (simp only [stepMoves]; done)
    | (simp only [jumpMoves]; done)
    | (simp only [disjointMoves]; done)

end TDCSGFigures
```

{figref "word-steps"}[]: the animation `TDCSGFigures.wordSteps`, an illustration, and the data of
its key frames, `TDCSGFigures.wordSteps_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-- The animation `wordSteps` and the data its key frames are drawn from, written out; an
illustration, to which this theorem is not linked. It has one panel whose keys are `stepKey k`,
`k = 0, …, 4`, and whose steps are made from the declared moves `stepMoves`; its poster, the still
shown while it is pointed at or focused, under reduced motion and in print, is the last key. Every
key draws `stepBase` (the two disks of radius `2.1`, their lens, the centres recording where they
stand, and the names), then the circle about the centre of the last turn (`stepPivot`), at key `4`
the segment from `-1` to `z₃` (`stepReach`), the points left behind, faint and labelled
(`stepTrail`, each recording exactly where it stands relative to the two disks and the lens), the
point `z_k` (`stepMover`) and its name (`stepLabel`). The points are drawn at their anchors
(`stepAnchors`), and the exact actors of the keys (`stepActors`) are those anchors. The points are
`z₀ = 0, z₁ = -1 + ζ⁴ = a(0), z₂ = b(z₁), z₃ = b(z₂), z₄ = a(z₃) = z₃`, written out in the basis
`1, ζ, ζ², ζ³`; the letters `a, b, b` find their point in their closed disk of radius `2.1` and the
last `a` does not (`|z₃ + 1|² > 441/100`), so it fixes `z₃`. Step `k` turns the point by
`stepTurn k`, about the centre of letter `k + 1` by `-1/5` of a full turn, when that letter acts,
and fades the circles, the names, the points left behind and the segment in and out; each declared
move, applied exactly in `ℚ(ζ₅)` to the anchors of the actors of one key, gives those of the next
(`stepsArrive`), so every turn carries `z_k` onto `z_{k+1}`. The captions are written out. Not
stated: how the builders draw, the timing and the frames the browser draws between the key frames.
-/
theorem wordSteps_spec :
    wordSteps.panels = #[{ motion :=
      { keys := ((List.range 5).map stepKey).toArray,
        steps := ((List.range 4).map (exactStep ∘ stepMoves)).toArray } }] ∧
    wordSteps.captions = stepCaptions ∧ wordSteps.poster = 4 ∧
    stepWord = [.a, .b, .b, .a] ∧
    (stepCaptions = (
#[
  "z₀ = 0, in both disks. The word a b b a is applied to it at radius 2.1, letter by letter from \
    left to right.",
  "Letter 1, a: z₀ lies in the left disk, so a turns it a fifth of a turn clockwise about −1 \
    (circled), to z₁.",
  "Letter 2, b: z₁ lies in the right disk, so b turns it a fifth of a turn clockwise about +1 \
    (circled), to z₂.",
  "Letter 3, b: z₂ lies in the right disk, so b turns it again, to z₃.",
  "Letter 4, a: z₃ lies outside the left disk, farther than 2.1 from −1 (dashed), so a leaves it \
    where it is: z₄ = z₃."]
    : Array String)) ∧
    (r2Step = (
rat (441 / 100)
    : QSqrt5)) ∧
    (stepBase = (
#[
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
    : Array Item)) ∧
    (∀ (k : Nat), stepKey k = (
  { width := figureWidth
    padding := 16
    style := houseStyle
    checks := .fail
    items := stepKeyItems k
    info := { title := s!"The point {stepName k} of 0 under a b b a at radius 2.1" } }
    : Plane.Figure)) ∧
    (∀ (k : Nat), stepKeyItems k = (
  stepBase ++ stepPivot k ++ stepReach k ++ (stepTrailIndices k).toArray.map stepTrail ++
    #[stepMover k, stepLabel k]
    : Array Item)) ∧
    (∀ (k : Nat), stepPoint k = (
stepPoints.getD k origin
    : Zeta5)) ∧
    (∀ (k : Nat), stepAnchors k = (
[ZetaFrac.ofZeta (stepPoint k)]
    : List ZetaFrac)) ∧
    (∀ (k : Nat), stepMover k = (
  Plane.Exact.point ((stepAnchors k).headD (ZetaFrac.ofZeta origin)) |>.size 5
    |>.named "the point followed through the word" |>.withId "point"
    : Item)) ∧
    (∀ (k : Nat), stepLabelText k = (
if k == 4 then "z₄ = z₃" else stepName k
    : String)) ∧
    (∀ (k : Nat), stepLabel k = (
  Plane.Exact.label (stepLabelText k) ((stepAnchors k).headD (ZetaFrac.ofZeta origin)) .auto
    |>.bold |>.withId s!"name-{k}"
    : Item)) ∧
    (∀ (j : Nat), stepTrail j = (
  let p := (stepAnchors j).headD (ZetaFrac.ofZeta origin)
  (group #[withSidesStep (stepPoint j) (Plane.Exact.point p |>.faint),
      Plane.Exact.label (stepName j) p .auto])
    |>.named (stepName j) |>.withId s!"trail-{j}"
    : Item)) ∧
    (∀ (k : Nat), stepTrailIndices k = (
  (List.range k).filter fun j => !(stepPoint j == stepPoint k)
    : List Nat)) ∧
    (∀ (k : Nat), stepPivot k = (
  if k == 0 || 3 < k then #[]
  else
    let c := (stepWord.getD (k - 1) .a).centre
    let left := c == leftCentre
    #[Plane.Exact.circle c stepPivotRadius |>.role (if left then leftRole else rightRole)
      |>.width 2 |>.named s!"a circle about the center {if left then "−1" else "+1"} of the last \
        turn" |>.withId (if left then "pivot-left" else "pivot-right")]
    : Array Item)) ∧
    (∀ (k : Nat), stepReach k = (
  if k == 4 then
    #[Plane.Exact.segment leftCentre (stepPoint 3) |>.role leftRole |>.width 1.5 |>.dashed
      |>.named "from −1 to z₃, longer than 2.1" |>.withId "reach"]
  else #[]
    : Array Item)) ∧
    (stepPivotRadius = (
1 / 5
    : Rat)) ∧
    (∀ (k : Nat), stepTurn k = (
  let l := stepWord.getD k .a
  ⟨ZetaFrac.ofZeta l.centre, l.turns⟩
    : ExactTurn)) ∧
    (∀ (k : Nat), stepPivotId k = (
  if (stepWord.getD k .a).centre == leftCentre then "pivot-left" else "pivot-right"
    : String)) ∧
    (∀ (k : Nat), stepActors k = (
  let z := ZetaFrac.ofZeta
  let pivot : List (ExactActor ZetaFrac) :=
    if k == 0 || 3 < k then []
    else
      let c := (stepWord.getD (k - 1) .a).centre
      [⟨if c == leftCentre then "pivot-left" else "pivot-right", [z c]⟩]
  let reach : List (ExactActor ZetaFrac) :=
    if k == 4 then [⟨"reach", [z leftCentre, z (stepPoint 3)]⟩] else []
  pivot ++ reach ++ (stepTrailIndices k).map (fun j => ⟨s!"trail-{j}", stepAnchors j⟩) ++
    [⟨"point", stepAnchors k⟩, ⟨s!"name-{k}", stepAnchors k⟩]
    : List (ExactActor ZetaFrac))) ∧
    (stepPoints == [⟨#[0, 0, 0, 0]⟩, ⟨#[-2, -1, -1, -1]⟩, ⟨#[3, 2, 2, 3]⟩, ⟨#[1, 0, 1, -2]⟩,
      ⟨#[1, 0, 1, -2]⟩]) = true ∧
    ((stepWord.zip stepPoints).map fun (l, z) => l.covers r2Step z) = [true, true, true, false] ∧
    QSqrt.lt r2Step ((stepPoints.getD 3 origin) - leftCentre).normSq = true ∧
    (stepWord.all fun l => l.turn == zeta 4) = true ∧
    (List.range 3).map stepPivotId = ["pivot-left", "pivot-right", "pivot-right"] ∧
    stepMoves 0 = [("point", .turn (stepTurn 0)), (stepPivotId 0, .appear),
      ("trail-0", .appear), ("name-0", .vanish), ("name-1", .appear)] ∧
    stepMoves 1 = [("point", .turn (stepTurn 1)), (stepPivotId 1, .appear),
      ("trail-1", .appear), (stepPivotId 0, .vanish), ("name-1", .vanish), ("name-2", .appear)] ∧
    stepMoves 2 = [("point", .turn (stepTurn 2)), ("trail-2", .appear), ("name-2", .vanish),
      ("name-3", .appear)] ∧
    stepMoves 3 = [("reach", .appear), (stepPivotId 2, .vanish), ("name-3", .vanish),
      ("name-4", .appear)] ∧
    (List.range 5).all (fun k => (stepAnchors k).length == 1) = true ∧
    declaredTurns 4 stepMoves = [-1 / 5, -1 / 5, -1 / 5] ∧
    declaredTurns 4 stepMoves = (stepWord.take 3).map Letter.turns ∧ turnsAreFifths = true ∧
    stepsArrive = true := by
  repeat' apply And.intro
  all_goals first
    | (intros; unfold wordSteps; with_reducible rfl)
    | (intros; unfold stepWord; with_reducible rfl)
    | (intros; unfold stepCaptions; with_reducible rfl)
    | (intros; unfold r2Step; with_reducible rfl)
    | (intros; unfold stepBase; with_reducible rfl)
    | (intros; unfold stepKey; with_reducible rfl)
    | (intros; unfold stepKeyItems; with_reducible rfl)
    | (intros; unfold stepPoint; with_reducible rfl)
    | (intros; unfold stepAnchors; with_reducible rfl)
    | (intros; unfold stepMover; with_reducible rfl)
    | (intros; unfold stepLabelText; with_reducible rfl)
    | (intros; unfold stepLabel; with_reducible rfl)
    | (intros; unfold stepTrail; with_reducible rfl)
    | (intros; unfold stepTrailIndices; with_reducible rfl)
    | (intros; unfold stepPivot; with_reducible rfl)
    | (intros; unfold stepReach; with_reducible rfl)
    | (intros; unfold stepPivotRadius; with_reducible rfl)
    | (intros; unfold stepTurn; with_reducible rfl)
    | (intros; unfold stepPivotId; with_reducible rfl)
    | (intros; unfold stepActors; with_reducible rfl)
    | decide +kernel
    | (simp only [generatorMoves]; done)
    | (simp only [stepMoves]; done)
    | (simp only [jumpMoves]; done)
    | (simp only [disjointMoves]; done)

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
`wordLoop 2`, `wordLoop 3`: one panel whose keys are `wordKey i k` and whose steps are
`wordStep i k`, with the captions `wordCaption i k`; the poster, the still shown while the picture
is pointed at or focused, under reduced motion and in print, is the last key, where the image lies
on the chord again. Key `k` draws, over the disks, their lens, the
chord and the piece (`wordUnder`), the image `[w_k(p), w_k(q)]` of the piece `[p, q]` after `k`
letters (`wordSegment`, read from `wordPath i`, here written out in the basis `1, ζ, ζ², ζ³`), the
circle about the centre of the turn before it (`wordPivot`) and the ends lying on a boundary circle
before the next letter (`wordContacts`, from `wordEqualities i`). Step `k` turns the image by the
declared turn `wordTurn i k`, about the centre of letter `k + 1` by the letter's own fraction
`Letter.turns`, and fades the other marks in and out (`wordFades`); that declared turn, applied
exactly in `ℚ(ζ₅)`, carries both ends of image `k` onto those of image `k + 1` (`wordArrives`), and
its fraction, written out in `wordLoop_keys`, is the letter's fifth in the letter's sense
(`turnsAreFifths`). Before every letter both current ends lie in the letter's closed disk of radius
`R` (`wordChecks`), so the letter turns the whole segment, as in `TDCSG.Five.applyWord_chord`; the
tests that hold with equality are those before letters 3, 4 of word 1, letters 2, 3 of word 2 and
letters 1, 2, 5, 6 of word 3. The caption of key `k ≥ 1` names letter `k`, its turn and its
direction. The last images are the pieces moved by `(2φ - 2)E` (words 1, 2) and `(2φ - 4)E`
(word 3). Not stated: how the builders draw, the timing and the frames the browser draws between
the key frames. -/
theorem wordLoop_figures :
    wordLoop1 = wordLoop 1 ∧ wordLoop2 = wordLoop 2 ∧ wordLoop3 = wordLoop 3 ∧
    (∀ i, (wordLoop i).panels =
      #[{ motion := { keys := wordLoopKeys i, steps := wordLoopSteps i } }]) ∧
    (∀ i, wordLoopKeys i =
      ((List.range ((wordPiece i).1.length + 1)).map (wordKey i)).toArray) ∧
    (∀ i, wordLoopSteps i =
      ((List.range (wordPiece i).1.length).map (wordStep i)).toArray) ∧
    (∀ i, (wordLoop i).captions =
      ((List.range ((wordPiece i).1.length + 1)).map (wordCaption i)).toArray) ∧
    (∀ i, (wordLoop i).poster = (wordPiece i).1.length) ∧
    (∀ i k, (wordKey i k).items =
      wordUnder i ++ (#[wordSegment i k] ++ wordPivot i k ++ wordContacts i k) ++ wordOver i) ∧
    (∀ i k, wordSegment i k =
      (Plane.Exact.segment ((wordPath i).getD k (origin, origin)).1
        ((wordPath i).getD k (origin, origin)).2 |>.role (pieceRole i) |>.width 4
        |>.named s!"the image of the piece of word {i}" |>.withId "segment")) ∧
    (∀ i k, wordStep i k =
      { moves := #[("segment", Plane.Exact.turnAbout (wordTurn i k).centre (wordTurn i k).turns)] ++
          wordFades i k }) ∧
    (∀ i k, wordTurn i k =
      ⟨ZetaFrac.ofZeta ((wordPiece i).1.getD k .a).centre, ((wordPiece i).1.getD k .a).turns⟩) := by
  exact ⟨by unfold wordLoop1; with_reducible rfl, by unfold wordLoop2; with_reducible rfl,
    by unfold wordLoop3; with_reducible rfl, fun _ => by unfold wordLoop; with_reducible rfl,
    fun _ => rfl, fun _ => rfl, fun _ => by unfold wordLoop; with_reducible rfl,
    fun _ => by unfold wordLoop; with_reducible rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => by unfold wordTurn; with_reducible rfl⟩

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
    (List.range 5).map (fun k => (wordTurn 1 k).turns) = [1 / 5, 1 / 5, 1 / 5, 1 / 5, 1 / 5] ∧
    (List.range 5).map (fun k => (wordTurn 2 k).turns) = [-1 / 5, -1 / 5, -1 / 5, -1 / 5, -1 / 5] ∧
    (List.range 6).map (fun k => (wordTurn 3 k).turns) =
      [-1 / 5, -1 / 5, -1 / 5, 1 / 5, 1 / 5, 1 / 5] ∧
    [1, 2, 3].all (fun i => (List.range (wordPiece i).1.length).all fun k =>
      (wordTurn i k).turns == ((wordPiece i).1.getD k .a).turns) = true ∧
    turnsAreFifths = true ∧
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

/-- The key frames of `exchangedIntervals` before the last and its slides, written out. Key
`k ≤ 3` draws, in the frame of the figure of the two rows, the row before the return, the names,
and a copy of each piece (`intervalCopy`), drawn at its ends (`intervalCopyAnchors`): pieces
`1, …, k` at their places in the row after the return, the others still on the row before. The
exact actors of the keys (`intervalActors`) are those ends. Step `k < 3` slides the copy of piece
`k + 1` by `intervalSlide (k + 1)`, `(2φ - 2, -1/2)` for pieces `1` and `2` and `(2φ - 4, -1/2)`
for piece `3`: the move of its word along the chord, as the return map `chordStep` applies word
`i` to the midpoint of piece `i`, and the drop from one row to the other. Step `3` fades the copies
out and the row after in. Each declared slide, applied exactly in `ℚ(√5)²` to the ends of the
copies of one key, gives those of the next (`intervalArrives`). The captions are written out. Not
stated: how the builders draw, the timing and the frames the browser draws between the key
frames. -/
theorem exchangedIntervals_keys :
    exchangedIntervals.captions = intervalCaptions ∧
    (intervalCaptions = (
#[
  "The three pieces of [−1, 1) before one return, in the order 1, 2, 3 (top row). The word of \
    each piece moves it along the chord.",
  "Word 1 moves piece 1, −1 ≤ t ≤ 1 − φ, by 2φ − 2 to the right.",
  "Word 2 moves piece 2, 1 − φ < t < 3 − 2φ, by 2φ − 2 to the right, beside the image of piece \
    1.",
  "Word 3 moves piece 3, 3 − 2φ ≤ t < 1, by 2φ − 4 to the left, to the left end of the \
    interval.",
  "After one return the pieces read 3, 1, 2 on the same interval. Joined into a circle of \
    circumference two, the three moves are one rotation by 2φ − 2 = 2/φ."]
    : Array String)) ∧
    (∀ (k : Nat), intervalKey k = (
  if 3 < k then exchangedIntervalsFinal
  else { exchangedIntervalsFinal with items := intervalKeyItems k,
                                      info := { title := intervalCaptions.getD k "" } }
    : Plane.Figure)) ∧
    (∀ (k : Nat), intervalKeyItems k = (
  (#[1, 2, 3].flatMap fun i => intervalBand i false) ++
    #[1, 2, 3].map (fun i => intervalCopy i (decide (i ≤ k))) ++ intervalNames
    : Array Item)) ∧
    (∀ (i : Nat) (moved : Bool), intervalCopyAnchors i moved = (
  let (a, b) := returnInterval i moved
  [(a, intervalRowY moved), (b, intervalRowY moved)]
    : List (QSqrt5 × QSqrt5))) ∧
    (∀ (i : Nat) (moved : Bool), intervalCopy i moved = (
  let e := fun (j : Nat) => (intervalCopyAnchors i moved).getD j (rat 0, rat 0)
  Plane.Exact.segment (e 0) (e 1) |>.width 5 |>.role (pieceRole i)
    |>.named s!"a copy of piece {i}, moved by word {i}" |>.withId s!"piece-{i}"
    : Item)) ∧
    (∀ (k : Nat), intervalMoves k = (
  if k < 3 then [(s!"piece-{k + 1}", .slide (intervalSlide (k + 1)))]
  else [1, 2, 3].flatMap fun i =>
    [(s!"piece-{i}", .vanish), (s!"after-{i}", .appear), (s!"after-label-{i}", .appear)]
    : List (String × ExactMove (QSqrt5 × QSqrt5)))) ∧
    (∀ (i : Nat), intervalSlide i = (
  ((returnInterval i true).1 - (returnInterval i false).1, intervalRowY true - intervalRowY false)
    : QSqrt5 × QSqrt5)) ∧
    (∀ (k : Nat), intervalActors k = (
  if k ≤ 3 then
    [1, 2, 3].map fun i => ⟨s!"piece-{i}", intervalCopyAnchors i (decide (i ≤ k))⟩
  else
    [1, 2, 3].flatMap fun i =>
      let (a, b) := returnInterval i true
      [⟨s!"after-{i}", [(a, intervalRowY true), (b, intervalRowY true)]⟩,
        ⟨s!"after-label-{i}", [((a + b) * rat (1 / 2), intervalRowY true)]⟩]
    : List (ExactActor (QSqrt5 × QSqrt5)))) ∧
    moveKinds (intervalMoves 3) = [("piece-1", "vanish"), ("after-1", "appear"),
      ("after-label-1", "appear"), ("piece-2", "vanish"), ("after-2", "appear"),
      ("after-label-2", "appear"), ("piece-3", "vanish"), ("after-3", "appear"),
      ("after-label-3", "appear")] ∧
    [1, 2, 3].all (fun i => let v := intervalSlide i
      v.1 == phi * rat 2 - rat (if i == 3 then 4 else 2) && v.2 == rat (-1 / 2)) = true ∧
    [1, 2, 3].all (fun i =>
      let m := ((returnInterval i false).1 + (returnInterval i false).2) * rat (1 / 2)
      (chordStep m).1 == i && (chordStep m).2 - m == (intervalSlide i).1) = true ∧
    [1, 2, 3].all (fun i => (intervalCopyAnchors i false).length == 2 &&
      (intervalCopyAnchors i true).length == 2) = true ∧
    intervalArrives = true := by
  repeat' apply And.intro
  all_goals first
    | (intros; unfold exchangedIntervals; with_reducible rfl)
    | (intros; unfold intervalCaptions; with_reducible rfl)
    | (intros; unfold intervalKey; with_reducible rfl)
    | (intros; unfold intervalKeyItems; with_reducible rfl)
    | (intros; unfold intervalCopyAnchors; with_reducible rfl)
    | (intros; unfold intervalCopy; with_reducible rfl)
    | (intros; unfold intervalMoves; with_reducible rfl)
    | (intros; unfold intervalSlide; with_reducible rfl)
    | (intros; unfold intervalActors; with_reducible rfl)
    | decide +kernel
    | (simp only [generatorMoves]; done)
    | (simp only [stepMoves]; done)
    | (simp only [jumpMoves]; done)
    | (simp only [disjointMoves]; done)

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

/-- The key frames of `chordOrbit` before the last and its hops, written out. Key
`k ≤ orbitHops` draws, in the frame of the figure of the returns, the frame, the axis of steps,
the points of rows `0, …, k - 1` and the point that hops at row `k`, on `t_k` (`orbitHopper`), drawn
at its anchor (`orbitHopAnchors`); the exact actors of the keys (`orbitActors`) are those points.
Step `k < orbitHops` slides the point by `(t_{k+1} - t_k, -1/20)`, one return: the move `2φ - 2` or
`2φ - 4` of the word applied at `t_k` (`chordStep`) and one row down, and fades in the point of row
`k` that it leaves; step `orbitHops` fades it out and the rows from `orbitHops` on in. Each declared
move, applied exactly in `ℚ(√5)²` to the anchors of the actors of one key, gives those of the next
(`orbitArrives`). The caption of each key is stated as a function of the rows (`orbitCaption`);
its words, which the kernel does not compute, are pinned by `#guard` in `TDCSGTests.Motions`. Not
stated: how the builders draw, the timing and the frames the browser draws between the key
frames. -/
theorem chordOrbit_keys :
    chordOrbit.captions = ((List.range (orbitHops + 2)).map orbitCaption).toArray ∧
    (∀ (k : Nat), orbitKey k = (
  if orbitHops < k then chordOrbitFinal
  else { chordOrbitFinal with items := orbitKeyItems k, info := { title := orbitCaption k } }
    : Plane.Figure)) ∧
    (∀ (k : Nat), orbitKeyItems k = (
  chordOrbitFrame ++ stepAxis ++
    ((chordRows orbitSteps).extract 0 k).mapIdx (fun j (w, t) => rowPoint j w t) ++
    #[orbitHopper k]
    : Array Item)) ∧
    (∀ (k : Nat), orbitHopAnchors k = (
  [tPoint ((chordRows orbitSteps).getD k (0, rat 0)).2 (rowY k)]
    : List (QSqrt5 × QSqrt5))) ∧
    (∀ (k : Nat), orbitHopper k = (
  Plane.Exact.point ((orbitHopAnchors k).headD (rat 0, rat 0)) |>.size 5
    |>.named "the point tE of the orbit, one return per hop" |>.withId "hop"
    : Item)) ∧
    (∀ (k : Nat), orbitMoves k = (
  let rows := chordRows orbitSteps
  if k < orbitHops then
    [("hop", .slide ((rows.getD (k + 1) (0, rat 0)).2 - (rows.getD k (0, rat 0)).2,
        rowY (k + 1) - rowY k)), (s!"row-{k}", .appear)]
  else
    [("hop", .vanish)] ++ (List.range (orbitSteps + 1 - orbitHops)).map fun j =>
      (s!"row-{orbitHops + j}", .appear)
    : List (String × ExactMove (QSqrt5 × QSqrt5)))) ∧
    (∀ (k : Nat), orbitActors k = (
  let rows := chordRows orbitSteps
  let shown := if k ≤ orbitHops then k else orbitSteps + 1
  ((List.range shown).map fun j => ⟨s!"row-{j}", [tPoint (rows.getD j (0, rat 0)).2 (rowY j)]⟩) ++
    (if k ≤ orbitHops then [⟨"hop", orbitHopAnchors k⟩] else [])
    : List (ExactActor (QSqrt5 × QSqrt5)))) ∧
    (∀ (w : Nat), orbitShiftText w = (
if w == 3 then "2φ − 4" else "2φ − 2"
    : String)) ∧
    (∀ (k : Nat), orbitCaption k = (
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
    : String)) ∧
    moveKinds (orbitMoves orbitHops) = [("hop", "vanish")] ++
      (List.range 13).map (fun j => (s!"row-{12 + j}", "appear")) ∧
    (List.range orbitHops).all (fun k =>
      let (w, t) := (chordRows orbitSteps).getD k (0, rat 0)
      ((chordRows orbitSteps).getD (k + 1) (0, rat 0)).2 - t == (chordStep t).2 - t &&
        (chordStep t).1 == w) = true ∧
    (List.range (orbitHops + 1)).all (fun k => (orbitHopAnchors k).length == 1) = true ∧
    orbitArrives = true := by
  repeat' apply And.intro
  all_goals first
    | (intros; unfold chordOrbit; with_reducible rfl)
    | (intros; unfold orbitKey; with_reducible rfl)
    | (intros; unfold orbitKeyItems; with_reducible rfl)
    | (intros; unfold orbitHopAnchors; with_reducible rfl)
    | (intros; unfold orbitHopper; with_reducible rfl)
    | (intros; unfold orbitMoves; with_reducible rfl)
    | (intros; unfold orbitActors; with_reducible rfl)
    | (intros; unfold orbitShiftText; with_reducible rfl)
    | (intros; unfold orbitCaption; with_reducible rfl)
    | decide +kernel
    | (simp only [generatorMoves]; done)
    | (simp only [stepMoves]; done)
    | (simp only [jumpMoves]; done)
    | (simp only [disjointMoves]; done)

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

set_option maxHeartbeats 4000000 in
/-- The frame pair and the data its key frames are drawn from. The figure is the motion of the
default configuration (`FramePairConfig.motion`): the word `a b⁻¹ a b a⁻¹ b⁻¹ a b a⁻¹ b` applied
to `z = 0` at `r = 2.12`, with an arrow for each turn and without the rings that mark turn
centres; its two panels' keys are the key figures `FramePairConfig.keys`, its steps are
made by `panelStep` from the declared moves `FramePairConfig.frameSteps`, and its captions are
`FramePairConfig.keyCaption` of each key, written out in full.
The states after `0, 1, …, 10` letters are computed exactly: the labels `n` of the current left
centre and the direction indices `j`, written out; the letters `3` and `8` do not act, every other
letter does (the exact disk test `Early.Letter.covers`), and every letter is decided by a margin
of at least `0.08`: the centre of its disk lies at least that far inside or outside the window
(`marginsVisible`); every state satisfies the framing equation `2 (x - P(n)) = ζʲ (y + 1)` of
`TDCSG.Five.Framed` exactly. The turns alternate between the two centres except across a letter
that does not act, where the same centre turns twice (`pivotsAlternate`; the letters that act,
with the side of their disk, are written out). The thirty-one keys, written out, are for each
letter that acts the state before it with its arrows, the state after it with its arrows and the
state after it without them, and for each letter that does not act its ring, the ring held, and
the state without it. Every declared move, a fifth of a turn of the point about the centre of the
letter's halved disk on the left, of the body of centres and riding disks about the active centre
on the right, an arrow or a ring appearing or vanishing, or a pause, carries the items of one key
onto those of the next exactly in `ℚ(ζ₅)`; each ring lies about the centre of its letter's disk in
both panels, a centre outside the window (`ringsPlaced`); and each arrow is shown exactly in the
two keys of its turn, about that turn's declared centre and in its sense, in both panels
(`arrowsPlaced`), and the declared fractions, written out for both panels, are the letters' own
fifths, `turnFactor l.turns = some l.turn` with `|l.turns| = 1/5` (`turnsAreFifths`) (all in
`FramePairConfig.allArrive`; the general statements are
`TDCSG.Five.halved_genA`, `TDCSG.Five.halved_genB`, `TDCSG.Five.framePicture_genA_genB` and, for
the inverse letters, `TDCSG.Five.halved_permA_symm`, `TDCSG.Five.halved_permB_symm` and
`TDCSG.Five.framePicture_symm`). Not stated: how the builders draw, the layout, the timing and the
frames the browser draws between the key frames. -/
theorem framePair_keys :
    framePair = ({} : FramePairConfig).motion ∧
    ({} : FramePairConfig).word = word ∧ ({} : FramePairConfig).radius = pairRadius ∧
    ({} : FramePairConfig).arrowMark = true ∧
    ({} : FramePairConfig).pivotMark = false ∧ ({} : FramePairConfig).faintDisks = false ∧
    word = [.a, .bInv, .a, .b, .aInv, .bInv, .a, .b, .aInv, .b] ∧ pairRadius = 53 / 25 ∧
    ({} : FramePairConfig).motion.panels =
      #[{ title := "Traditional view",
          motion := { keys := ({} : FramePairConfig).leftKeys,
                      steps := ({} : FramePairConfig).leftSteps } },
        { title := "Moving frame",
          motion := { keys := ({} : FramePairConfig).rightKeys,
                      steps := ({} : FramePairConfig).rightSteps } }] ∧
    (∀ cfg : FramePairConfig, cfg.leftKeys = cfg.keys.map fun p => { p.1 with view := none }) ∧
    (∀ cfg : FramePairConfig, cfg.rightKeys = cfg.keys.map fun p => { p.2 with view := none }) ∧
    (∀ cfg : FramePairConfig, cfg.leftSteps = cfg.frameSteps.toArray.map fun s =>
      panelStep s.leftTurn s.leftTurning s.appearLeft s.vanishLeft) ∧
    (∀ cfg : FramePairConfig, cfg.rightSteps = cfg.frameSteps.toArray.map fun s =>
      panelStep s.rightTurn s.rightTurning s.appearRight s.vanishRight) ∧
    (∀ t turning appear vanish, panelStep t turning appear vanish =
      let turns : Array (String × Move) := match t with
        | some t => turning.toArray.map fun id => (id, Plane.Exact.turnAbout t.centre t.turns)
        | none => #[]
      let moves := turns ++ appear.toArray.map (·, Move.appear) ++
        vanish.toArray.map (·, Move.vanish)
      if moves.isEmpty then MotionStep.idle else { moves }) ∧
    ({} : FramePairConfig).motion.captions =
      ((List.range ({} : FramePairConfig).keyCount).map ({} : FramePairConfig).keyCaption).toArray ∧
    (states.map (·.n) == [
      #[0, 0, 0, 0, 0], #[0, 0, 0, 0, 0], #[-1, 1, 0, 0, 0], #[-1, 1, 0, 0, 0], #[0, 0, 0, 0, 0],
      #[0, 0, 0, 0, 0], #[1, 0, 0, 0, -1], #[1, 0, 0, 0, -1], #[1, 0, 0, 0, -1], #[1, 0, 0, 0, -1],
      #[0, 0, 0, 0, 0]]) = true ∧
    states.map (·.j) = [0, 1, 0, 0, 1, 0, 4, 0, 0, 4, 0] ∧
    states.map (·.acted) =
      [true, true, true, false, true, true, true, true, false, true, true] ∧
    states.all State.framed = true ∧
    ({} : FramePairConfig).actingSides =
      [(0, 0), (1, 1), (3, 1), (4, 0), (5, 1), (6, 0), (8, 0), (9, 1)] ∧
    ({} : FramePairConfig).pivotsAlternate = true ∧
    ({} : FramePairConfig).marginsVisible (2 / 25) = true ∧
    (({} : FramePairConfig).keyRefs.map fun r => (r.state, r.mark, r.pivot, r.held)) = [
      (0, false, none, false), (0, false, some 0, false), (1, false, some 0, false),
      (1, false, none, false), (1, false, some 1, false), (2, false, some 1, false),
      (2, false, none, false), (3, true, none, false), (3, true, none, true),
      (3, false, none, false), (3, false, some 3, false), (4, false, some 3, false),
      (4, false, none, false), (4, false, some 4, false), (5, false, some 4, false),
      (5, false, none, false), (5, false, some 5, false), (6, false, some 5, false),
      (6, false, none, false), (6, false, some 6, false), (7, false, some 6, false),
      (7, false, none, false), (8, true, none, false), (8, true, none, true),
      (8, false, none, false), (8, false, some 8, false), (9, false, some 8, false),
      (9, false, none, false), (9, false, some 9, false), (10, false, some 9, false),
      (10, false, none, false)] ∧
    ((List.range 31).map ({} : FramePairConfig).keyCaption) = [
      "Start: z = 0, so x = 1/2. Left: the disks halved, with centers 0 and 1, and the point " ++
        "(y + 1)/2. Right: the window about x, the point fixed at x, and the left and right " ++
        "centers P(n) and P(n + eⱼ) with the halved disks riding on them; n is the integer " ++
        "label of the left center, j the index of the direction from the left to the right " ++
        "center (n = (0, 0, 0, 0, 0), j = 0).",
      "Letter 1, a, is next: the point lies in the left disk, so it acts. Arrows show the " ++
        "turn: clockwise about the left center 0 on the left, counterclockwise about the left " ++
        "center in the moving frame. (n = (0, 0, 0, 0, 0), j = 0)",
      "Letter 1, a, acts: the point turns a fifth of a turn clockwise about the left center 0; " ++
        "in the moving frame the right center turns a fifth of a turn counterclockwise about " ++
        "the left center. (n = (0, 0, 0, 0, 0), j = 1)",
      "After letter 1, a: the point has turned a fifth of a turn clockwise about the left " ++
        "center 0, and in the moving frame the right center a fifth of a turn counterclockwise " ++
        "about the left center. (n = (0, 0, 0, 0, 0), j = 1)",
      "Letter 2, b⁻¹, is next: the point lies in the right disk, so it acts. Arrows show the " ++
        "turn: counterclockwise about the right center 1 on the left, clockwise about the " ++
        "right center in the moving frame. (n = (0, 0, 0, 0, 0), j = 1)",
      "Letter 2, b⁻¹, acts: the point turns a fifth of a turn counterclockwise about the right " ++
        "center 1; in the moving frame the left center turns a fifth of a turn clockwise about " ++
        "the right center. (n = (−1, 1, 0, 0, 0), j = 0)",
      "After letter 2, b⁻¹: the point has turned a fifth of a turn counterclockwise about the " ++
        "right center 1, and in the moving frame the left center a fifth of a turn clockwise " ++
        "about the right center. (n = (−1, 1, 0, 0, 0), j = 0)",
      "Letter 3, a, does not act: the point lies outside the left disk, and in the moving " ++
        "frame the left center lies outside the window; a ring marks that center in both " ++
        "panels, and nothing moves. (n = (−1, 1, 0, 0, 0), j = 0)",
      "Letter 3, a, does not act (held): a ring marks the left center in both panels, and " ++
        "nothing moves. (n = (−1, 1, 0, 0, 0), j = 0)",
      "Letter 3, a, did not act: the state is unchanged. (n = (−1, 1, 0, 0, 0), j = 0)",
      "Letter 4, b, is next: the point lies in the right disk, so it acts. Arrows show the " ++
        "turn: clockwise about the right center 1 on the left, counterclockwise about the " ++
        "right center in the moving frame. (n = (−1, 1, 0, 0, 0), j = 0)",
      "Letter 4, b, acts: the point turns a fifth of a turn clockwise about the right center " ++
        "1; in the moving frame the left center turns a fifth of a turn counterclockwise about " ++
        "the right center. (n = (0, 0, 0, 0, 0), j = 1)",
      "After letter 4, b: the point has turned a fifth of a turn clockwise about the right " ++
        "center 1, and in the moving frame the left center a fifth of a turn counterclockwise " ++
        "about the right center. (n = (0, 0, 0, 0, 0), j = 1)",
      "Letter 5, a⁻¹, is next: the point lies in the left disk, so it acts. Arrows show the " ++
        "turn: counterclockwise about the left center 0 on the left, clockwise about the left " ++
        "center in the moving frame. (n = (0, 0, 0, 0, 0), j = 1)",
      "Letter 5, a⁻¹, acts: the point turns a fifth of a turn counterclockwise about the left " ++
        "center 0; in the moving frame the right center turns a fifth of a turn clockwise " ++
        "about the left center. (n = (0, 0, 0, 0, 0), j = 0)",
      "After letter 5, a⁻¹: the point has turned a fifth of a turn counterclockwise about the " ++
        "left center 0, and in the moving frame the right center a fifth of a turn clockwise " ++
        "about the left center. (n = (0, 0, 0, 0, 0), j = 0)",
      "Letter 6, b⁻¹, is next: the point lies in the right disk, so it acts. Arrows show the " ++
        "turn: counterclockwise about the right center 1 on the left, clockwise about the " ++
        "right center in the moving frame. (n = (0, 0, 0, 0, 0), j = 0)",
      "Letter 6, b⁻¹, acts: the point turns a fifth of a turn counterclockwise about the right " ++
        "center 1; in the moving frame the left center turns a fifth of a turn clockwise about " ++
        "the right center. (n = (1, 0, 0, 0, −1), j = 4)",
      "After letter 6, b⁻¹: the point has turned a fifth of a turn counterclockwise about the " ++
        "right center 1, and in the moving frame the left center a fifth of a turn clockwise " ++
        "about the right center. (n = (1, 0, 0, 0, −1), j = 4)",
      "Letter 7, a, is next: the point lies in the left disk, so it acts. Arrows show the " ++
        "turn: clockwise about the left center 0 on the left, counterclockwise about the left " ++
        "center in the moving frame. (n = (1, 0, 0, 0, −1), j = 4)",
      "Letter 7, a, acts: the point turns a fifth of a turn clockwise about the left center 0; " ++
        "in the moving frame the right center turns a fifth of a turn counterclockwise about " ++
        "the left center. (n = (1, 0, 0, 0, −1), j = 0)",
      "After letter 7, a: the point has turned a fifth of a turn clockwise about the left " ++
        "center 0, and in the moving frame the right center a fifth of a turn counterclockwise " ++
        "about the left center. (n = (1, 0, 0, 0, −1), j = 0)",
      "Letter 8, b, does not act: the point lies outside the right disk, and in the moving " ++
        "frame the right center lies outside the window; a ring marks that center in both " ++
        "panels, and nothing moves. (n = (1, 0, 0, 0, −1), j = 0)",
      "Letter 8, b, does not act (held): a ring marks the right center in both panels, and " ++
        "nothing moves. (n = (1, 0, 0, 0, −1), j = 0)",
      "Letter 8, b, did not act: the state is unchanged. (n = (1, 0, 0, 0, −1), j = 0)",
      "Letter 9, a⁻¹, is next: the point lies in the left disk, so it acts. Arrows show the " ++
        "turn: counterclockwise about the left center 0 on the left, clockwise about the left " ++
        "center in the moving frame. (n = (1, 0, 0, 0, −1), j = 0)",
      "Letter 9, a⁻¹, acts: the point turns a fifth of a turn counterclockwise about the left " ++
        "center 0; in the moving frame the right center turns a fifth of a turn clockwise " ++
        "about the left center. (n = (1, 0, 0, 0, −1), j = 4)",
      "After letter 9, a⁻¹: the point has turned a fifth of a turn counterclockwise about the " ++
        "left center 0, and in the moving frame the right center a fifth of a turn clockwise " ++
        "about the left center. (n = (1, 0, 0, 0, −1), j = 4)",
      "Letter 10, b, is next: the point lies in the right disk, so it acts. Arrows show the " ++
        "turn: clockwise about the right center 1 on the left, counterclockwise about the " ++
        "right center in the moving frame. (n = (1, 0, 0, 0, −1), j = 4)",
      "Letter 10, b, acts: the point turns a fifth of a turn clockwise about the right center " ++
        "1; in the moving frame the left center turns a fifth of a turn counterclockwise about " ++
        "the right center. (n = (0, 0, 0, 0, 0), j = 0)",
      "After letter 10, b: the point has turned a fifth of a turn clockwise about the right " ++
        "center 1, and in the moving frame the left center a fifth of a turn counterclockwise " ++
        "about the right center. (n = (0, 0, 0, 0, 0), j = 0)"] ∧
    ({} : FramePairConfig).keyCount = 31 ∧ ({} : FramePairConfig).allArrive = true ∧
    ({} : FramePairConfig).ringsPlaced = true ∧ ({} : FramePairConfig).arrowsPlaced = true ∧
    turnsAreFifths = true ∧
    (({} : FramePairConfig).frameSteps.filterMap (·.leftTurn.map (·.turns))) =
      [-1 / 5, 1 / 5, -1 / 5, 1 / 5, 1 / 5, -1 / 5, 1 / 5, -1 / 5] ∧
    (({} : FramePairConfig).frameSteps.filterMap (·.rightTurn.map (·.turns))) =
      [1 / 5, -1 / 5, 1 / 5, -1 / 5, -1 / 5, 1 / 5, -1 / 5, 1 / 5] := by
  refine ⟨by unfold framePair; with_reducible rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl, rfl, ?_⟩
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

{figref "lens-radius"}[]: the animation `TDCSGFigures.Lens.lensRadius`, whose last key frame is the
lens picture at `R`, with its theorem `TDCSGFigures.Lens.lensRadius_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Lens

open PILean PILean.Plane PILean.Exact TDCSGFigures LensLoopConfig

/-- What `lensRadius` shows, and why. It is the loop of `lensConfig`: two panels on one clock, the
lens pictures `key k` (left) and the neighbourhood of the tip enlarged, `zoomKey k` (right, at its
own scale, drawn from the same setting `setting k` by `zoomItems`), for `k = 0, …, 5`: the radii
`r = 1.8, 2, 2.08, 2.12`, then `R` with the dashed edge `Re v = κ - η` on `Re v = κ`, then the last
key at `R` (`criticalSetting`), the two half-planes one, which is the poster. The steps are made
from `movesOf`: when the radius changes, every actor of both keys morphs through the exact pictures
`between j q` and `zoomBetween j q` at the fractions `q = i/6`, `0 < i < 6`, of the step, which
are the lens pictures at the squared radius `(1 - q) r_j² + q r_{j+1}²` (`r2Between`); between two
consecutive samples the browser interpolates the path data linearly, and that is not stated. What
one key draws and the next does not appears or vanishes. The items of every key are `lensItems` and
`zoomItems` of its setting, written out: the half radius `√(r²/4)`, the tip
`tipOf (h²) = (c₁/2 + √(h² s²), √(s²/4) - √(h² c₁²))` with `h² = r²/4 - 1/4` (`hSqOf`), recording
that it lies on both circles and on the lens and, below `R`, outside both half-planes, at `R` on
both edges; `v*` and the margin `η` at the first key; in the enlarged panel, the margin `η` as a bar
above the box below `R`, and `η = 0` at `R`. The facts hold exactly in `ℚ(√5)`, read off the
coordinates of the tip drawn (`tipOnCircles`, `reAtMost`, written out): at every key and at every
sample (all of whose radii are below `R`) the tip lies on both circles, so on the perpendicular
bisector of `0` and `u`, and its real part is at most `κ - 2η` (`LensLoopConfig.tipOnBoth`); at
every key below `R` it lies left of `κ - η` (`tipFacts`). For every radius, every point of the lens
has real part at most `κ - 2η` (`TDCSG.Five.re_le_of_mem_lens`), which is what the captions say of
the tip below `R`. At `R` the
margin is `0` (`margin` is `η` of `TDCSG.Five.IsGoodLevel`), `h² = s²` and `c₁/2 + s² = κ`, so the
tip is `v*`, which lies on both circles of radius `R/2` with real part `κ`; the disk `|v| ≤ r/2`
lies left of `κ - η` at `1.8`, `2` and `2.08` and crosses it at `2.12` (`diskLeftOfCut`). The
captions are stated as a function of the data (`LensLoopConfig.caption`), their words pinned by
`#guard` in `TDCSGTests.Motions`. Not stated: how the builders draw, the layout, the scale of each
panel, the timing and the frames the browser draws between the samples. -/
theorem lensRadius_spec :
    lensRadius = lensConfig.motion ∧
    lensConfig.radii = #[(9 / 5, "1.8"), (2, "2"), (52 / 25, "2.08"), (53 / 25, "2.12")] ∧
    lensConfig.samples = 6 ∧ lensConfig.keyCount = 6 ∧
    (∀ cfg : LensLoopConfig, cfg.motion.panels = #[
      { title := "The lens", motion :=
        { keys := ((List.range cfg.keyCount).map cfg.key).toArray,
          steps := ((List.range (cfg.keyCount - 1)).map fun j =>
            ({ moves := cfg.movesOf cfg.key j } : MotionStep)).toArray,
          between := cfg.between, morphSamples := cfg.samples } },
      { title := "Near the tip", motion :=
        { keys := ((List.range cfg.keyCount).map cfg.zoomKey).toArray,
          steps := ((List.range (cfg.keyCount - 1)).map fun j =>
            ({ moves := cfg.movesOf cfg.zoomKey j } : MotionStep)).toArray,
          between := cfg.zoomBetween, morphSamples := cfg.samples } }]) ∧
    (∀ cfg : LensLoopConfig, cfg.motion.captions =
      ((List.range cfg.keyCount).map cfg.caption).toArray) ∧
    (∀ cfg : LensLoopConfig, cfg.motion.poster = cfg.keyCount - 1) ∧
    (∀ cfg : LensLoopConfig, cfg.motion.scale = .independent) ∧
    (∀ cfg : LensLoopConfig, cfg.motion.checks = .fail) ∧
    (∀ (r2 : QSqrt5), hSqOf r2 = (
r2 * rat (1 / 4) - rat (1 / 4)
    : QSqrt5)) ∧
    (∀ (h2 : QSqrt5), tipOf h2 = (
  ⟨{ base := cosine * rat (1 / 2), roots := [(1, h2 * sineSq)] },
    { roots := [(1, sineSq * rat (1 / 4)), (-1, h2 * (cosine * cosine))] }⟩
    : SurdPoint)) ∧
    (∀ (p : SurdPoint) (cuts : Option Plane.Incidence), tipItemWith p cuts = (
  let it := Plane.Exact.point p |>.size 5
    |>.named "the tip of the lens: its corner of largest real part"
    |>.incident .on "the circle |v| = r/2" |>.incident .on "the circle |v − u| = r/2"
    |>.incident .on "the lens"
  match cuts with
  | some i => it |>.incident i "the half-plane Re v ≥ κ − η" |>.incident i "the half-plane Re v ≥ κ"
  | none => it
    : Item)) ∧
    (∀ (r2 : QSqrt5) (rText : String) (first : Bool) (cuts : Plane.Incidence)
      (radiusRow : Nat), loopSetting r2 rText first cuts radiusRow = (
  { half := ⟨r2 * rat (1 / 4)⟩, r2, rText,
    tipPt := tipItemWith (tipOf (hSqOf r2)) (some cuts) |>.named tipTitle,
    tipXY := PlanePoint.toPoint (tipOf (hSqOf r2)), other := otherSide (r2 * rat (1 / 4)),
    critical := false, showVStar := first, showMargin := first, motion := true, radiusRow }
    : Setting (SqrtOf QSqrt5))) ∧
    (criticalSetting = (
  { loopSetting criticalSq "R = √(3 + φ)" false .on with
    critical := true,
    tipPt := tipItemWith (tipOf (hSqOf criticalSq)) none
      |>.incident .on "the half-plane Re v ≥ κ" |>.named tipTitle }
    : Setting (SqrtOf QSqrt5))) ∧
    (∀ {β : Type} (st : Setting β) (id : String) (it : Item), st.act id it = (
  if st.motion then it.actor id else it
    : Item)) ∧
    (∀ {β : Type} (st : Setting β), st.atR = (
  if st.motion then "" else s!", r = {st.rText}"
    : String)) ∧
    (∀ {β : Type} [RealValue β] (st : Setting β), lensItems st = (
  let kc := cut st.r2
  let foot : QSqrt5 × QSqrt5 := (cosine, ⟨0, 0⟩)
  (if st.critical then #[] else #[
    Plane.Exact.polygon (halfPlane kc) |>.faint |>.filled |>.width 1 |>.dashed
      |>.fillOpacity 0.16 |>.named "the half-plane Re v ≥ κ − η"
      |>.describedBy (if st.motion then "where the lens estimate puts no point of the lens"
        else s!"where the lens estimate puts no point of the lens, at r = {st.rText}")
      |>.declRef `TDCSG.Five.div_two_lt_norm_sub_of_le_re |> st.act "cut"]) ++ #[
    Plane.Exact.polygon (halfPlane kappa) |>.faint |>.filled |>.width 1 |>.fillOpacity 0.18
      |>.named "the half-plane Re v ≥ κ"
      |>.describedBy "κ = (2φ + 1)/4 = (1 + L)/2, L = φ − 1/2",
    (if st.motion then
      Plane.Exact.segment ((rat (-23 / 20), rat 0) : QSqrt5 × QSqrt5) (xRight, rat 0) |>.faint
        |>.width 1 |>.named "the real axis"
    else Plane.Exact.line origin rightCentre |>.faint |>.width 1 |>.named "the real axis"),
    Plane.Exact.disk origin st.half |>.noFill |>.role windowRole
      |>.named "the circle |v| = r/2" |>.describedBy s!"the closed disk |v| ≤ r/2{st.atR}"
      |> st.act "disk-0",
    Plane.Exact.disk (zeta 1) st.half |>.noFill |>.role windowRole |>.dashed
      |>.named "the circle |v − u| = r/2"
      |>.describedBy s!"the closed disk |v − u| ≤ r/2 about u = ζ{st.atR}" |> st.act "disk-u",
    Plane.Exact.lens origin (zeta 1) st.half st.half |>.role lensRole |>.noOutline
      |>.fillOpacity 0.12 |>.named "the lens" |> st.act "lens",
    Plane.Exact.segment uSurd ⟨Surd.ofQ cosine, Surd.ofQ ⟨0, 0⟩⟩ |>.faint |>.width 1
      |>.dashed #[2, 3] |>.named "the foot of u on the real axis"] ++
  (if st.showMargin then #[
    Plane.Exact.segment (kc, marginY) (kappa, marginY) |>.width 1
      |>.named "the margin η = (3 + φ − r²)/16 between the cuts κ − η and κ"
      |>.declRef `TDCSG.Five.IsGoodLevel |> st.act "margin",
    Plane.Exact.tickAt (kc, marginY) (kc, marginY) (kappa, marginY) |> st.act "margin-tick-cut",
    Plane.Exact.tickAt (kappa, marginY) (kc, marginY) (kappa, marginY)
      |> st.act "margin-tick-kappa"] ++
    (if st.motion then #[] else #[Plane.Exact.labelBeside "η" (kc, marginY) (kappa, marginY)])
    else #[]) ++ #[
    Plane.segment ⟨0, 0⟩ (radiusEnd (RealValue.toFloat st.half)) |>.role windowRole |>.width 1.5
      |>.dashed |>.named "a radius r/2 of the disk |v| ≤ r/2" |> st.act "radius",
    Plane.labelBeside "r/2" ⟨0, 0⟩ (radiusEnd (RealValue.toFloat st.half)) |>.role windowRole
      |> st.act "radius-label",
    Plane.Exact.point origin |>.role windowRole |>.named "0, the center of |v| ≤ r/2"
      |> (if st.motion then (·.incident .on "the real axis") else id)
      |>.incident .inside "the circle |v| = r/2"
      |>.incident st.other.incidence "the circle |v − u| = r/2"
      |>.incident (Side.lens .inside st.other).incidence "the lens",
    Plane.Exact.point (zeta 1) |>.role windowRole |>.named "u = ζ, the center of |v − u| ≤ r/2"
      |>.incident .inside "the circle |v − u| = r/2"
      |>.incident st.other.incidence "the circle |v| = r/2"
      |>.incident (Side.lens .inside st.other).incidence "the lens",
    Plane.Exact.point foot |>.faint |>.size 3
      |>.named "c₁ = Re u = (φ − 1)/2 on the real axis" |>.incident .on "the real axis",
    st.act "tip" st.tipPt] ++
  (if st.showVStar then #[
    Plane.Exact.point vStar |>.named "v∗ = 1 + t u, t = 1/2 − c₁, at distance R/2 from 0 and u"
      |>.incident .outside "the circle |v| = r/2" |>.incident .outside "the circle |v − u| = r/2"
      |>.incident .outside "the lens" |>.incident .on "the half-plane Re v ≥ κ"
      |>.incident .inside "the half-plane Re v ≥ κ − η" |> st.act "vstar",
    Plane.Exact.label "v∗" vStar .auto |> st.act "vstar-label"] else #[]) ++ #[
    (if st.motion then Plane.Exact.label "0" origin .below (some 12)
      else Plane.Exact.label "0" origin .auto) |>.role windowRole |> st.act "label-0",
    (if st.motion then Plane.Exact.label "u = ζ" (zeta 1) .aboveRight (some 8)
      else Plane.Exact.label "u = ζ" (zeta 1) .auto) |>.role windowRole |> st.act "label-u",
    (if st.motion then Plane.Exact.label "c₁" foot .below (some 16)
      else Plane.Exact.label "c₁" foot .auto) |> st.act "label-c1",
    Plane.label (if st.critical then "tip = v∗" else "tip") st.tipXY .auto
      |> st.act (if st.critical then "tip-label-critical" else "tip-label"),
    Plane.Exact.label "lens" ((rat (1 / 10), rat (11 / 20)) : QSqrt5 × QSqrt5) |>.role lensRole,
    Plane.Exact.label "|v| ≤ r/2" ((rat (3 / 10), rat (-11 / 20)) : QSqrt5 × QSqrt5)
      |>.role windowRole,
    Plane.Exact.label "|v − u| ≤ r/2" ((rat (9 / 20), rat (3 / 2)) : QSqrt5 × QSqrt5)
      |>.role windowRole,
    Plane.Exact.label (if st.critical && !st.motion then "Re v ≥ κ, η = 0" else "Re v ≥ κ")
      ((kappa, cutLabelY) : QSqrt5 × QSqrt5) .right |> st.act "kappa-label"] ++
  (if st.critical then #[] else #[
    Plane.Exact.label "Re v ≥ κ − η →" ((kc, cutLabelY) : QSqrt5 × QSqrt5) .left
      |> st.act "cut-label"]) ++
  (if st.motion then #[
    Plane.Exact.label s!"r = {st.rText}"
      ((rat (-11 / 10), rat (9 / 4) - rat (st.radiusRow / 5)) : QSqrt5 × QSqrt5)
      .right |>.bold |> st.act s!"r-{st.rText}"] else #[])
    : Array Item)) ∧
    (∀ (st : Setting (SqrtOf QSqrt5)), zoomTip st = (
  let it := Plane.Exact.point (tipOf (hSqOf st.r2)) |>.size 5
    |>.incident .on "the circle |v| = r/2" |>.incident .on "the circle |v − u| = r/2"
  let it := if st.critical then it.incident .on "the half-plane Re v ≥ κ"
    else
      let i := if st.r2 == criticalSq then Plane.Incidence.on else .outside
      it.incident i "the half-plane Re v ≥ κ − η" |>.incident i "the half-plane Re v ≥ κ"
  it.named tipTitle |>.actor "tip"
    : Item)) ∧
    (∀ (st : Setting (SqrtOf QSqrt5)), zoomMargin st = (
  let kc := cut st.r2
  if st.r2 == criticalSq then #[
    Plane.Exact.label "η = 0" ((kappa, zoomBarY) : QSqrt5 × QSqrt5) .above (some 26)
      |>.actor "zoom-eta-zero"]
  else #[
    Plane.Exact.segment (kc, zoomBarY) (kappa, zoomBarY) |>.width 1
      |>.named "the margin η between the edges" |>.actor "zoom-margin",
    Plane.Exact.tickAt (kc, zoomBarY) (kc, zoomBarY) (kappa, zoomBarY) |>.actor "zoom-tick-cut",
    Plane.Exact.tickAt (kappa, zoomBarY) (kc, zoomBarY) (kappa, zoomBarY)
      |>.actor "zoom-tick-kappa",
    Plane.Exact.labelBeside "η" (kc, zoomBarY) (kappa, zoomBarY) |>.actor "zoom-eta"]
    : Array Item)) ∧
    (∀ (st : Setting (SqrtOf QSqrt5)), zoomItems st = (
  let kc := cut st.r2
  let a0 := angleFrom ⟨0, 0⟩ st.tipXY
  let au := angleFrom (PlanePoint.toPoint (zeta 1)) st.tipXY
  #[Plane.Exact.polygon (zoomHalfPlane kappa) |>.faint |>.filled |>.width 1 |>.fillOpacity 0.18
      |>.named "the half-plane Re v ≥ κ"] ++
  (if st.critical then #[] else #[
    Plane.Exact.polygon (zoomHalfPlane kc) |>.faint |>.filled |>.width 1 |>.dashed
      |>.fillOpacity 0.16 |>.named "the half-plane Re v ≥ κ − η" |>.actor "cut"]) ++ #[
    Plane.Exact.arc origin st.half (a0 - zoomArc) (a0 + zoomArc) |>.role windowRole
      |>.named "the circle |v| = r/2" |>.actor "disk-0",
    Plane.Exact.arc (zeta 1) st.half (au - zoomArc) (au + zoomArc) |>.role windowRole |>.dashed
      |>.named "the circle |v − u| = r/2" |>.actor "disk-u",
    zoomTip st,
    Plane.Exact.label "κ" ((kappa, zoomBottom) : QSqrt5 × QSqrt5) .belowRight
      |>.actor "kappa-label"] ++
  (if st.r2 == criticalSq then #[] else #[
    Plane.Exact.label "κ − η" ((kc, zoomBottom) : QSqrt5 × QSqrt5) .belowLeft
      |>.actor "cut-label"]) ++
  zoomMargin st
    : Array Item)) ∧
    (∀ (a : QSqrt5), zoomHalfPlane a = (
  [(a, zoomBottom), (zoomRight, zoomBottom), (zoomRight, zoomTop), (a, zoomTop)]
    : List (QSqrt5 × QSqrt5))) ∧
    (∀ (cfg : LensLoopConfig) (k : Nat), cfg.r2At k = (
  match cfg.radii[k]? with
  | some (r, _) => rat (r * r)
  | none => criticalSq
    : QSqrt5)) ∧
    (∀ (cfg : LensLoopConfig) (k : Nat), cfg.setting k = (
  match cfg.radii[k]? with
  | some (_, t) => loopSetting (cfg.r2At k) t (k == 0) .outside (k % 2)
  | none =>
    if k == cfg.radii.size then loopSetting criticalSq "R = √(3 + φ)" false .on (k % 2)
    else { criticalSetting with radiusRow := (k - 1) % 2 }
    : Setting (SqrtOf QSqrt5))) ∧
    (∀ (cfg : LensLoopConfig) (k : Nat), cfg.key k = (
  { lensFigure (cfg.setting k) false with view := none, width := mainWidth }
    : Plane.Figure)) ∧
    (∀ (cfg : LensLoopConfig) (k : Nat), cfg.zoomKey k = (
  { cfg.key k with items := zoomItems (cfg.setting k), width := zoomWidth }
    : Plane.Figure)) ∧
    (∀ (cfg : LensLoopConfig) (keyAt : Nat → Plane.Figure) (j : Nat), cfg.movesOf keyAt j = (
  let a := actorIds (keyAt j)
  let b := actorIds (keyAt (j + 1))
  (if cfg.grows j then (a.filter b.contains).map (·, Move.morph) else #[]) ++
    (a.filter (!b.contains ·)).map (·, Move.vanish) ++
    (b.filter (!a.contains ·)).map (·, Move.appear)
    : Array (String × Move))) ∧
    (∀ (cfg : LensLoopConfig) (j : Nat) (q : Rat), cfg.r2Between j q = (
cfg.r2At j * rat (1 - q) + cfg.r2At (j + 1) * rat q
    : QSqrt5)) ∧
    (∀ (cfg : LensLoopConfig) (j : Nat) (q : Rat), cfg.between j q = (
  if cfg.grows j then
    some { cfg.key j with items := lensItems (loopSetting (cfg.r2Between j q) "" false) }
  else none
    : Option Plane.Figure)) ∧
    (∀ (cfg : LensLoopConfig) (j : Nat) (q : Rat), cfg.zoomBetween j q = (
  if cfg.grows j then
    some { cfg.zoomKey j with items := zoomItems (loopSetting (cfg.r2Between j q) "" false) }
  else none
    : Option Plane.Figure)) ∧
    (∀ (cfg : LensLoopConfig) (k : Nat), cfg.caption k = (
  match cfg.radii[k]? with
  | some (r, t) =>
    let disk := if diskLeftOfCut r then " The circle |v| = r/2 lies left of the dashed edge: no \
        v meets the hypothesis of the lemma."
      else " The circle |v| = r/2 crosses the dashed edge, and the lens does not."
    if k == 0 then
      s!"The lens of the closed disks |v| ≤ r/2 and |v − u| ≤ r/2 at r = {t}, with the \
        half-planes Re v ≥ κ − η (dashed edge) and Re v ≥ κ, η = (3 + φ − r²)/16, and v∗ on \
        Re v = κ. The second panel shows the tip enlarged, and above it the margin η between \
        the edges as a bar. The tip lies left of the dashed edge, at least η from it." ++ disk
    else
      s!"r = {t}: the margin η is smaller, and the tip has moved right; it stays at least η \
        left of the dashed edge." ++ disk
  | none =>
    if k == cfg.radii.size then
      "r = R = √(3 + φ): η = 0, so the dashed edge has reached Re v = κ, and so has the tip: \
        the tip is v∗."
    else
      "At R the two half-planes are one, Re v ≥ κ, and the tip of the lens is v∗, on its \
        edge. Below R it stays at least η left of the dashed edge."
    : String)) ∧
    (∀ (p : SurdPoint) (ρ2 : QSqrt5), tipOnCircles p ρ2 = (
  match p.re, p.im with
  | ⟨b, [(sa, A)]⟩, ⟨y0, [(sb, B), (sc, C)]⟩ =>
    sa == 1 && sb == 1 && sc == -1 && y0 == ⟨0, 0⟩ && b == cosine * rat (1 / 2) &&
      B == sineSq * rat (1 / 4) && QSqrt.lt ⟨0, 0⟩ cosine && QSqrt.le ⟨0, 0⟩ A &&
      QSqrt.le ⟨0, 0⟩ C && cosine * cosine * A == sineSq * C &&
      cosine * cosine * rat (1 / 4) + A + B + C == ρ2
  | _, _ => false
    : Bool)) ∧
    (∀ (p : SurdPoint) (K : QSqrt5) (strict : Bool), reAtMost p K strict = (
  match p.re with
  | ⟨b, [(1, A)]⟩ => sqrtLt A (K - b) || (!strict && sqrtEq A (K - b))
  | _ => false
    : Bool)) ∧
    (∀ (r2 : QSqrt5), LensLoopConfig.tipOnBoth r2 = (
  tipOnCircles (tipOf (hSqOf r2)) (r2 * rat (1 / 4)) &&
    reAtMost (tipOf (hSqOf r2)) (kappa - margin r2 * rat 2)
    : Bool)) ∧
    (∀ (cfg : LensLoopConfig), cfg.samplesBelowR = (
  (List.range cfg.radii.size).all fun j => (List.range (cfg.samples - 1)).all fun i =>
    let r2 := cfg.r2Between j ((i + 1 : Nat) / (cfg.samples : Rat))
    QSqrt.lt r2 criticalSq && tipOnBoth r2
    : Bool)) ∧
    (∀ {β : Type} [RealValue β] (st : Setting β) (narrow : Bool), lensFigure st narrow = (
  { width := figureWidth
    narrowWidth := if narrow then some narrowWidth else none
    view := some view
    padding := 1
    style := partTwoStyle
    checks := .fail
    items := lensItems st
    info := { title :=
      s!"The lens at r = {st.rText} and the half-planes Re v ≥ κ − η and Re v ≥ κ" } }
    : Plane.Figure)) ∧
    zoomRight = rat (109 / 100) ∧ zoomBottom = rat (2 / 25) ∧ zoomTop = rat (8 / 25) ∧
    zoomBarY = rat (17 / 50) ∧
    lensConfig.samplesBelowR = true ∧
    ((List.range 4).all fun k => QSqrt.lt (lensConfig.r2At k) criticalSq) = true ∧
    (lensConfig.radii.all fun (r, _) =>
      tipFacts (r / 2) && tipReLe (r / 2) && LensLoopConfig.tipOnBoth (rat (r * r))) = true ∧
    LensLoopConfig.tipOnBoth criticalSq = true ∧
    (margin criticalSq == rat 0) = true ∧ (hSqOf criticalSq == sineSq) = true ∧
    (cosine * rat (1 / 2) + sineSq == kappa) = true ∧
    (vStar.normSq == criticalSq * rat (1 / 4)) = true ∧
    ((vStar - ZetaFrac.ofZeta (zeta 1)).normSq == criticalSq * rat (1 / 4)) = true ∧
    (vStar.realPart == kappa) = true ∧
    (lensConfig.radii.map fun (r, _) => LensLoopConfig.diskLeftOfCut r) =
      #[true, true, true, false] :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl, rfl, fun _ _ _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

figure_links lensRadius lensRadius_spec

end TDCSGFigures.Lens
```

# The figures of chapter 6

%%%
tag := "theorems-levels"
file := "Theorems-levels"
%%%

{figref "terminal-crossing"}[]: the animation `TDCSGFigures.Levels.terminalCrossing`, whose last
key frame is the figure of the crossing, with its theorem
`TDCSGFigures.Levels.terminalCrossing_spec`; the other key frames, the walk and the moves are stated
in `TDCSGFigures.Levels.terminalCrossing_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Levels

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- The animation `terminalCrossing` and the figure of the crossing, the last key frame of its
upper panel. The animation has two panels on one clock, `crossMotion` (the crossing) above
`zoomMotion` (the leaf enlarged); its poster, the still shown under reduced motion and in print, is
the last key, and its checks are strict. Key `5` of the crossing is `terminalCrossingFinal`, the
figure of the crossing, whose items are written out in drawing order, each with its id: the data
are `r = 53/25`, `x = 59/125`, `n = (4, -3, 1, 1, -3)` and the leaf `n + e₀`; those of the four
neighbours `n + eₖ` and the four candidates `n + e₀ - eₖ` (`k = 1, …, 4`) are made by the builders
`neighbourEdge`, `rejectedStep`, `neighbourPoint`, `neighbourLabel` (placed by `neighbourPlace`),
`candidatePoint` and `candidateLabel`, whose definitions are stated. The records hold exactly: `n`
has weight zero and its level `n₀ = 4` is good at `r = 2.12`, `x = 0.472`; `n`, the leaf and every
`n + eₖ` lie inside the window and every `n + e₀ - eₖ` outside it (`windowSide`, from
`|q P(m) - p|² ≤ q² r²/4` for `x = p/q`), so the leaf has no neighbour but `n`; the leaf's real part
`8 - 4φ` exceeds the cut `Re x + κ - η`, and `P(n) = 7 - 4φ` is real. Not stated: how the builders
and modifiers draw, the layout, the lettering, the style's colour values and the pixels. -/
theorem terminalCrossing_spec :
    terminalCrossing.panels = #[{ title := "The crossing", motion := crossMotion },
      { title := "Near the leaf, enlarged", motion := zoomMotion }] ∧
    terminalCrossing.poster = 5 ∧ terminalCrossing.checks = .fail ∧
    crossMotion.keys = ((List.range 6).map crossKey).toArray ∧
    crossKey 5 = terminalCrossingFinal ∧
    crossN = #[4, -3, 1, 1, -3] ∧ leaf = shift crossN 0 1 ∧ crossX = 59 / 125 ∧
    crossRadius = 53 / 25 ∧ crossCut = rat crossX + kappa - margin crossRadiusSq ∧
    (∀ k, neighbourEdge k = (Plane.Exact.segment (proj crossN) (proj (shift crossN k 1))
      |>.role "right" |>.width 1.5 |>.named s!"the edge from n to n + e{sub k}"
      |>.withId s!"nedge-{k}")) ∧
    (∀ k, rejectedStep k = (Plane.Exact.segment (proj leaf) (proj (shift leaf k (-1)))
      |>.faint |>.width 1.5 |>.dashed
      |>.named s!"the rejected step from n + e₀ to n + e₀ − e{sub k}" |>.withId s!"reject-{k}")) ∧
    (∀ k, neighbourPoint k = (Plane.Exact.point (proj (shift crossN k 1)) |>.role "right"
      |>.marker .square
      |>.named s!"n + e{sub k} = {labelText (shift crossN k 1)}, weight 1, a neighbour of n"
      |>.incident (windowSide (shift crossN k 1)).incidence "the window"
      |>.withId s!"neighbour-{k}")) ∧
    (∀ k, neighbourPlace k =
      #[(.left, 10), (.right, 17), (.above, 15), (.left, 10)].getD (k - 1) (.above, 10)) ∧
    (∀ k, neighbourLabel k =
      (Plane.Exact.label s!"n + e{sub k}" (proj (shift crossN k 1)) (neighbourPlace k).1
        (some (neighbourPlace k).2) |>.role "right" |>.withId s!"neighbour-label-{k}")) ∧
    (∀ k, candidatePoint k = (Plane.Exact.point (proj (shift leaf k (-1))) |>.faint
      |>.marker .ring
      |>.named s!"n + e₀ − e{sub k} = {labelText (shift leaf k (-1))}, weight 0"
      |>.incident (windowSide (shift leaf k (-1))).incidence "the window"
      |>.withId s!"candidate-{k}")) ∧
    (∀ k p, candidateLabel k p =
      (Plane.Exact.label s!"n + e₀ − e{sub k}" (proj (shift leaf k (-1))) p
        |>.withId s!"candidate-label-{k}")) ∧
    terminalCrossingFinal.items = #[
      Plane.Exact.polygon crossHalfPlane |>.faint |>.filled |>.noOutline |>.fillOpacity 0.16
        |>.named "the half-plane Re w ≥ Re x + κ − η"
        |>.describedBy "beyond the cut of the lens estimate, turned to the direction j = 0"
        |>.declRef `TDCSG.Five.div_two_lt_norm_sub_of_le_re |>.withId "half-plane",
      Plane.Exact.disk crossXPoint (53 / 50 : Rat) |>.role "window" |>.fillOpacity 0.07
        |>.named "the window" |>.describedBy "the closed disk |w − x| ≤ r/2, r = 2.12, x = 0.472"
        |>.declRef `TDCSG.Five.InWindow |>.withId "window",
      Plane.Exact.segment crossXPoint crossRim |>.role "window" |>.width 1.5 |>.dashed
        |>.named "a radius r/2 = 1.06 of the window" |>.withId "radius",
      Plane.Exact.labelBeside "r/2" crossXPoint crossRim |>.role "window" |>.withId "radius-label",
      neighbourEdge 1, neighbourEdge 2, neighbourEdge 3, neighbourEdge 4,
      rejectedStep 1, rejectedStep 2, rejectedStep 3, rejectedStep 4,
      Plane.Exact.segment (proj crossN) (proj leaf) |>.width 3.5
        |>.named "the edge from n to n + e₀: it raises n₀ from the good level 4 to 5"
        |>.declRef `TDCSG.Five.IsGoodLevel.leaf |>.withId "edge",
      Plane.Exact.polygon zoomBox |>.width 1
        |>.named "a square about the leaf; the next figure and the lower panel enlarge its centre"
        |>.withId "zoom-box",
      neighbourPoint 1, neighbourLabel 1, neighbourPoint 2, neighbourLabel 2,
      neighbourPoint 3, neighbourLabel 3, neighbourPoint 4, neighbourLabel 4,
      candidatePoint 1, candidateLabel 1 .belowLeft, candidatePoint 2, candidateLabel 2 .below,
      candidatePoint 3, candidateLabel 3 .above, candidatePoint 4, candidateLabel 4 .aboveLeft,
      Plane.Exact.point (proj crossN) |>.role "left" |>.size 5
        |>.named s!"n = {labelText crossN}, weight 0, P(n) = 7 − 4φ, at the good level n₀ = 4"
        |>.incident (windowSide crossN).incidence "the window" |>.withId "n",
      Plane.Exact.point (proj leaf) |>.role "right" |>.marker .square |>.size 5
        |>.named s!"the leaf n + e₀ = {labelText leaf}, weight 1, P = 8 − 4φ"
        |>.incident (windowSide leaf).incidence "the window"
        |>.incident .inside "the half-plane Re w ≥ Re x + κ − η" |>.withId "leaf",
      Plane.Exact.label "n" (proj crossN) (.toward (Plane.deg 100)) (some 10) |>.role "left"
        |>.italic |>.withId "name-n",
      Plane.Exact.label "n₀ = 4 → 5" ((rat (21 / 20), rat (2 / 25)) : QSqrt5 × QSqrt5)
        |>.withId "level-label",
      Plane.Exact.label "window" ((rat 0, rat (6 / 5)) : QSqrt5 × QSqrt5)
        |>.role "window" |>.withId "window-label",
      Plane.Exact.label "Re w ≥ Re x + κ − η" ((crossCut, rat (5 / 4)) : QSqrt5 × QSqrt5) .right
        |>.size 12 |>.withId "cut-label"] ∧
    weight crossN = 0 ∧ isGoodLevel crossRadiusSq crossX 0 4 = some true ∧
    (windowSide crossN == .inside && windowSide leaf == .inside) = true ∧
    [1, 2, 3, 4].all (fun k => windowSide (shift crossN k 1) == .inside) = true ∧
    [1, 2, 3, 4].all (fun k => windowSide (shift leaf k (-1)) == .outside) = true ∧
    QSqrt.lt crossCut (proj leaf).realPart = true ∧
    ((proj crossN).realPart == ⟨5, -2⟩ && (proj crossN).conj == proj crossN &&
      (proj leaf).realPart == ⟨6, -2⟩) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

figure_links terminalCrossing terminalCrossing_spec

/-- The key frames of `terminalCrossing` before the last, its walk and its moves, written out. Key
`k < 5` of the crossing draws the items of `terminalCrossingFinal` that `crossShows k` keeps (the
rejected steps, the candidates and their names from key `3`, never the words `n₀ = 4 → 5`, which
appear at the last step), with the name `n` as `earlyName`, clear of the circle, and a
circle about each point of `walkAt k`: `P(n)`, the point `(1.512, 0)` of the edge (`boxEntry`), the
leaf, the leaf, `P(n)`. Key `k < 5` of the enlarged panel draws the items of `terminalZoom` with
the ids `zoomIds`, the leaf's name as `zoomEarlyName`, and a circle about each point of
`zoomWalkAt k`: none, `(1.512, 0)`, the leaf, the leaf, none; key `5` is `zoomFinal`. The circle is
drawn at the points the exact arrival check reads (`walkerItems`, `crossActors`, `zoomActors`).
The declared moves are written out; each slide, applied exactly to the circle's centre in one key,
gives its centre in the next, in `ℚ(ζ₅)` for the crossing and in `ℚ(√5)²` for the enlarged panel
(`crossArrives`, `zoomArrives`), and the other actors come and go only by a declared appearance or
disappearance. The point `boxEntry` drawn and slid to is real and lies on the edge, between
`P(n) = 7 - 4φ` and the leaf `8 - 4φ`, both real; the circle about it and the circle about the leaf
lie inside the region the enlarged panel shows, `zoomView`, made from `enlargedLeft`,
`enlargedRight` and `enlargedHalf`, and that region lies inside the square `zoomBox` about the leaf
drawn in the crossing; the enlarged panel draws the point and the leaf at the same real parts. The
captions are written out. Not stated: how the builders draw, the layout, the timing and the frames
the browser draws between the key frames. -/
theorem terminalCrossing_keys :
    crossCaptions = #[
      "A crossing at a good level, at r = 2.12, x = 0.472: the label n = (4, −3, 1, 1, −3) has \
        weight zero and its coordinate n₀ = 4 is a good level. The circle starts at n; the thick \
        edge leads to n + e₀ and raises n₀ to 5.",
      "The walk follows the thick edge into the small square about the leaf, whose centre the \
        lower panel shows enlarged.",
      "It reaches the leaf n + e₀: enlarged, the step ends between 0.0045 and 0.0046 beyond the \
        cut Re w = Re x + κ − η and between 0.0041 and 0.0042 inside the window's edge, both less \
        than a pixel in the upper panel.",
      "By the lens estimate the four other candidates n + e₀ − eₖ of the leaf lie outside the \
        window (open rings at the ends of dashed spokes): n + e₀ has no neighbor but n.",
      "So the only step from the leaf leads back along the same edge to n, at level 4.",
      "The crossing: n with its four neighbors n + eₖ inside the window, the thick edge to the \
        leaf n + e₀ in the shaded half-plane, and the leaf's four candidates outside the window. \
        Below, the neighborhood of the leaf enlarged, with a scale bar of length 0.005."] ∧
    terminalCrossing.captions = crossCaptions ∧
    crossMotion.steps = ((List.range 5).map (exactStep ∘ crossMoves)).toArray ∧
    zoomMotion.keys = ((List.range 6).map zoomKey).toArray ∧
    zoomMotion.steps = ((List.range 5).map (exactStep ∘ zoomMoves)).toArray ∧
    (∀ k, crossKey k = if k < 5 then { terminalCrossingFinal with items := crossKeyItems k }
      else terminalCrossingFinal) ∧
    (∀ k, crossKeyItems k =
      (terminalCrossingFinal.items.filter fun it => crossShows k (it.actorId?.getD "")).map
        (fun it => if it.actorId? == some "name-n" then earlyName else it) ++
      walkerItems walkerRadius (walkAt k)) ∧
    (∀ k id, crossShows k id = (if id.startsWith "reject-" || id.startsWith "candidate-" then
      decide (3 ≤ k) else id != "level-label")) ∧
    earlyName = (Plane.Exact.label "n" (proj crossN) (.toward (Plane.deg 168)) (some 16)
      |>.role "left" |>.italic |>.withId "name-n-early") ∧
    (∀ {α : Type} [PlanePoint α] (ρ : Rat) (ps : List α), walkerItems ρ ps =
      (ps.map fun c => Plane.Exact.circle c ρ |>.width 2 |>.role "left"
        |>.named "a circle about the point the walk has reached" |>.withId "walker").toArray) ∧
    walkerRadius = 1 / 16 ∧ zoomWalkerRadius = 1 / 1800 ∧
    nZ = ZetaFrac.ofZeta (proj crossN) ∧ leafZ = ZetaFrac.ofZeta (proj leaf) ∧
    boxEntry = ⟨Zeta5.ofInt 1512, 1000⟩ ∧ boxEntryQ = (boxEntry.realPart, rat 0) ∧
    leafQ = ((proj leaf).realPart, rat 0) ∧
    (List.range 6).map walkAt = [[nZ], [boxEntry], [leafZ], [leafZ], [nZ], []] ∧
    (List.range 6).map zoomWalkAt = [[], [boxEntryQ], [leafQ], [leafQ], [], []] ∧
    zoomIds = #["half-plane", "window-arc", "edge", "scale", "leaf", "leaf-label", "scale-label",
      "edge-label", "cut-name", "cut-label", "window-edge-label"] ∧
    zoomFinal = { terminalZoom with
      items := terminalZoom.items.mapIdx fun i it => it.withId (zoomIds.getD i "") } ∧
    zoomEarlyName = (Plane.Exact.label "n + e₀ (leaf)" leafQ .below (some 14) |>.size 12
      |>.role "right" |>.withId "leaf-label-early") ∧
    (∀ k, zoomKey k = if k < 5 then { zoomFinal with items := zoomKeyItems k } else zoomFinal) ∧
    (∀ k, zoomKeyItems k = zoomFinal.items.map (fun it =>
        if it.actorId? == some "leaf-label" then zoomEarlyName else it) ++
      walkerItems zoomWalkerRadius (zoomWalkAt k)) ∧
    (∀ p q, zetaFracSub p q = ZetaFrac.add p ⟨-q.num, q.den⟩) ∧
    crossMoves 0 = [("walker", .slide (zetaFracSub boxEntry nZ))] ∧
    crossMoves 1 = [("walker", .slide (zetaFracSub leafZ boxEntry))] ∧
    moveKinds (crossMoves 2) = [("reject-1", "appear"), ("reject-2", "appear"),
      ("reject-3", "appear"), ("reject-4", "appear"), ("candidate-1", "appear"),
      ("candidate-label-1", "appear"), ("candidate-2", "appear"), ("candidate-label-2", "appear"),
      ("candidate-3", "appear"), ("candidate-label-3", "appear"), ("candidate-4", "appear"),
      ("candidate-label-4", "appear")] ∧
    crossMoves 3 = [("walker", .slide (zetaFracSub nZ leafZ))] ∧
    moveKinds (crossMoves 4) = [("walker", "vanish"), ("name-n-early", "vanish"),
      ("name-n", "appear"), ("level-label", "appear")] ∧
    moveKinds (zoomMoves 0) = [("walker", "appear")] ∧
    zoomMoves 1 = [("walker", .slide (leafQ.1 - boxEntryQ.1, leafQ.2 - boxEntryQ.2))] ∧
    zoomMoves 2 = [] ∧ moveKinds (zoomMoves 3) = [("walker", "vanish")] ∧
    moveKinds (zoomMoves 4) = [("leaf-label-early", "vanish"), ("leaf-label", "appear")] ∧
    (∀ k, crossFadeIds k = (if 3 ≤ k then [1, 2, 3, 4].flatMap fun j =>
        [s!"reject-{j}", s!"candidate-{j}", s!"candidate-label-{j}"] else []) ++
      (if k < 5 then ["name-n-early"] else ["name-n", "level-label"])) ∧
    (∀ k, crossActors k = (if (walkAt k).isEmpty then [] else [⟨"walker", walkAt k⟩]) ++
      (crossFadeIds k).map fun id => ⟨id, []⟩) ∧
    (∀ k, zoomActors k = (if (zoomWalkAt k).isEmpty then [] else [⟨"walker", zoomWalkAt k⟩]) ++
      [⟨if k < 5 then "leaf-label-early" else "leaf-label", []⟩]) ∧
    zoomView = ⟨Exact.toFloat enlargedLeft, Exact.toFloat (-enlargedHalf),
      Exact.toFloat enlargedRight, Exact.toFloat enlargedHalf⟩ ∧
    enlargedLeft = 151 / 100 ∧ enlargedRight = 1542 / 1000 ∧ enlargedHalf = 13 / 2000 ∧
    zoomBox = (let a := proj leaf |>.realPart
      let d := rat (1 / 20)
      [(a - d, rat 0 - d), (a + d, rat 0 - d), (a + d, d), (a - d, d)]) ∧
    (crossArrives && zoomArrives &&
      QSqrt.lt (proj crossN).realPart boxEntry.realPart &&
      QSqrt.lt boxEntry.realPart (proj leaf).realPart && boxEntry.num.conj == boxEntry.num &&
      (proj leaf).conj == proj leaf && (proj crossN).conj == proj crossN &&
      QSqrt.lt (rat enlargedLeft) (boxEntry.realPart - rat zoomWalkerRadius) &&
      QSqrt.lt (leafZ.realPart + rat zoomWalkerRadius) (rat enlargedRight) &&
      QSqrt.lt (rat zoomWalkerRadius) (rat enlargedHalf) &&
      leafQ.1 == leafZ.realPart &&
      QSqrt.lt ((proj leaf).realPart - rat (1 / 20)) (rat enlargedLeft) &&
      QSqrt.lt (rat enlargedRight) ((proj leaf).realPart + rat (1 / 20)) &&
      decide (enlargedHalf < 1 / 20)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel⟩

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

{figref "level-winding"}[]: the animation `TDCSGFigures.Levels.levelWinding`, an illustration,
and the data of its key frames, `TDCSGFigures.Levels.levelWinding_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Levels

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- The animation `levelWinding` and the data its key frames are drawn from, written out; an
illustration, to which this theorem is not linked. It has two panels on one clock, `circleMotion`
above `stripMotion`, of 23 keys each, one per level `levelAt k = -13 + k`; its poster is the last
key and its checks are strict. Key `k` of the circle draws `circleItems k`: the shaded arc of the
good phases and the circle (`circleBase`), the points of the levels up to `levelAt k`, the hand and
the mark of its sense at `levelAt k`, and the names of the levels up to `levelAt k` (`circleName`,
`goodName`). Level `m`'s point, its name and, when it is the level reached, the hand are placed at
the angle `angleOf (circleTurns m)` (`levelAngle`), in floating point, from the rational
`circleTurns m = phaseAt m`, the reduced phase rounded; step `k` turns the hand and its mark by
`turnOf k`, the difference of the turns of the two levels taken modulo one. Key `k` along the levels
draws `stripBase` (the bands, the gap, the strip and the walls, the names of the walls above the
strip's top `stripTop`, the marks of the phases at `stripTop`, `0` and `stripBottom`, the marks of
the levels below `stripBottom`), the points of the levels up to `levelAt k` at
`stripAt m = (m, 8 t)`, `t` the exact reduced phase in `ℚ(√5)`, and a ring about the last
(`tracerAt k`); step `k` slides the ring by the exact vector from one point to the next.
Decided exactly: each reduced phase is the one before plus `φ - 1` or minus `2 - φ`
(`phaseStepsArePhi`: the phase grows by `φ L`); each rational `circleTurns m` is within `2⁻⁶²` of
the exact reduced phase (`circleNearPhase`); every declared turn is within `2⁻⁶²` of `φ - 1`
(`turnsNearPhi`); every slide of the ring carries it exactly onto the next point, and the points
come only by declared appearances (`stripArrives`); the good levels are `-10`, `-2` and `3`. The
captions are stated as a function of the level; their words are pinned by evaluation in
`TDCSGTests.Motions`. Not stated: the floating-point angles and coordinates of the circle, how the
builders draw, the layout, the timing and the frames the browser draws between the key frames. -/
theorem levelWinding_keys :
    levelWinding.panels = #[{ title := "On a circle", motion := circleMotion },
      { title := "Along the levels", motion := stripMotion }] ∧
    levelWinding.poster = 22 ∧ levelWinding.checks = .fail ∧
    levelWinding.captions = ((List.range levelCount).map windingCaption).toArray ∧
    circleMotion.keys = ((List.range levelCount).map circleKey).toArray ∧
    (∀ k, (circleKey k).items = circleItems k) ∧
    (∀ k, circleItems k = circleBase ++ ((levels.take (k + 1)).map circlePoint).toArray ++
      #[hand (levelAt k), handSense (levelAt k)] ++
      ((levels.take (k + 1)).map circleName).toArray) ∧
    circleBase = #[
      Plane.sector ⟨0, 0⟩ 1 (pi / 2 - goodHalfAngle) (pi / 2 + goodHalfAngle)
        |>.role "good" |>.noOutline |>.fillOpacity 0.18 |>.named arcTitle,
      Plane.circle ⟨0, 0⟩ 1 |>.faint |>.width 1.5 |>.named circleTitle] ∧
    goodHalfAngle = 2 * pi * RealValue.toFloat bandWidth ∧
    circleMotion.steps = ((List.range (levelCount - 1)).map fun k =>
      ({ moves := circleMoves k } : MotionStep)).toArray ∧
    (∀ k, circleMoves k = (let m' := levelAt (k + 1)
      #[("hand", .turn ⟨0, 0⟩ (turnOf k)), ("hand-sense", .turn ⟨0, 0⟩ (turnOf k)),
        (s!"level-{m'}", .appear), (s!"name-{m'}", .appear)])) ∧
    (∀ k, levelAt k = levels.getD k 0) ∧
    (∀ m, circleTurns m = phaseAt m) ∧
    (∀ m, levelAngle m = angleOf (Exact.toFloat (circleTurns m))) ∧
    (∀ t, angleOf t = -(pi / 2) + 2 * pi * t) ∧
    (∀ θ ρ, onCircle θ ρ = ⟨ρ * Float.cos θ, ρ * Float.sin θ⟩) ∧
    (∀ k, turnOf k = (let d := circleTurns (levelAt (k + 1)) - circleTurns (levelAt k)
      if d < 0 then d + 1 else d)) ∧
    (∀ m, hand m = (Plane.arrow ⟨0, 0⟩ (onCircle (levelAngle m) handLength) |>.width 2
      |>.role "left" |>.named "the hand, at the phase of the level last reached"
      |>.withId "hand")) ∧
    (∀ m, handSense m = (let θ := levelAngle m
      Plane.angleMark ⟨0, 0⟩ (θ - 0.7) (θ - 0.12) (some 34) |>.role "left"
        |>.named "the sense of the hand's turn, counterclockwise" |>.withId "hand-sense")) ∧
    (∀ m, circlePoint m = (levelMark m (Plane.point (onCircle (levelAngle m) 1))
      |>.named s!"level {intText m}" |>.incident .on circleTitle
      |>.incident (if good m then .on else .outside) arcTitle |>.withId s!"level-{m}")) ∧
    (∀ m, circleName m = (let p := onCircle (levelAngle m) 1
      if good m then
        Plane.label (goodName m) p (if p.x ≥ 0 then .aboveRight else .aboveLeft) |>.size 16
          |>.role "good" |>.withId s!"name-{m}"
      else
        Plane.label (intText m) p (.toward (levelAngle m)) (some 6) |>.size 15 |>.faint
          |>.withId s!"name-{m}")) ∧
    (∀ m, goodName m =
      if m == -10 then "lo = −10" else if m == 3 then "hi = 3" else intText m) ∧
    (∀ m, intText m = if m < 0 then s!"−{-m}" else toString m) ∧
    (∀ m it, levelMark m it = if good m then it.role "good" |>.size 6 else it.faint |>.size 3.5) ∧
    stripMotion.keys = ((List.range levelCount).map stripKey).toArray ∧
    stripMotion.steps = ((List.range (levelCount - 1)).map fun k =>
      exactStep (stripMoves k)).toArray ∧
    (∀ m, stripAt m = (rat m, unitHeight * phaseQ m)) ∧ unitHeight = rat 8 ∧
    stripTop = unitHeight * rat (1 / 2) ∧ stripBottom = rat 0 - stripTop ∧
    bandTop = unitHeight * (rat (1 / 2) - bandWidth) ∧
    stripLeft = rat (-27 / 2) ∧ stripRight = rat (19 / 2) ∧
    (∀ m, phaseQ m = (reducedPhase m).getD (rat 0)) ∧
    (∀ k, tracerAt k = [stripAt (levelAt k)]) ∧
    (∀ ps, tracerItems ps = (ps.map fun c => Plane.Exact.circle c tracerRadius |>.width 2
      |>.role "left" |>.named "a ring about the level last reached" |>.withId "tracer").toArray) ∧
    (∀ k, (stripKey k).items = stripBase ++ ((levels.take (k + 1)).map stripPoint).toArray ++
      tracerItems (tracerAt k)) ∧
    (∀ s x y place offset, stripLabel s x y place offset =
      Plane.Exact.label s ((rat x, y) : QSqrt5 × QSqrt5) place offset) ∧
    stripBase = #[
      Plane.Exact.polygon (rect stripLeft bandTop stripRight stripTop) |>.role "good" |>.filled
        |>.noOutline |>.fillOpacity 0.18 |>.named "the upper good band",
      Plane.Exact.polygon (rect stripLeft stripBottom stripRight (rat 0 - bandTop)) |>.role "good"
        |>.filled |>.noOutline |>.fillOpacity 0.18 |>.named "the lower good band",
      Plane.Exact.polygon (rect (rat (-5 / 2)) stripBottom (rat (5 / 2)) stripTop) |>.faint
        |>.filled |>.noOutline |>.fillOpacity 0.12
        |>.named "the gap |m| ≤ 2 between the search ranges",
      Plane.Exact.polygon (rect stripLeft stripBottom stripRight stripTop) |>.faint |>.width 1
        |>.named "the phases from −L/2 to L/2",
      Plane.Exact.segment ((rat (-10), stripBottom) : QSqrt5 × QSqrt5) (rat (-10), stripTop)
        |>.role "good" |>.width 1.5 |>.dashed |>.named "the wall lo = −10",
      Plane.Exact.segment ((rat 3, stripBottom) : QSqrt5 × QSqrt5) (rat 3, stripTop)
        |>.role "good" |>.width 1.5 |>.dashed |>.named "the wall hi = 3",
      stripLabel "lo = −10" (-10) stripTop .above (some 14) |>.role "good",
      stripLabel "hi = 3" 3 stripTop .above (some 14) |>.role "good",
      stripLabel "L/2" (-27 / 2) stripTop .left,
      stripLabel "0" (-27 / 2) (rat 0) .left,
      stripLabel "−L/2" (-27 / 2) stripBottom .left,
      stripLabel "−13" (-13) stripBottom .below,
      stripLabel "−5" (-5) stripBottom .below,
      stripLabel "0" 0 stripBottom .below,
      stripLabel "5" 5 stripBottom .below,
      stripLabel "9" 9 stripBottom .below] ∧
    (∀ m, stripPoint m = (
      let y := (stripAt m).2
      let it := levelMark m (Plane.Exact.point (stripAt m)) |>.named s!"level {intText m}"
        |>.incident (above bandTop y) "the upper good band"
        |>.incident (above y (rat 0 - bandTop)) "the lower good band"
        |>.incident (if QSqrt.lt stripBottom y && QSqrt.lt y stripTop then .inside else .outside)
          "the phases from −L/2 to L/2"
      let it := if m == -10 then it.incident .on "the wall lo = −10"
        else if m == 3 then it.incident .on "the wall hi = 3" else it
      it.withId s!"level-{m}")) ∧
    (∀ k, stripMoves k = (let p := stripAt (levelAt k)
      let q := stripAt (levelAt (k + 1))
      [("tracer", .slide (q.1 - p.1, q.2 - p.2)), (s!"level-{levelAt (k + 1)}", .appear)])) ∧
    (∀ k, stripActors k = [⟨"tracer", tracerAt k⟩] ++
      (levels.take (k + 1)).map fun m => ⟨s!"level-{m}", [stripAt m]⟩) ∧
    (levelCount == 23 && phaseStepsArePhi && circleNearPhase && turnsNearPhi && stripArrives &&
      levels.filter good == [-10, -2, 3]) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ _ _ => rfl, rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, by decide +kernel⟩

end TDCSGFigures.Levels
```

# The figures of chapter 7

%%%
tag := "theorems-confinement"
file := "Theorems-confinement"
%%%

{figref "component-of-zero"}[]: the animation `TDCSGFigures.Confinement.componentOfZero`, whose
last key frame is the figure of the component, with its theorem
`TDCSGFigures.Confinement.componentOfZero_spec`; the layers and the other key frames are stated in
`TDCSGFigures.Confinement.componentOfZero_keys`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Confinement

open PILean PILean.Plane PILean.Exact TDCSGFigures

set_option maxHeartbeats 4000000 in
/-- The animation `componentOfZero` and the figure of the component, its last key frame. The
animation has one panel, `compMotion`, whose last key is `componentOfZeroFinal`; its poster is that
key and its checks are strict. The figure's items are `compItems lastLayer false`: the window, an
edge `edgeItem n m` for each edge of `compEdges`, a point `labelPoint n` for each label of
`compLabels`, the window centre (on the edge from `0` to `e₀`) and the labels with the legend, in
this order, each with its id; the builders' definitions are stated, and at the last layer every
edge and every label is drawn (`compItems lastLayer false` lists all 19 edges and all 18 labels,
in order). The component of `0` found by the exact search (`component`, every window test decided
in `ℚ(√5)`) is the list of 18 labels written out, and its edges are the 19 written out, each from a
weight-zero label `n` to `n + eⱼ`; every label lies inside the window, so each point's record
holds. Every coordinate of every label is `-1`, `0` or `1`, and in each coordinate `j` the good
levels nearest the gap `|m| ≤ 2` are those the caption states (`wallText`), with every label
strictly inside the slab `lo < nⱼ ≤ hi` they bound. Not stated: how the builders and modifiers
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
    componentOfZero.panels = #[{ motion := compMotion }] ∧
    componentOfZero.poster = 6 ∧ componentOfZero.checks = .fail ∧
    compMotion.keys = ((List.range 7).map compKey).toArray ∧
    compKey 6 = componentOfZeroFinal ∧
    componentOfZeroFinal.items = compItems lastLayer false ∧
    (∀ d tinted, compItems d tinted =
      #[compWindow] ++
        ((List.range compEdges.length).filter (edgeLayer · ≤ d)).toArray.map compEdge ++
        (if tinted && 1 ≤ d then (layerIndices d).toArray.map compTint else #[]) ++
        ((List.range compLabels.length).filter fun i =>
          layerOf (compLabels.getD i zeroLabel) ≤ d).toArray.map compLabel ++
        #[compCentre (1 ≤ d)] ++
        compNames.filter fun it => 2 ≤ d || it.actorId? != some "name-e0") ∧
    lastLayer = 5 ∧
    compWindow = (Plane.Exact.disk ((compX, 0) : Rat × Rat) (39 / 40 : Rat) |>.role "window"
      |>.fillOpacity 0.07 |>.named "the window"
      |>.describedBy "the closed disk |w − x| ≤ r/2, r = 1.95, x = 1/2"
      |>.declRef `TDCSG.Five.InWindow |>.withId "window") ∧
    (∀ i, compEdge i = (let (n, m) := compEdges.getD i (zeroLabel, zeroLabel)
      edgeItem n m |>.withId s!"edge-{i}")) ∧
    (∀ i, compLabel i =
      (labelPoint (compLabels.getD i zeroLabel) .inside "the window" |>.withId s!"label-{i}")) ∧
    (∀ onEdge, compCentre onEdge = (
      let it := Plane.Exact.point ((compX, 0) : Rat × Rat) |>.role "window" |>.marker .cross
        |>.named "the window center x = 1/2" |>.incident .inside "the window"
      (if onEdge then it.incident .on "the edge from (0, 0, 0, 0, 0) to (1, 0, 0, 0, 0)" else it)
        |>.withId "centre")) ∧
    compNames = #[
      Plane.Exact.label "0" origin (.toward (Plane.deg 200)) |>.role "left" |>.withId "name-0",
      Plane.Exact.label "e₀" rightCentre .auto |>.role "right" |>.withId "name-e0",
      Plane.Exact.label "dots: weight 0 (left centers)" ((1 / 2 : Rat), (-9 / 8 : Rat))
        |>.role "left" |>.withId "legend-dots",
      Plane.Exact.label "squares: weight 1 (right centers)" ((1 / 2 : Rat), (-5 / 4 : Rat))
        |>.role "right" |>.withId "legend-squares",
      Plane.Exact.label "×: the window center x = 1/2" ((1 / 2 : Rat), (-11 / 8 : Rat))
        |>.role "window" |>.withId "legend-centre"] ∧
    (compLabels == [#[0, 0, 0, 0, 0], #[1, 0, 0, 0, 0], #[0, 1, 0, 0, 0], #[0, 0, 0, 0, 1],
      #[0, 0, 0, -1, 1], #[0, 0, 1, -1, 1], #[0, -1, 1, -1, 1], #[1, -1, 1, -1, 1],
      #[1, -1, 1, -1, 0], #[1, -1, 1, 0, 0], #[1, -1, 0, 0, 0], #[0, 1, -1, 0, 0],
      #[0, 1, -1, 1, 0], #[0, 1, -1, 1, -1], #[1, 1, -1, 1, -1], #[1, 0, -1, 1, -1],
      #[1, 0, 0, 1, -1], #[1, 0, 0, 0, -1]] &&
    compEdges == [(#[0, 0, 0, 0, 0], #[1, 0, 0, 0, 0]), (#[0, 0, 0, 0, 0], #[0, 1, 0, 0, 0]),
      (#[0, 0, 0, 0, 0], #[0, 0, 0, 0, 1]), (#[0, 0, 0, -1, 1], #[0, 0, 1, -1, 1]),
      (#[0, 0, 0, -1, 1], #[0, 0, 0, 0, 1]), (#[0, -1, 1, -1, 1], #[1, -1, 1, -1, 1]),
      (#[0, -1, 1, -1, 1], #[0, 0, 1, -1, 1]), (#[1, -1, 1, -1, 0], #[1, -1, 1, 0, 0]),
      (#[1, -1, 1, -1, 0], #[1, -1, 1, -1, 1]), (#[1, -1, 0, 0, 0], #[1, 0, 0, 0, 0]),
      (#[1, -1, 0, 0, 0], #[1, -1, 1, 0, 0]), (#[0, 1, -1, 0, 0], #[0, 1, 0, 0, 0]),
      (#[0, 1, -1, 0, 0], #[0, 1, -1, 1, 0]), (#[0, 1, -1, 1, -1], #[1, 1, -1, 1, -1]),
      (#[0, 1, -1, 1, -1], #[0, 1, -1, 1, 0]), (#[1, 0, -1, 1, -1], #[1, 1, -1, 1, -1]),
      (#[1, 0, -1, 1, -1], #[1, 0, 0, 1, -1]), (#[1, 0, 0, 0, -1], #[1, 0, 0, 1, -1]),
      (#[1, 0, 0, 0, -1], #[1, 0, 0, 0, 0])] &&
    compLabels.all (fun n => inWindow compRadiusSq compX n) &&
    compEdges.all (fun (n, m) => weight n == 0 &&
      (List.range 5).any fun j => m == shift n j 1) &&
    compLabels.all (fun n => n.all fun c => -1 ≤ c && c ≤ 1) &&
    [wallText 0, wallText 1, wallText 2, wallText 3, wallText 4] ==
      ["n₀: −4, 4", "n₁: −3, 10", "n₂: −7, 6", "n₃: −7, 6", "n₄: −3, 10"] &&
    (List.range 5).all (fun j => match nearestWalls j with
      | (some lo, some hi) => compLabels.all fun n => lo < n[j]! && n[j]! ≤ hi
      | _ => false) &&
    (List.range compEdges.length).filter (edgeLayer · ≤ 5) == List.range 19 &&
    (List.range compLabels.length).filter (fun i => layerOf (compLabels.getD i zeroLabel) ≤ 5) ==
      List.range 18) = true :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, by decide +kernel⟩

figure_links componentOfZero componentOfZero_spec

set_option maxHeartbeats 4000000 in
/-- The layers of `componentOfZero` and its key frames before the last, written out. The layers
`compLayers` are the labels of the component by their distance from `0` in the center graph: the
first is `[0]`, they hold the labels of `compLabels`, each once, every edge of `compEdges` joins two
consecutive layers, and every label of a layer after the first is joined to one of the layer before
(`layersAreDistances`, decided exactly). The edges of `compEdges` are all the edges of the center
graph among the labels of `compLabels` (`edgesAmong`), and `compLabels` is the whole component,
as the search that found it stops only when no label of the window is joined to one found
(`componentOfZero_spec`); so the layer of a label is its distance from `0`, by induction on the
distance, and no label lies at distance 6. Key `d ≤ 5` is `compItems d true`: the window, the edges
with both ends at distance at most `d` (`edgeLayer`), for `d ≥ 1` a tint about each label at
distance `d` (`compTint`, the part of a small disk about it within `tintClip` of the window
centre), drawn under the labels, the labels at distance at most `d`, the window centre (on the
edge from `0` to `e₀` from `d = 1`), the name `0`, the name `e₀` from `d = 2`, and the legend. The
moves of each step are the actors of one key absent from the next, which vanish, and those of the
next absent from the one, which appear (`compMoves`); each actor that comes and goes is listed with
the exact points that fix it (`compActors`: the projections of the ends of an edge, of a label, of
a tinted label), and every declared move carries the actors of one key onto those of the next
(`compArrives`). The captions are stated as a function of the layers; their words are pinned by
evaluation in `TDCSGTests.Motions`. Not stated: how the builders draw, the layout, the timing and
the frames the browser draws between the key frames. -/
theorem componentOfZero_keys :
    compLayers = [
      [#[0, 0, 0, 0, 0]],
      [#[1, 0, 0, 0, 0], #[0, 1, 0, 0, 0], #[0, 0, 0, 0, 1]],
      [#[0, 0, 0, -1, 1], #[1, -1, 0, 0, 0], #[0, 1, -1, 0, 0], #[1, 0, 0, 0, -1]],
      [#[0, 0, 1, -1, 1], #[1, -1, 1, 0, 0], #[0, 1, -1, 1, 0], #[1, 0, 0, 1, -1]],
      [#[0, -1, 1, -1, 1], #[1, -1, 1, -1, 0], #[0, 1, -1, 1, -1], #[1, 0, -1, 1, -1]],
      [#[1, -1, 1, -1, 1], #[1, 1, -1, 1, -1]]] ∧
    (∀ n, layerOf n = (compLayers.findIdx? (·.contains n)).getD (lastLayer + 1)) ∧
    (∀ n m, joined n m = compEdges.any fun (a, b) => (a == n && b == m) || (a == m && b == n)) ∧
    (layersAreDistances = (
      let all := compLayers.flatten
      compLayers.head? == some [zeroLabel] &&
        all.length == compLabels.length && compLabels.all all.contains &&
        all.all (fun n => all.count n == 1) &&
        compEdges.all (fun (a, b) => layerOf a + 1 == layerOf b || layerOf b + 1 == layerOf a) &&
        compLayers.zipIdx.all fun (ls, d) =>
          d == 0 || ls.all fun n => (compLayers.getD (d - 1) []).any (joined n))) ∧
    (∀ i, edgeLayer i = (let (a, b) := compEdges.getD i (zeroLabel, zeroLabel)
      max (layerOf a) (layerOf b))) ∧
    (∀ d, layerIndices d =
      (List.range compLabels.length).filter fun i => layerOf (compLabels.getD i zeroLabel) == d) ∧
    tintRadius = 1 / 22 ∧ tintClip = 987 / 1000 ∧
    (∀ i, compTint i = (Plane.Exact.lens (ZetaFrac.ofZeta (proj (compLabels.getD i zeroLabel)))
        ⟨Zeta5.ofInt 1, 2⟩ tintRadius tintClip |>.role "lens" |>.noOutline |>.fillOpacity 0.3
      |>.named "a tint about a label of the frontier" |>.withId s!"tint-{i}")) ∧
    (∀ d, compKey d = if d ≤ lastLayer then { componentOfZeroFinal with items := compItems d true }
      else componentOfZeroFinal) ∧
    compMotion.steps = ((List.range 6).map (exactStep ∘ compMoves)).toArray ∧
    (∀ d, compActors d = (
      let z := fun (n : Label) => ZetaFrac.ofZeta (proj n)
      let dd := min d lastLayer
      (((List.range compEdges.length).filter (edgeLayer · ≤ dd)).map fun i =>
          let (n, m) := compEdges.getD i (zeroLabel, zeroLabel)
          (⟨s!"edge-{i}", [z n, z m]⟩ : ExactActor ZetaFrac)) ++
        (if 1 ≤ d && d ≤ lastLayer then (layerIndices d).map fun i =>
          ⟨s!"tint-{i}", [z (compLabels.getD i zeroLabel)]⟩ else []) ++
        (((List.range compLabels.length).filter fun i =>
          layerOf (compLabels.getD i zeroLabel) ≤ dd).map fun i =>
            ⟨s!"label-{i}", [z (compLabels.getD i zeroLabel)]⟩) ++
        (if 2 ≤ d then [⟨"name-e0", []⟩] else []))) ∧
    (∀ d, compMoves d = (
      let a := compActors d
      let b := compActors (d + 1)
      (a.filter (fun x => !b.any (·.id == x.id))).map (·.id, .vanish) ++
        (b.filter (fun x => !a.any (·.id == x.id))).map (·.id, .appear))) ∧
    componentOfZero.captions = ((List.range 7).map compCaption).toArray ∧
    compEdges = edgesAmong compLabels ∧
    (layersAreDistances && compArrives &&
      (List.range 6).map layerIndices ==
        [[0], [1, 2, 3], [4, 10, 11, 17], [5, 9, 12, 16], [6, 8, 13, 15], [7, 14]] &&
      (List.range 6).map foundBy == [1, 4, 8, 12, 16, 18]) = true :=
  ⟨rfl, fun _ => rfl, fun _ _ => rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl,
    fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, by decide +kernel⟩

end TDCSGFigures.Confinement
```

{figref "walk-to-leaf"}[]: the animation `TDCSGFigures.Confinement.walkToLeaf`, an illustration,
and the data of its key frames, `TDCSGFigures.Confinement.walkToLeaf_spec`.

```Verso.Genre.Manual.InlineLean.lean
namespace TDCSGFigures.Confinement

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- The animation `walkToLeaf` and the data its key frames are drawn from, written out; an
illustration, to which this theorem is not linked. It has one panel whose keys are `walkKey k`,
`k = 0, …, 16`, and whose steps are made from the declared moves `walkMoves`; its poster, the still
shown while it is pointed at or focused, under reduced motion and in print, is the last key, with
the labels numbered. Key `k` draws the
window, the edges and labels of the path `path` up to `path[k]` (`walkShown`), from key `15` on the
candidates `n + eₖ` (`k ≠ 2`) of the leaf with their spokes, at key `16` the step back and the
labels numbered in the order of the walk, and a circle about `P(walkAt k)`, the label where the walk
is: `path[k]` up to the leaf, the leaf at key `15`, `n + e₂` at key `16`. The circle is drawn at its
anchor (`walkerAnchors`), and the exact actors of the keys (`walkActors`) are the points the keys
draw. Step `k` slides the circle from `P(walkAt k)` to `P(walkAt (k + 1))` when they differ, by
`±ζʲ` for a step `±eⱼ` of the path, and fades in what the next key shows first; each declared slide,
applied exactly in `ℚ(ζ₅)` to the anchors of the actors of one key, gives those of the next
(`walkArrives`). The data are checked exactly at `r = 2.13`, `x = 1/5`: the path starts at `0`;
every label has weight `0` or `1`, and each step adds `eⱼ` to a label of weight `0` or takes it from
a label of weight `1`; every label lies in the window; so the path is a path of the centre graph.
`n` has weight zero, its level `n₂ = -5` is good, and its candidates `n + e₀`, `n + e₁`, `n + e₃`,
`n + e₄` lie outside the window, so `n + e₂` is its only neighbour. The caption of each key is
stated as a function of the path (`walkCaption`); its words, which the kernel does not compute, are
pinned by `#guard` in `TDCSGTests.Motions`. Not stated: how the builders draw, the layout, the
timing and the frames the browser draws between the key frames. -/
theorem walkToLeaf_spec :
    walkToLeaf.panels = #[{ motion :=
      { keys := ((List.range walkKeyCount).map walkKey).toArray,
        steps := ((List.range (walkKeyCount - 1)).map fun k =>
          exactStep (walkMoves k)).toArray } }] ∧
    walkKeyCount = 17 ∧ walkToLeaf.poster = walkKeyCount - 1 ∧
    walkToLeaf.captions = ((List.range walkKeyCount).map walkCaption).toArray ∧
    (∀ (k : Nat), walkAt k = (
  if k ≤ path.length - 1 then path.getD k zeroLabel
  else if k == path.length then leafN
  else beforeLeaf
    : Label)) ∧
    (∀ (k : Nat), walkShown k = (
min (k + 1) path.length
    : Nat)) ∧
    (∀ (k : Nat), walkerAnchors k = (
[ZetaFrac.ofZeta (proj (walkAt k))]
    : List ZetaFrac)) ∧
    (∀ (k : Nat), walker k = (
  Plane.Exact.circle ((walkerAnchors k).headD (ZetaFrac.ofZeta origin)) walkerRadius |>.width 2
    |>.named "a circle about the label where the walk is" |>.withId "walker"
    : Item)) ∧
    (walkerRadius = (
1 / 20
    : Rat)) ∧
    (walkNumbered = (
(List.range (path.length - 3)).map (· + 1)
    : List Nat)) ∧
    (∀ (k : Nat), walkKey k = (
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
        else #[]) ++
      (if back then (walkNumbered.toArray.map fun i =>
          Plane.Exact.label s!"{i}" (proj (path.getD i zeroLabel)) .auto |>.size 11
            |>.withId s!"number-{i}") else #[])
    info := { title := s!"The walk at key {k}" } }
    : Plane.Figure)) ∧
    (∀ (k : Nat), walkNameIds k = (
  (if path.length - 2 ≤ k then ["name-before"] else []) ++
    (if path.length - 1 ≤ k then ["name-leaf", "good-level"] else []) ++
    (if path.length ≤ k then [0, 1, 3, 4].map (s!"candidate-label-{·}") else []) ++
    (if path.length + 1 ≤ k then walkNumbered.map (s!"number-{·}") else [])
    : List String)) ∧
    (∀ (k : Nat), walkMoves k = (
  let slide :=
    ("walker", ExactMove.slide (ZetaFrac.ofZeta (proj (walkAt (k + 1)) - proj (walkAt k))))
  let names := ((walkNameIds (k + 1)).filter (!(walkNameIds k).contains ·)).map (·, .appear)
  if k + 1 < path.length then
    [slide, (s!"edge-{k}", .appear), (s!"label-{k + 1}", .appear)] ++ names
  else if k + 1 == path.length then
    ([0, 1, 3, 4].map (s!"reject-{·}", .appear)) ++
      ([0, 1, 3, 4].map (s!"candidate-{·}", .appear)) ++ names
  else [slide, ("back", .appear)] ++ names
    : List (String × ExactMove ZetaFrac))) ∧
    (∀ (k : Nat), walkActors k = (
  let z := ZetaFrac.ofZeta
  let ps := path.take (walkShown k)
  let cands := if path.length ≤ k then [0, 1, 3, 4] else []
  [⟨"walker", walkerAnchors k⟩] ++
    ((ps.zip ps.tail).zipIdx.map fun ((a, b), i) => ⟨s!"edge-{i}", [z (proj a), z (proj b)]⟩) ++
    (ps.zipIdx.map fun (n, i) => ⟨s!"label-{i}", [z (proj n)]⟩) ++
    (cands.map fun j => ⟨s!"reject-{j}", [z (proj leafN), z (proj (shift leafN j 1))]⟩) ++
    (cands.map fun j => ⟨s!"candidate-{j}", [z (proj (shift leafN j 1))]⟩) ++
    (if path.length + 1 ≤ k then [⟨"back", [z (proj leafN), z (proj beforeLeaf)]⟩] else []) ++
    (walkNameIds k).map fun id => ⟨id, []⟩
    : List (ExactActor ZetaFrac))) ∧
    (∀ (k : Nat), stepText k = (
  let (j, sgn) := stepDir (path.getD k zeroLabel) (path.getD (k + 1) zeroLabel)
  s!"{if sgn == 1 then "+" else "−"} e{sub j}"
    : String)) ∧
    (∀ (k : Nat), walkCaption k = (
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
    s!"From the leaf n the only step leads back to n + e₂, as the one-step lemma requires. The \
      labels of the path are numbered 1 to {path.length - 3} in the order of the walk; labels \
      {path.length - 2} and {path.length - 1} are n + e₂ and n."
    : String)) ∧
    (List.range walkKeyCount).all (fun k => (walkerAnchors k).length == 1) = true ∧
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
      if weight a == 0 then b == shift a j 1 else b == shift a j (-1)) = true ∧
    path.all (fun n => weight n == 0 || weight n == 1) = true ∧
    weight leafN = 0 ∧ isGoodLevel walkRadiusSq walkX 2 (-5) = some true ∧
    [0, 1, 3, 4].all (fun j => !inWindow walkRadiusSq walkX (shift leafN j 1)) = true := by
  repeat' apply And.intro
  all_goals first
    | (intros; unfold walkToLeaf; with_reducible rfl)
    | (intros; unfold walkAt; with_reducible rfl)
    | (intros; unfold walkShown; with_reducible rfl)
    | (intros; unfold walkerAnchors; with_reducible rfl)
    | (intros; unfold walker; with_reducible rfl)
    | (intros; unfold walkerRadius; with_reducible rfl)
    | (intros; unfold walkNumbered; with_reducible rfl)
    | (intros; unfold walkKey; with_reducible rfl)
    | (intros; unfold walkNameIds; with_reducible rfl)
    | (intros; unfold walkMoves; with_reducible rfl)
    | (intros; unfold walkActors; with_reducible rfl)
    | (intros; unfold stepText; with_reducible rfl)
    | (intros; unfold walkCaption; with_reducible rfl)
    | decide +kernel
    | (simp only [generatorMoves]; done)
    | (simp only [stepMoves]; done)
    | (simp only [jumpMoves]; done)
    | (simp only [disjointMoves]; done)

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
