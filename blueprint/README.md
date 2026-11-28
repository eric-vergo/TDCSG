# Building the fivefold blueprint

From the repository root, with the Lean version in `lean-toolchain`, run

```sh
lake build TDCSGBlueprint
lake exe vbp build
lake exe vbp check
python3 -m http.server --directory _out/site/html-multi 8000
```

Open [the local site](http://localhost:8000/). The source links under the figures and in the
Lean panels name the commit the checkout is at; on a tree with changes not yet committed they lead
to that commit's lines, so commit before building a site that others read.

The first command elaborates the
chapters and their linked Lean declarations. The generator writes a multipage
site, sidebar, searchable Lean panels, dependency graph and Project Stats page.
The Pages deployment serves the same directory under the repository prefix.

`lake exe vbp build` also replays the site's Lean declarations, with everything they depend on,
in the two kernel checkers of the Lean toolchain, `con-leche` and `con-ron` (in the toolchain's
`bin`). Green marks and fills appear only where both accepted; the Project Stats page shows each
checker's answer. An accepted export is recorded in the user's cache directory
(`verso-blueprint/kernel-replay-checkers.json`), and a later build of an identical export does
not run the checkers again. `lake exe vbp build --no-kernel-replay` skips the replay; the site
then shows no green and no page says "proved". The release check
(`scripts/check-pages.py --release`) requires an accepted replay that covers every node.

The entry point is `BlueprintMain.lean`. The chapter sequence lives in
`blueprint/TDCSGBlueprint.lean`, one module per chapter in
`blueprint/TDCSGBlueprint/`:

| Chapter | Module |
|---|---|
| 1 Compound symmetry | `CompoundSymmetry` |
| 2 Two disks and the critical radius (statement of the main theorem) | `TwoDisks` |
| Part I, Infinite at the threshold | `PartOne` |
| 3 The chord and its three words | `Chord` |
| Part II, Finite below the threshold | `PartTwo` |
| 4 Lift to integer labels | `Lift` |
| 5 The lens estimate | `Lens` |
| 6 Good levels | `Levels` |
| 7 Confinement | `Confinement` |
| 8 Proof of the main theorem | `MainTheorem` |
| 9 Other orders | `OtherOrders` |
| 10 Verification | `Verification` |
| Figures and their theorems (unnumbered) | `TDCSGFigureTheorems`, at the repository root |

Prose links to files of this repository use the role
`{repoFile "notes/engine.md"}[engine guide]` of Verso Blueprint. It links to
the file at the commit the site is built from, as the Lean source links do, and the release check
in `scripts/check-pages.py` rejects any other link into the repository except the repository home,
the Actions history and the run that built the release.

The two parts are unnumbered pages between the chapters, so the chapters keep
one numbering throughout. The main theorem is stated in `TwoDisks`; its
`:::proof` block is in `MainTheorem`, which imports `TwoDisks`, and Blueprint
merges the two into one node.

The graph uses the dependency labels of the chapter statements. Set
`(lean := "...")` to the declaration being described and `(uses := "...")` to
the nodes whose declarations its Lean proof uses. Helper lemmas of a proof go in
`(lean := "...")` on its `:::proof` block. The generator enables the fork's side-by-side
source view. The challenge and solution declare the same constants and must be
elaborated separately. The verification chapter imports only the solution.

## Figures

Every figure of the site is drawn by PILean: the value of a declaration with the attribute
`@[figure]` in the library `TDCSGFigures` (`TDCSGFigures/`, one module per page or chapter, plus
`Data` and `Data/`, the exact objects, and `Style`, the house style). The library imports PILean
and the orbit engine `TDCSGCompute` only: no Mathlib, no Verso. The generator renders the figures
the pages use with `PILeanVerso.withFigures` into `-verso-data/pilean-figures` with a manifest,
fingerprints and the source record of each file, and fails the build when a figure with
`checks := .fail` has a layout problem (at its full and its narrow width, in both themes).

A chapter shows a figure with `:::figure` (inline, so that the picture follows the page's theme and
its elements link to Lean), with a label, a text alternative, the theorem it proves and the caption
as the body; the site shows no slider or stepper (`:::figure_explorer`), and
`scripts/check-motion.py` checks that no page has one. An animation (a PILean
`MotionPanels` marked `@[figure illustration]`) is shown with `:::figure` too, always inline: it
loops on its own clock with no controls and no script, and shows its key frames as stills, each with
its caption, while it is hovered or focused, when the reader turns animations off with the switch
beside the theme control or the system asks for reduced motion, and in print. Figures are numbered
as the Blueprint numbers its statements: "Figure 5.1" is the first figure of chapter 5, and the
figures of the unnumbered pages (the front page and the two part pages) are numbered 1 to 4. Prose
refers to a figure by its label, `{figref "lens-estimate"}[]`, which renders its current number.

Under each figure the page shows its number and caption, then a source line: the declaration,
its file and line linked to the repository at the build's commit, the fingerprint, and the
theorem that states what it draws. Links to Lean declarations, in the source line and on the
elements of an inline picture, lead into the site (`leanLinks := .site`): to the declaration's
row in the Lean panel of the Blueprint entry that names it, or, for the theorems of the figures,
to the inline Lean block that defines it. The build warns about a declaration with no such place.
The page Figures lists every figure.

The theorems of the figures, `<name>_spec`, are stated and proved in Lean blocks of the page
"Figures and their theorems", `TDCSGFigureTheorems.lean`, one section per page of the site, and
attached to their figures there with `figure_links`. Each writes out the figure's items and proves
the facts its caption uses. The page lives at the repository root, in a library of its own,
because PILean derives a theorem's source link from its module name. The theorems are not
Blueprint statements, so they add no node to the dependency graph and are not part of the kernel
replay; `lake build TDCSGBlueprint` checks them.

`scripts/check-pages.py` reads the manifest, requires a visible numbered caption, an accessible
name and gapless numbering, allows no other image in the pages, follows the Lean links and every
link to a place in the same page, requires every animation to be recorded as checked strictly
(`checks` `fail`, no error left), with its narrow rendition (except the walk of chapter 7, scaled
down as a whole on a small screen), and as an illustration or, for an animation that replaced a
figure with a linked theorem, with that theorem (`LINKED_MOTIONS` in the script), and calls
PILean's site checks (`tools/site/` of the `pilean` package): `pilean-verify`, every inline
picture, moving ones included, against its file (`inline_check.py`), nothing active in a figure
or an animation (`markup_check.py`), each figure's page against the manifest, with an animation's
words, its table of steps, its stills and its files (`page_check.py`); and a fresh render of the
figures compared with the site's folder.

`scripts/check-motion.py` calls PILean's browser checks of animations, on standalone files
(`tools/motion-browser-check.py`) and on the site's pages (`tools/site/motion_browser.py`), with
the exact expectations `lake exe tdcsg-motion-out` writes from Lean, and adds the positions in the
dark theme, the width against the text column, that the site has no script of its own for a
figure, and that no page scrolls sideways at 1440, 768, 390 and 320 px and every formula is drawn
inside the block that holds it. It needs Playwright for Python with its Chromium:

```sh
lake exe tdcsg-motion-out /tmp/motion-out
python3 scripts/check-pages.py _out/site/html-multi
python3 scripts/check-motion.py _out/site/html-multi /tmp/motion-out [SHOTS] [--workers N]
```

The release workflow runs both after the build, the browser checks with four workers (`--workers`,
pages checked at a time, each in its own Chromium).

`scripts/check-engines.py`, run by hand on a Mac, adds the same checks in Firefox (on the site, on
the standalone files, and the formulas of every page) and in WebKit, the engine of Safari (on the
standalone files, through PILean's `tools/webkit/webkit_check.py`, which needs a logged-in session
with a screen and shows nothing). It runs each pass only where it can and says what it skipped; it
installs nothing:

```sh
python3 scripts/check-engines.py _out/site/html-multi /tmp/motion-out [--workers N]
```

### Animations

Thirteen figures are animations drawn by PILean from exact key frames: the turn of one disk and
two disjoint disks of chapter 1 (`TDCSGFigures.extensionJump`, `disjointDisks` in
`TDCSGFigures/Compound.lean`), one step of the left generator and a word letter by letter of
chapter 2 (`generatorStep`, `wordSteps` in `TDCSGFigures/TwoDisks.lean`), the three words, the
interval exchange and the orbit on the chord of chapter 3 (`wordLoop1`, `wordLoop2`, `wordLoop3`,
`chordOrbit` in `TDCSGFigures/Chord.lean`, `exchangedIntervals` in
`TDCSGFigures/ProofDiagrams.lean`), the frame pair of chapter 4 (`TDCSGFigures.Lift.framePair` in
`TDCSGFigures/FramePairMotion.lean`) and the walk of chapter 7
(`TDCSGFigures.Confinement.walkToLeaf`). Each key is a `Plane.Figure` of exact data, and each step
between two keys declares its moves: a turn of named items by a fifth of a full turn about an
exact centre, a slide along an exact vector, or an item that appears or vanishes. The moves are
declared once, exactly (`TDCSGFigures.ExactMove` in `TDCSGFigures/Data/Moves.lean`, or the frame
pair's own steps), and read twice: by PILean's engine, which draws them, and by the exact arrival
check (`TDCSGFigures.allArrive`), which applies each to the exact anchors of the actors of one key
in `ℚ(ζ₅)` or `ℚ(√5)²` and requires those of the next. PILean checks, at the strict level, that each
declared move carries one key onto the next on the page, that every rest shows its key's still and
that the written SVG draws what its plan says; the site build refuses an animation not checked
strictly. The animations share one timing, `TDCSGFigures.motionPacing` in
`TDCSGFigures/Style.lean` (the pieces of the interval exchange slide as long as a turn takes); the
frame pair shows each turn with an arrow about its centre, whose fades are steps of their own
between short rests, so that the pause between two turns keeps the shared length.

Where an animation replaced a figure with a linked theorem (`generatorStep`, `extensionJump`,
`disjointDisks`, `exchangedIntervals`, `chordOrbit`), it keeps the figure's name, label and
number, its last key frame is that figure (`<name>Final`) and its poster, the still the figure page,
the reduced-motion view and print show first, and the theorem `<name>_spec` stays linked: it states
that the last key frame is the figure and what the figure draws. The other key frames, the moves
and the captions are stated in a plain theorem `<name>_keys`. The other animations are
illustrations (`@[figure illustration]`): no theorem is linked to them, and the data of their key
frames are stated in `wordLoop_keys`, `wordSteps_spec`, `framePair_keys` and `walkToLeaf_spec`.
Each actor that moves is drawn at the exact anchors that its arrival check reads, and the theorems
state those anchors.
The exact arrival check works modulo a full turn, so the sense and the size of every declared turn
are pinned separately: each turn by a letter uses the letter's own fraction `Letter.turns`, whose
factor and size `turnsAreFifths` states (`TDCSGFigures/Data/Turns.lean`), and each statement writes
out the fractions its animation declares (`declaredTurns`). `TDCSGTests.Motions` proves that the
exact arrival checks refuse a wrong centre, fraction, vector or position.

The site ships no script of its own for the animations: the moving pictures are SMIL in the page,
and what hides them is the stylesheet of PILean's adapter and the motion switch of Verso Blueprint.
Each animation keeps the label, and so the anchor, of the figure at its place (`#word-trace` for
Figure 3.2, `#change-of-frame` for Figure 4.2, and so on), and the site build writes a page that
sends the reader on at the address of each figure page whose declaration has a new name
(`movedFigures` in `BlueprintMain.lean`).

### Adding a figure

1. Put the exact data it needs in `TDCSGFigures/Data.lean` or `TDCSGFigures/Data/` (points of
   `ℤ[ζ₅]` as `PILean.Exact.Zeta5`, reals of `ℚ(√5)` as `QSqrt5`, radii as `Rat` or
   `SqrtOf QSqrt5`, orbits through `TDCSGFigures.orbit`), with a `#guard` for every property its
   caption states.
2. Draw it in the module of its chapter (`TDCSGFigures/<Chapter>.lean`, imported by
   `TDCSGFigures.lean`) as a `Plane.Figure` in `houseStyle` (`partTwoStyle`, `radiusStyle` for their roles), with
   `checks := .fail`, `width := figureWidth` and `narrowWidth := some narrowWidth`. Disks are
   outlines (`noFill`), the lens a region of its own (`role lensRole`), the left disk and what
   belongs to it `role leftRole`, the right `role rightRole`, the window `role windowRole`, good
   levels `role goodRole`; every point, disk, centre, radius and region has a title (`named`) and
   a label beside it; a point near a curve records where it is (`incident`), decided exactly. Link
   elements to the Lean declarations that state their facts with `declRef`, choosing declarations
   that have a Blueprint entry.
3. Mark it `@[figure]`, add it to `previews` in `TDCSGFigures/Preview.lean` and look at the
   previews (below).
4. Write its specification theorem `<name>_spec` in a Lean block of its page's section of
   `TDCSGFigureTheorems.lean`, with the item list written out and the exact facts proved by `rfl`
   and `decide +kernel` (see `TDCSGFigures.criticalChord_spec`), followed by `figure_links`.
5. Put it in its chapter with `:::figure TDCSGFigures.name (label := "…") (inline := true)
   (links := TDCSGFigures.name_spec) (alt := "…")`, the caption as the body; the chapter imports
   `TDCSGFigureTheorems`.

An animation is a `Plane.MotionPanels` (one panel, or several on one clock) whose keys are drawn
as in step 2 and whose steps declare their moves, exactly (`exactStep`, with `moveTiming` for its
timing), with `pacing := motionPacing`, `checks := .fail`, `width := figureWidth` and
`narrowWidth := some narrowWidth`, marked `@[figure illustration]`; its captions, one per key,
carry no counter ("Step k of N" is added by the page). Draw each actor that moves at the exact
anchors its arrival check reads (one list for both, as `turningAnchors` does). State in a plain
theorem on the page of the figures' theorems that the figure is made of its keys and steps
(`by unfold name; with_reducible rfl`, which fails at once when they differ), what each key draws,
the anchors, the declared moves, that they arrive exactly (`allArrive … = true`) and each caption as
a function of its key's data; add it to `previews` and to `siteMotions` in
`TDCSGTests/Motions.lean`, whose `engineErrors`, run compiled by `lake test`, requires that
PILean's engine finds no error in it, and
show it with `:::figure TDCSGFigures.name (label := "…") (alt := "…")`. An animation that replaces
a figure with a linked theorem keeps its name and label, ends on that figure, at its size (and
shows it as its poster), and keeps its theorem linked, as above.

Where what a figure draws changes with a parameter (the radius of the orbit of zero,
`TDCSGFigures.orbitRadius`, and of the lens, `TDCSGFigures.Lens.lensRadius`), the actors whose
drawing changes are declared to morph, and the motion gives the exact pictures between two keys
(`Motion.between`, sampled `morphSamples` times per step); the browser interpolates only between
consecutive samples. Points that come with a key and stay are one group, an actor that appears
once and never moves. Such an animation has no narrow rendition when the narrow width would bring
its points closer than the layout checks allow (the orbit at the critical radius); a picture of
panels side by side has one.

### The frame pair for other words

The two frames of chapter 4 are computed by `TDCSGFigures.Lift.statesFor` in
`TDCSGFigures/Data/Frames.lean` for any squared radius in `ℚ(√5)`, starting point of `ℤ[ζ₅]` and
word in `a`, `b`, `a⁻¹`, `b⁻¹`. `stepsHold` checks the geometry of every step exactly; the general
statements are `TDCSG.Five.framePicture_genA_genB`, `framePicture_symm`, `two_mul_sub_proj_genA`,
`two_mul_sub_proj_genB`, `halved_genA` and `halved_genB`. `wordReport` lists, letter by letter,
whether a letter acts and the exact margin of its disk's centre against the window, and how far the
orbit reaches in both frames; `wordSummary` collects what a pin states. The figure's word is pinned
in `TDCSGFigures/Lift.lean`, other words in `TDCSGTests/FrameWords.lean`, which `lake test` builds.
`scripts/FrameWords.lean`, outside every build, searches the words in `a` and `b` at `r = 1.95` for
words with letters that do not act and for words whose orbit closes:

```sh
lake env lean scripts/FrameWords.lean
```

`TDCSGFigures/FramePair.lean` draws the two frames as key figures for any word and radius
(`FramePairConfig`, whose defaults are the figure): one key per state, and for a letter that does
not act one more key, which shows its ring before the state's own key, so that the ring appears
and vanishes while nothing turns. `FramePairConfig.actorsAt` lists, for each panel and key, every
moving item (an actor) with its id, its kind of drawing, its stable base title and its exact
anchor points; the key figures draw the actors from it, and `allArrive` checks against the same
list that each declared turn of `frameSteps`, in each panel's own coordinates, carries key `k` onto
key `k + 1` exactly. `TDCSGFigures/FramePairMotion.lean` makes the keys a PILean `MotionPanels`,
the two panels side by side in one SVG on one clock (stacked at the narrow width). The pins of
other words are in `TDCSGTests/FramePair.lean`. To look at the frame pair of another word
(outside the repository; nothing goes into the site):

```sh
lake exe tdcsg-figure-preview --frame-pair aababb --out DIR
```

writes its animated SVG (light and dark) and its key stills, wide and narrow, prints the engine's
errors and notes and whether every declared move arrives exactly, and exits with status 1 if one
fails.

### Drawing figures in a worktree

The folder `figures/` is a small Lake workspace that builds `TDCSGFigures` and the preview tool
without Mathlib and Verso, against the PILean package of the main checkout. In a git worktree,
give it its own copy of that package first. On macOS `cp -c` makes an APFS clone: it takes no
disk space and no time, nothing is downloaded, and builds in the worktree write only into the
worktree's copy, so several worktrees can build at the same time without sharing a build folder.

```sh
git worktree add -b figure-NAME ../TDCSG-wt-NAME figures
cd ../TDCSG-wt-NAME
mkdir -p .lake/packages
cp -cR ../TDCSG/.lake/packages/pilean .lake/packages/pilean   # from the main checkout
cd figures
lake build                                       # TDCSGCompute and TDCSGFigures
lake exe tdcsg-figure-preview --out out NAME     # every figure when no NAME is given
```

The preview tool writes `out/NAME[-narrow][-dark].{svg,png}` (light, dark, narrow and narrow
dark; for an animation its animated SVG and `NAME[-narrow]-key-K.{svg,png}`) and prints every layout problem of the figure at both
widths, whatever its checks level; it exits with status 1 when there is one. The site build
applies the same checks. `figures/lean-toolchain` must name the toolchain of
the root `lean-toolchain`. The specification theorems are not part of this workspace: they live on
the page `TDCSGFigureTheorems`, which needs Verso, and `lake build TDCSGBlueprint` checks them.

## Dependencies

The repository pins the fork of Verso Blueprint, the forks of Verso and SubVerso it builds on,
PILean (`pilean`, and its Verso and LeAnTeX adapters `pilean-verso` and `pilean-leantex`, all at
one PILean commit), Mathlib and their dependencies in `lakefile.toml` and `lake-manifest.json`.
Verso, SubVerso and PILean are pinned at the commits the fork itself pins; the root requires
Verso and SubVerso before the fork so that the workspace uses these revisions, `pilean` because
`TDCSGFigures` imports PILean directly, and Mathlib last so that its revisions of the packages it
shares with the fork (ProofWidgets, Plausible) win. When moving the fork, move these pins with it,
one package at a time, and keep Mathlib's shared package revisions.

GitHub Actions supplies `verification.json` after its Linux comparator run succeeds. A local
render remains usable without that file. See the
[standalone challenge](../Comparator/FiveDisk/Challenge.lean) and
[solution](../Comparator/FiveDisk/Solution.lean).
