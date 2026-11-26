# Building the fivefold blueprint

From the repository root, with the Lean version in `lean-toolchain`, run

```sh
lake build TDCSGBlueprint
lake exe vbp build
lake exe vbp check
python3 -m http.server --directory _out/site/html-multi 8000
```

Open [the local site](http://localhost:8000/). The first command elaborates the
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

A chapter shows a figure with `:::figure` (inline, so that the picture follows the page's theme
and its elements link to Lean) or `:::figure_explorer` (a slider or stepper), with a label, a text
alternative, the theorem it proves and the caption as the body. Figures are numbered as the
Blueprint numbers its statements: "Figure 5.1" is the first figure of chapter 5, and the figures
of the unnumbered pages (the front page and the two part pages) are numbered 1 to 4. Prose refers
to a figure by its label, `{figref "lens-estimate"}[]`, which renders its current number.

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
name and gapless numbering, allows no other image in the pages, follows the Lean links, and runs
`lake exe pilean-verify`, the inline-picture check of PILean's Verso adapter and a fresh render of
the figures compared with the site's folder.

Chapter 3 progressively enhances the three PILean frames of `wordTrace` with a looping
illustration for each word. The player turns each rendered segment about the active center and
snaps to the next checked path at the end of the letter. The generator supplies the letters and
interval coordinates from Lean. The original numbered traces remain available in the chapter.
With reduced motion, each word has a labeled still for every turn.

With the site served locally and Playwright Core available to Node, run the browser check against
the site root (including its prefix if it has one):

```sh
node scripts/check-word-motion.cjs http://localhost:8000/
```

Set `CHROMIUM` to an installed Chromium executable when using a browser outside Playwright's cache.
The check compares both ends of every animated turn with the checked PILean paths, follows the
chapter links and exercises playback, offscreen suspension, mobile widths and reduced motion.

### Adding a figure

1. Put the exact data it needs in `TDCSGFigures/Data.lean` or `TDCSGFigures/Data/` (points of
   `ℤ[ζ₅]` as `PILean.Exact.Zeta5`, reals of `ℚ(√5)` as `QSqrt5`, radii as `Rat` or
   `SqrtOf QSqrt5`, orbits through `TDCSGFigures.orbit`), with a `#guard` for every property its
   caption states.
2. Draw it in the module of its chapter (`TDCSGFigures/<Chapter>.lean`, imported by
   `TDCSGFigures.lean`) as a `Plane.Figure` (or an `Explorer` made with `Plane.slider` or
   `Plane.stepper`) in `houseStyle` (`partTwoStyle`, `radiusStyle` for their roles), with
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
   (links := TDCSGFigures.name_spec) (alt := "…")` or `:::figure_explorer`, the caption as the
   body; the chapter imports `TDCSGFigureTheorems`.

### The frame pair for other words

The two frames of chapter 4 (`changeOfFrame`) are computed by `TDCSGFigures.Lift.statesFor` in
`TDCSGFigures/Data/Frames.lean` for any squared radius in `ℚ(√5)`, starting point of `ℤ[ζ₅]` and
word in `a`, `b`, `a⁻¹`, `b⁻¹`. `stepsHold` checks the geometry of every step exactly; the general
statements are `TDCSG.Five.framePicture_genA_genB`, `framePicture_symm`, `two_mul_sub_proj_genA`,
`two_mul_sub_proj_genB`, `halved_genA` and `halved_genB`. `wordReport` lists, letter by letter,
whether a letter acts and the exact margin of its disk's centre against the window, and how far the
orbit reaches in both frames; `wordSummary` collects what a pin states. The figure's word is pinned
in `TDCSGFigures/Lift.lean`, other candidate words in `TDCSGTests/FrameWords.lean`, which
`lake test` builds. `scripts/FrameWords.lean`, outside every build, searches the words in `a` and
`b` at `r = 1.95` for words with letters that do not act and for words whose orbit closes:

```sh
lake env lean scripts/FrameWords.lean
```

`TDCSGFigures/FramePair.lean` draws the two frames as key figures for an animation, one pair per
rest of a word. `FramePairConfig.actorsAt` lists, for each panel and key, every moving item (an
actor) with its id, its kind of drawing, its stable base title and its exact anchor points; the
key figures (`halvedKey`, `centreKey`, in their views with legends by `keys`) draw the actors from
it, and `allArrive` checks against the same list that each declared turn of `frameSteps`, in each
panel's own coordinates, carries key `k` onto key `k + 1` exactly. The words' pins are in
`TDCSGTests/FramePair.lean`. The variants: the word and radius, the right panel (`R1` centres with
riding disks, `R2` centres and edge, `R3` with the centre-graph edge), trails (dots, or arcs of the
paths the centres swept), a full-size left panel, the mark of an idle letter (a dashed outline over
its disk, or a ring about its centre) and the views (both panels of one width, each cropped to its
extent, or side by side with a wider right panel; one unit length throughout). To look at them
(outside the repository; nothing goes into the site):

```sh
lake exe tdcsg-figure-preview --frame-pair-keys DIR --word aababaabbabb --variant R3 --trails \
  --view wide-right
```

writes the keys of both panels (light, dark, narrow) and contact sheets `DIR/<variant>/sheet*.html`,
and prints the disks' diameters in pixels.

`TDCSGFigures/FramePairMotion.lean` animates the keys: `FramePairConfig.motion` is a PILean
`MotionPanels`, the two panels side by side in one SVG on one clock, one step per letter, the
moves those of `frameSteps` (the point turns in the left panel, the body of centres in the
right, idle marks and trails fade in and out), checked by PILean's engine (arrival within 0.01 px,
the rests against the key stills, the written SVG against the baked frames, nothing leaving its
panel while it turns). The exact pins above say that the declared moves carry each key onto the
next; the engine's checks say that the picture draws those moves. To compare the variants in
motion and choose a pacing (outside the repository; nothing goes into the site):

```sh
lake exe tdcsg-figure-preview --motion-variants DIR
```

writes one animated SVG per variant and rendition (wide, narrow, light, dark) at a canonical
pacing to `DIR/svg`, `DIR/variants.json`, and `DIR/index.html`, a page that plays the chosen
variant re-timed (turn, hold, idle step, first and last hold, seam, easing, speed), scrubs
through the loop, shows the stills, and prints the chosen values as Lean to copy. `DIR/check`
holds the files of PILean's browser check, `python3 tools/motion-browser-check.py DIR/check`
from a PILean checkout.

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

The preview tool writes `out/NAME[-frame-K][-narrow][-dark].{svg,png}` (light, dark, narrow and
narrow dark; each frame of an explorer as its slider shows it) and prints every layout problem
of the figure at both widths, whatever its checks level; it exits with status 1 when there is
one. The site build applies the same checks. `figures/lean-toolchain` must name the toolchain of
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
[standalone challenge](../Comparator/FiveDisk/Challenge.lean) and [solution](../Comparator/FiveDisk/Solution.lean).
