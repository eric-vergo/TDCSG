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

Two kinds of figures share one numbering, 1 to N in document order.

* **PILean figures** (the front page). Each is the value of a declaration with the attribute
  `@[figure]` in the library `TDCSGFigures` (`TDCSGFigures/`, one module per page or chapter,
  plus `Data`, the exact objects, and `Style`, the house style). The library imports PILean and
  the orbit engine `TDCSGCompute` only: no Mathlib, no Verso. The generator renders the figures
  a page uses with `PILeanVerso.withFigures` into `-verso-data/pilean-figures` with a manifest,
  fingerprints and the source record of each file, and fails the build when a figure with
  `checks := .fail` has a layout problem (at its full and its narrow width, in both themes).
  Under each figure the page shows its number and caption, then a source line: the declaration,
  its file and line linked to the repository at the build's commit, the fingerprint, and the
  theorem that states what it draws. Links to Lean declarations, in the source line and on the
  elements of an inline picture, lead to the declaration's row in the Lean panel of the
  Blueprint entry that names it (`leanLinks := .site`); the build warns about a declaration
  with no such place. The page `Figures` lists every figure.
* **Hand-drawn plates** (chapters 2 to 7). `blueprint/TDCSGBlueprint/Figures.lean` writes them as
  SVG in floating-point drawing coordinates to the site's `plates/` folder, with
  `plates/SHA256SUMS`; a plate is the image of a paragraph whose text is its caption, starting
  with `*Figure N.*`. Dark mode shows them inverted (`blueprint/figures.css`).

`scripts/check-pages.py` checks both kinds; for PILean figures it reads the manifest, requires a
visible numbered caption and an accessible name, follows the Lean links, and runs
`lake exe pilean-verify`, the inline-picture check of PILean's Verso adapter and a fresh render
of the figures compared with the site's folder.

### Adding a figure

1. Put the exact data it needs in `TDCSGFigures/Data.lean` (points of `ℤ[ζ₅]` as
   `PILean.Exact.Zeta5`, reals of `ℚ(√5)` as `QSqrt5`, radii as `Rat` or `SqrtOf QSqrt5`, orbits
   through `TDCSGFigures.orbit`), with a `#guard` for every property its caption states.
2. Draw it in the module of its chapter (`TDCSGFigures/<Chapter>.lean`, imported by
   `TDCSGFigures.lean`) as a `Plane.Figure` (or an `Explorer` made with `Plane.slider` or
   `Plane.stepper`) in `houseStyle`, with `checks := .fail`, `width := figureWidth` and
   `narrowWidth := some narrowWidth`. Disks are outlines (`noFill`), the lens a region of its
   own (`role lensRole`), the left disk and what belongs to it `role leftRole`, the right
   `role rightRole`; every point, disk, centre, radius and region has a title (`named`) and a
   label; a point near a curve records where it is (`incident`), decided exactly. Link elements
   to the Lean declarations that state their facts with `declRef`, choosing declarations that
   have a Blueprint entry.
3. Mark it `@[figure]`, write its specification theorem `<name>_spec` with the item list written
   out and the exact facts proved by `rfl` and `decide +kernel` (see
   `TDCSGFigures.criticalChord_spec`), and attach it with `figure_proves`.
4. Add it to `previews` in `TDCSGFigures/Preview.lean`, look at the previews (below), and put it
   in its chapter with `:::figure TDCSGFigures.name (label := "…") (inline := true)
   (proves := TDCSGFigures.name_spec) (alt := "…")` or `:::figure_explorer`, the caption as the
   body. Remove the plate it replaces from `Figures.lean` and from `expected` in
   `scripts/check-pages.py`, and renumber the hand-written captions after it.

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
cp -cR /Users/eric/Github/TDCSG/.lake/packages/pilean .lake/packages/pilean
cd figures
lake build                                       # TDCSGCompute and TDCSGFigures
lake exe tdcsg-figure-preview --out out NAME     # every figure when no NAME is given
```

The preview tool writes `out/NAME[-frame-K][-narrow][-dark].{svg,png}` (light, dark, narrow and
narrow dark; each frame of an explorer as its slider shows it) and prints every layout problem
of the figure at both widths, whatever its checks level; it exits with status 1 when there is
one. The site build applies the same checks. `figures/lean-toolchain` must name the toolchain of
the root `lean-toolchain`.

## Dependencies

The repository pins the fork, PILean (`pilean`, and its Verso and LeAnTeX adapters
`pilean-verso` and `pilean-leantex`, all at one PILean commit), Mathlib and their dependencies in
`lake-manifest.json`. The root pin of `pilean` overrides the older one the fork requires. Keep
Mathlib's shared package revisions when updating the documentation dependencies: update the
PILean packages alone with `lake update pilean pilean-verso pilean-leantex`.

GitHub Actions supplies `verification.json` after its Linux comparator run succeeds. A local
render remains usable without that file. See the
[standalone challenge](../Comparator/Challenge.lean) and [solution](../Comparator/Solution.lean).
