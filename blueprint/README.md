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

The front page and the geometric chapters show SVG figures generated from
`blueprint/TDCSGBlueprint/Figures.lean` by the PILean revision in the Blueprint
dependency manifest. The file `figures/SHA256SUMS` in the site
records the bytes of the generated figures. The geometry runs in Lean using
floating-point drawing coordinates. The proof uses exact real, complex and
integer arithmetic in the linked declarations.

The graph uses the dependency labels of the chapter statements. Set
`(lean := "...")` to the declaration being described and `(uses := "...")` to
the nodes whose declarations its Lean proof uses. Helper lemmas of a proof go in
`(lean := "...")` on its `:::proof` block. The generator enables the fork's side-by-side
source view. The challenge and solution declare the same constants and must be
elaborated separately. The verification chapter imports only the solution.

The repository pins the fork, PILean, Mathlib and their dependencies in
`lake-manifest.json`. Keep Mathlib's shared package revisions when updating the
documentation dependencies. GitHub Actions supplies `verification.json` after
its Linux comparator run succeeds. A local render remains usable without that
file. See the [standalone challenge](../Comparator/Challenge.lean) and
[solution](../Comparator/Solution.lean).
