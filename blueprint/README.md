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
`blueprint/TDCSGBlueprint.lean`. Each geometric chapter begins with an SVG
generated from `blueprint/TDCSGBlueprint/Figures.lean` by the PILean revision
in the Blueprint dependency manifest. The file `figures/SHA256SUMS` in the site
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
