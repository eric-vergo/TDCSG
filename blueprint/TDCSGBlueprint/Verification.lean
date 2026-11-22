/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoBlueprint
import Comparator.Solution

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Checking the independent statement" =>

%%%
tag := "verification"
%%%

The challenge defines the two permutations of the complex plane directly from their disk
actions. It asks three questions using only these definitions, the radical
$`\sqrt{3+(1+\sqrt5)/2}`, and Mathlib. The solution identifies that action with the
formal development and proves each statement. Open the Lean panel to compare the precise
statements with the results of the geometric argument.

:::theorem "challenge_finite" (lean := "FiveDisk.finite_iff") (uses := "classification")
The permutation group is finite precisely below the stated radical.
:::

:::theorem "challenge_endpoint" (lean := "FiveDisk.infinite_orbit_zero") (uses := "endpoint_infinite")
Exactly at the radical, the orbit of zero is infinite.
:::

:::theorem "challenge_supremum" (lean := "FiveDisk.supremum_finite") (uses := "classification")
The supremum of the radii for which the group is finite equals the radical.
:::

The {ref "chord"}[chord construction] gives the stronger orbit statement for every radius
at or above the threshold. The independent orbit challenge asks for the boundary case.

*Independent replay*

Each successful hosted build provides a verification record identifying the commit, Actions run,
toolchain, kernel checks and theorem names. The [site home](/index.html) and the
[Actions history](https://github.com/eric-vergo/TDCSG/actions) are available independently.
A local preview can be viewed without a hosted verdict. The Project Stats page describes what the blueprint
inspected in its compiled declarations. The release workflow separately runs the comparator
on Linux and publishes its verdict with the site.

Read the [standalone challenge](https://github.com/eric-vergo/TDCSG/blob/main/Comparator/Challenge.lean),
[solution](https://github.com/eric-vergo/TDCSG/blob/main/Comparator/Solution.lean), and
[allowed axioms](https://github.com/eric-vergo/TDCSG/blob/main/comparator.json). The challenge
compares formal statements. Checking how those statements express the intended mathematical
problem also requires reading their definitions.

# Software and typeface credits

Verso and the cited Verso Blueprint modules credit Lean FRO LLC and their respective
authors under the [Apache License 2.0](/Apache-2.0.txt). The
[Blueprint source](https://github.com/eric-vergo/verso-blueprint/tree/9fa92b2bf1d3bf2071963157e077b011666c435d)
includes the individual file credits. PILean draws the geometric plates. LeAnTeX
typesets the formulas with glyph outlines from Antonis Tsolomitis’s New Computer Modern.
The selected fonts carry the GUST Font License. See the
[font package notice](/NewCM-license.txt) and the [LaTeX Project Public License](/LPPL-1.3c.txt).

The browser math renderer also distributes the [KaTeX font license](/notices/KaTeX-fonts-LICENSE.txt).

The search interface includes third-party software. Read its [original notices](/search-notices.txt).
Verso records the following licenses for the components used by this manual.

{licenseInfo}
