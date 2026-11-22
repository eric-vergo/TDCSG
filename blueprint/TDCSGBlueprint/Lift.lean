/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.FiveSharp

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Keep the point fixed and move its centers" =>

%%%
tag := "lift"
%%%

![Five unit directions from zero with a circular window centered at one half. Blue segments reach retained neighbors. Gray segments leave the window.](/figures/moving.svg)

The transformation $`x=(z+1)/2` sends the two original centers to 0 and 1 and halves all distances.
Follow the rotations in a moving frame. Its orientation has just five possibilities. A change of
active center moves one unit in a direction $`\zeta^j`, where $`\zeta=\exp(2\pi i/5)`. Now $`x`
stays fixed. To decide whether a center can act, ask whether it lies within $`r/2` of $`x`.

:::definition "center_projection" (lean := "TDCSG.Five.Walls.Label, TDCSG.Five.Walls.proj, TDCSG.Five.Walls.weight") (uses := "disk_rotation")
Record a center by an integer vector $`n=(n_0,\ldots,n_4)`. Its position is
$`P(n)=\sum_j n_j\zeta^j` and its weight is $`\sum_j n_j`. Keep the integer vector: a bounded
region of the physical plane alone does not bound its integer coordinates.
:::

:::lemma_ "unit_step" (lean := "TDCSG.Five.Walls.proj_add, TDCSG.Five.Walls.proj_basis") (uses := "center_projection")
Adding the coordinate vector $`e_j` to a label adds the unit vector $`\zeta^j` to its projection.
:::

:::definition "active_graph" (lean := "TDCSG.Five.Walls.CenterEdge, TDCSG.Five.Walls.CenterReach") (uses := "unit_step")
An edge joins a weight-zero label $`n` to $`n+e_j` when both projections lie in the same closed
window. Retained paths may traverse an edge either way. Start from the zero label or $`e_0`,
the labels of the two initial centers.
:::

For the illustrated window $`x=1/2`, $`r=1.95`, three of the five neighbors of zero are inside.
The active-center graph keeps precisely these three edges at zero. Which other edges survive
depends on their own centers. The next chapter studies a pair of simultaneous disk tests.
