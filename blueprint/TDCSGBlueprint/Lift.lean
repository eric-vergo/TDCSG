/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.Five

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

:::definition "center_projection" (lean := "TDCSG.Five.dir, TDCSG.Five.Label, TDCSG.Five.Label.basis, TDCSG.Five.Label.proj, TDCSG.Five.Label.weight")
Record a center by an integer vector $`n=(n_0,\ldots,n_4)`, its label. Its position is
$`P(n)=\sum_j n_j\zeta^j` and its weight is $`\sum_j n_j`; both are additive in $`n`. Write
$`e_j` for the coordinate vectors. Keep the integer vector: a bounded region of the physical
plane alone does not bound its integer coordinates.
:::

:::lemma_ "unit_step" (lean := "TDCSG.Five.Label.proj_basis, TDCSG.Five.Label.weight_basis") (uses := "center_projection")
The label $`e_j` projects to $`\zeta^j` and has weight one. So adding $`e_j` to a label adds the
unit vector $`\zeta^j` to its projection and one to its weight.
:::

:::proof "unit_step"
The sums defining $`P(e_j)` and the weight of $`e_j` have the single nonzero term $`\zeta^j`,
respectively $`1`. Additivity gives the second sentence.
:::

:::definition "active_graph" (lean := "TDCSG.Five.InWindow, TDCSG.Five.CenterEdge, TDCSG.Five.centerGraph, TDCSG.Five.CenterReach") (uses := "center_projection")
Fix the radius $`r` and the window center $`x`. A label $`n` lies in the window when
$`|P(n)-x|\le r/2`. The center graph joins a weight-zero label $`n` to $`n+e_j` when both lie
in the window. It is a simple graph, so paths may traverse an edge either way. A label is
reachable when a path joins it to $`0` or $`e_0`, the labels of the two initial centers.
:::

:::theorem "words_walks" (lean := "TDCSG.Five.Framed, TDCSG.Five.framed_of_mem_orbit, TDCSG.Five.exists_centerReach_of_mem_orbit") (uses := "group_orbit, active_graph, unit_step")
Let $`x=(z+1)/2`. Every point $`y` of the orbit of $`z` that lies in one of the two closed disks
has the form $`y=c+2(x-P(n))/\zeta^j` for a center $`c\in\{-1,1\}`, a direction $`j` and a
label $`n` that is reachable in the center graph.
:::

:::proof "words_walks"
Carry an invariant along the orbit. The current point $`y` is framed by a weight-zero label
$`n` and a direction $`j` with $`2(x-P(n))=\zeta^j(y+1)`, so that $`2(x-P(n+e_j))=\zeta^j(y-1)`.
Thus $`n` and $`n+e_j` label the current left and right centers, and each of them that lies in
the window is reachable. The point $`z` is framed by $`n=0` and $`j=0`.

If $`a` acts at $`y`, then $`y` lies in the left disk, so $`n` lies in the window. The left
label stays, $`j` increases by one, and the new right label $`n+e_{j+1}` is joined to $`n` by an
edge whenever it lies in the window. If $`b` acts, the right label $`n+e_j` stays and the new
left label $`n+e_j-e_{j+1}` is joined to it in the same way. A generator that does not act
changes nothing. Each generator has order five, so its inverse is a power of it and the
invariant holds on the whole orbit. Solving the framing equation of the active center for
$`y` gives the formula.
:::

For the illustrated window $`x=1/2`, $`r=1.95`, three of the five neighbors of zero are inside.
The active-center graph keeps precisely these three edges at zero. Which other edges survive
depends on their own centers. The next chapter studies a pair of simultaneous disk tests.
