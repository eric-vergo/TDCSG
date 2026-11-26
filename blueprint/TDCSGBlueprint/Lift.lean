/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoManual
import VersoBlueprint
import PILeanVerso
import TDCSGFigureTheorems
import TDCSG.CriticalRadius.Five

open Verso.Genre Verso.Genre.Manual Informal PILeanVerso

#doc (Manual) "Lift to integer labels" =>

%%%
tag := "lift"
%%%

This chapter opens Part II, the proof that $`GG_5(r)` is finite for every $`r<\sqrt{3+\varphi}`.
It replaces the orbit of a point by a combinatorial object: walks in a graph on integer vectors.
Its theorem writes every orbit point inside the two disks in terms of a reachable vertex of this graph, so that a bound
on the reachable vertices, proved in Chapter 7, bounds the orbit.

:::figure TDCSGFigures.Lift.unitSteps (label := "unit-steps") (inline := true) (links := TDCSGFigures.Lift.unitSteps_spec) (alt := "A circular window about x = 1/2 and five unit steps from the point 0. The steps to 1, zeta and zeta to the fourth end inside the window as filled markers; the steps to zeta squared and zeta cubed are dashed and end outside it as open rings.")
The window $`|w-x|\le r/2` (shaded) at $`x=1/2` (the cross), $`r=1.95`, and the five unit steps
from the current left center $`0` to the projections $`\zeta^j=P(e_j)` of the labels $`e_j`. The
steps to $`1`, $`\zeta` and $`\zeta^4` end in the window (solid, ending in filled markers) and can
act; those to $`\zeta^2` and $`\zeta^3` end outside it (dashed, ending in open rings). Notice that
the ends $`\zeta` and $`\zeta^4` lie only just inside, at distance about $`0.970` from $`x`
against $`r/2=0.975`.
:::

The transformation $`x=(z+1)/2` sends the two original centers to 0 and 1 and halves all distances.
Follow the rotations in a moving frame. Its orientation has just five possibilities. A change of
active center moves one unit in a direction $`\zeta^j`, where $`\zeta=\exp(2\pi i/5)`. The point
$`x` stays fixed. To decide whether a center can act, ask whether it lies within $`r/2` of $`x`.

From here on the letter $`n` denotes a label, an integer vector, and the order of the rotations
is fixed at $`5`.

:::definition "center_projection" (lean := "TDCSG.Five.dir, TDCSG.Five.Label, TDCSG.Five.Label.basis, TDCSG.Five.Label.proj, TDCSG.Five.Label.weight")
Record a center by an integer vector $`n=(n_0,\ldots,n_4)`, its label. Its position in the
halved starting frame is
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
Lean calls the center graph `TDCSG.Five.centerGraph`.
:::

:::theorem "words_walks" (lean := "TDCSG.Five.Framed, TDCSG.Five.framed_of_mem_orbit, TDCSG.Five.exists_centerReach_of_mem_orbit") (uses := "group_orbit, generated_by_two, active_graph, unit_step")
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
changes nothing. Each generator has order five, so its inverse is a power of it, and since the
group is generated by $`a` and $`b` the invariant holds on the whole orbit. Solving the framing equation of the active center for
$`y` gives the formula.
:::

The proof's invariant has a picture. The rigid motion $`T(w)=P(n)+\zeta^jw` sends the halved
starting frame onto the moving frame: the halved centers $`0` and $`1` go to $`P(n)` and
$`P(n+e_j)`, and the halved point $`(y+1)/2` goes to $`x`. A letter that acts turns the point in
one frame and the pair of centers in the other.

:::lemma_ "frame_pair" (lean := "TDCSG.Five.framePicture_genA_genB, TDCSG.Five.halved_genA, TDCSG.Five.halved_genB, TDCSG.Five.frameMap_succ_zeta_pow_four_mul, TDCSG.Five.frameMap_add_basis_sub_basis_succ") (uses := "center_projection, unit_step")
Let $`y` be framed by $`(n,j)`, that is $`2(x-P(n))=\zeta^j(y+1)`, and let $`T_{n,j}(w)=P(n)+\zeta^jw`.
Then $`T_{n,j}` sends $`0`, $`1` and $`(y+1)/2` to $`P(n)`, $`P(n+e_j)` and $`x`. If $`a` acts at
$`y`, the halved point turns about $`0` by $`\zeta^4`, a fifth of a turn clockwise, and
$`T_{n,j+1}` sends the new picture onto $`P(n)`, $`P(n+e_{j+1})` and $`x` again: in the moving
frame the left center stays and the right center turns about it by a fifth of a turn
counterclockwise. If $`b` acts, the same holds about $`1` and the right center, with the frame
$`(n+e_j-e_{j+1},j+1)`. A letter that does not act fixes $`y` and the frame.
:::

:::proof "frame_pair"
The images of $`0` and $`1` are $`P(n)` and $`P(n)+\zeta^j=P(n+e_j)`, and $`T_{n,j}((y+1)/2)=x` is
the framing equation divided by two. A turn of the halved point by $`\zeta^4` about $`0` composed
with $`T_{n,j+1}` is $`T_{n,j}`, since $`\zeta^{j+1}\zeta^4=\zeta^j`; about $`1` the same holds
with the label $`n+e_j-e_{j+1}`. So the updated motion sends the turned picture to the same three
points of the moving frame, with the turned center in place of the old one.
:::

:::figure TDCSGFigures.Lift.framePair (label := "frame-pair") (alt := "Two panels on one clock. Left: two disks about 0 and 1, fixed, and a point that turns by fifths about the center of one of them. Right: a fixed window about x = 1/2 with a point at x, and a pair of centers with disks riding on them that turns by fifths about one of the centers. Some letters do not act; then a ring marks a center and nothing moves.")
The word $`aababaabbabb` applied to $`z=0` at $`r=1.95`, in both frames on one clock. Left, the
traditional view, halved by $`w\mapsto(w+1)/2`: the disks about $`0` and $`1` stay, and the point
$`(y+1)/2` turns a fifth of a turn clockwise about the center of the disk of each letter that
acts. Right, the moving frame of the proof: the window about $`x=1/2` and the point at $`x` stay,
and the pair of centers $`P(n)` and $`P(n+e_j)`, with the halved disks riding on them, turns a
fifth of a turn counterclockwise about the active center, so the other center takes a unit step.
The letters 3, 5 and 10 do not act: a ring marks the center of their disk while nothing moves. In
the moving frame that center lies outside the window, exactly when the point lies outside the
disk, as the framing equation requires.
:::

The key frames of {figref "frame-pair"}[] are exact: each is drawn from the states of the word
computed in $`\mathbb Z[\zeta]`, and each turn of a fifth carries one key frame onto the next,
as {bpref "frame_pair"}[] says. Between two key frames the browser turns the drawn items about the
stated center.

For the window of {figref "unit-steps"}[], $`x=1/2` and $`r=1.95`, three of the five neighbors of
zero are inside.
The center graph keeps precisely these three edges at zero. Which other edges survive
depends on their own centers. The next chapter studies a pair of simultaneous disk tests.
