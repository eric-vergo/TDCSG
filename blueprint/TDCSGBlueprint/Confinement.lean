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

#doc (Manual) "Confinement" =>

%%%
tag := "confinement"
%%%

This chapter completes Part II. It combines the good levels of Chapter 6 with a lemma about
graphs to show that every walk of Chapter 4 stays in a box of integer labels whose size does not
depend on the starting point. With the description of orbit points by labels, this bounds every
orbit by one number, and the orbit-bound lemma, in its two-disk form {bpref "two_disk_finite"}[],
makes $`GG_5(r)` finite for every $`r<R`, where $`R=\sqrt{3+\varphi}`.

:::figure TDCSGFigures.Confinement.componentOfZero (label := "component-of-zero") (inline := true) (proves := TDCSGFigures.Confinement.componentOfZero_spec) (alt := "Eighteen labels inside a circular window joined by edges into a star-shaped cycle: dots for weight zero, squares for weight one; the labels 0 and e0 lie on the horizontal axis through the window center.")
The component of the label $`0` in the center graph for $`x=1/2` and $`r=1.95`: 18 labels, each
drawn at its projection $`P(n)` inside the window $`|w-x|\le r/2`, dots for weight zero (the left
centers) and squares for weight one (the right centers); hovering over a label shows its integer
vector. The labels $`0` and $`e_0` of the two initial centers project to $`0` and $`1`; each edge
joins a weight-zero label $`n` to some $`n+e_j`, and segments that cross in the drawing do not meet
in the graph. Every label of the component has all coordinates in $`\{-1,0,1\}`. For each
coordinate $`j` the good levels $`lo\le-3` and $`hi\ge3` nearest $`0` are $`(lo,hi)=(-4,4)` for
$`n_0`, $`(-3,10)` for $`n_1`, $`(-7,6)` for $`n_2` and $`n_3`, and $`(-3,10)` for $`n_4`, so every
label lies strictly inside every slab $`lo<n_j\le hi`.
:::

Here the window is $`x=1/2` and $`r=1.95`. Starting at zero, enumerate the integer labels
of every retained neighbor until each has been visited. There are 18 labels in this component.
The weight-zero labels (dots) are left centers and the weight-one labels (squares) are right
centers; every edge joins one of each. Segments that cross in the drawing do not meet in the
graph: their crossing point is not a label, and each edge joins only its two endpoints, a
weight-zero label $`n` and a label $`n+e_j`. The window tests and the enumeration generate
{figref "component-of-zero"}[]. The theorem must also control every other starting point.

:::lemma_ "one_step" (lean := "SimpleGraph.Reachable.mem_or_exists_adj_of_leaf")
In a simple graph, let $`S` be a set of vertices that contains a vertex $`s` and all its
neighbors. Suppose that every edge from $`u\in S` to $`v\notin S` has a leaf endpoint: $`v` is
the only neighbor of $`u`, or $`u` is the only neighbor of $`v`. Then every vertex reachable
from $`s` lies in $`S` or is adjacent to a vertex of $`S`.
:::

:::proof "one_step"
Call a vertex of $`S` anchored if it is $`s` or has a neighbor in $`S`. Along a walk from $`s`,
every vertex in $`S` is anchored, because the walk reached it from $`s` or from a neighbor in
$`S`. Suppose the walk steps from an anchored $`u` to $`v\notin S`. Then $`u\ne s`, since all
neighbors of $`s` lie in $`S`. So $`u` has a neighbor in $`S`, which differs from $`v`, and the
hypothesis makes $`u` the only neighbor of $`v`. The next step returns to the anchored vertex
$`u`. Hence every vertex of the walk lies in $`S` or is a leaf hanging off a vertex of $`S`.
:::

:::lemma_ "slab_crossing" (lean := "TDCSG.Five.leaf_of_crossing") (uses := "active_graph, good_level, terminal_crossing")
Let $`0\le r<R`, and let $`lo` and $`hi` be good levels of coordinate $`j`. Every edge of the
center graph from a label $`n` with $`lo<n_j\le hi` to a label outside this slab has a leaf
endpoint.
:::

:::proof "slab_crossing" (lean := "TDCSG.Five.isGoodLevel_of_crossing, TDCSG.Five.leaf_of_isGoodLevel")
An edge joins a weight-zero label $`m` to $`m+e_k`, so it changes only the coordinate $`k`, by
one. To leave the slab it must have $`k=j` and $`m_j\in\{lo,hi\}`, a good level. The crossing
lemma then removes every other neighbor of one endpoint.
:::

:::theorem "label_box" (lean := "TDCSG.Five.exists_abs_le_of_centerReach") (uses := "all_walls, slab_crossing, one_step")
Let $`0\le r<R`. There is a bound $`D` such that, for every window center $`x`, every label
reachable in the center graph has all coordinates of absolute value at most $`D`.
:::

:::proof "label_box" (lean := "TDCSG.Five.abs_sub_le_one_of_adj")
Take $`K` from the recurrence of good levels. In coordinate $`j`, choose a good level $`lo`
within $`K` of $`-K-3` and a good level $`hi` within $`K` of $`K+3`. Adjacent labels differ by
at most one in each coordinate, so the starting label, $`0` or $`e_0`, and its neighbors lie in
the slab $`lo<n_j\le hi`. By the two preceding lemmas, every reachable label lies in the slab or
next to it. Hence $`|n_j|\le 2K+4`, so $`D=2K+4` is a bound.
:::

In {figref "component-of-zero"}[] no edge crosses a good level, and the same holds for the
component of $`0` at the window of {figref "terminal-crossing"}[] ($`r=2.12`, $`x=0.472`, 440 labels)
and at the window of {figref "level-phases"}[] ($`r=1.8`, $`x=0.87`): there the walks from $`0` never
meet a wall at all. To watch a walk from $`0` meet a wall, {figref "walk-to-leaf"}[] uses another
window, $`r=2.13` and $`x=1/5`, where the component of $`0` has 131 labels and two of its edges cross
a good level; it follows one of them.

:::figure_explorer TDCSGFigures.Confinement.walkToLeaf (label := "walk-to-leaf") (proves := TDCSGFigures.Confinement.walkToLeaf_spec) (alt := "A numbered path of labels inside a circular window. Its last step reaches the label n on the window's edge; the other candidates of n lie outside the window and the walk can only step back.")
A path of the center graph at $`r=2.13`, $`x=1/5`, found by a breadth-first search from $`0`,
drawn step by step (labels numbered along the path, dots for weight zero, squares for weight one).
It lowers the coordinate $`n_2` from $`0` to $`-4`, then crosses the good level $`-5` into the label
$`n=(0,3,-5,4,-2)` at the window's edge. The other candidates $`n+e_k`, $`k\ne2`, lie outside the
window (open rings at the ends of dashed spokes), so $`n` is a leaf and the walk can only step back
to $`n+e_2`, as the one-step lemma requires.
:::

:::lemma_ "box_finite" (lean := "TDCSG.finite_of_orbit_subset_insert_image") (uses := "group_orbit, two_disk_finite")
Let $`T` be a finite set, and for each point $`z` let $`f_z` be a map from $`T` to the plane. If
the orbit of every point $`z` lies in $`\{z\}\cup f_z(T)`, then $`GG_5(r)` is finite. The Lean
lemma holds for the two-disk group of any orders and radii.
:::

:::proof "box_finite"
Every orbit then has at most $`|T|+1` points, and uniformly bounded orbits make the group
finite.
:::

:::theorem "subcritical" (lean := "TDCSG.Five.finite_GG_of_lt") (uses := "label_box, words_walks, box_finite, two_disk_support, disjoint_disks")
The group $`GG_5(r)` is finite for every $`r<R`.
:::

:::proof "subcritical"
For $`r<0` the group is finite by the case of radii below one in Chapter 2. For $`0\le r<R` take the bound
$`D` of the label box. Let $`T` consist of the triples $`(c,j,n)` with $`c=\pm1`, a direction
$`j` and a label $`n` with $`|n_k|\le D`, and put $`f_z(c,j,n)=c+2((z+1)/2-P(n))/\zeta^j`. A
point outside both disks is fixed by the whole group. A point inside one disk keeps its whole
orbit inside the two disks, and the passage from words to walks writes each orbit point as $`f_z` of a triple
whose label is reachable and hence lies in the box.
:::

This proves the finite half of the main theorem. Chapter 8 combines it with the infinite half of
Part I.
