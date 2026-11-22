/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.FiveSharp

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "From a component to a finite group" =>

%%%
tag := "confinement"
%%%

![All edges and 18 vertices of the projected example component, drawn inside the circular window.](/figures/component.svg)

Here the window is $`x=1/2` and $`r=1.95`. Starting at zero, enumerate the integer labels
of every retained neighbor until each has been visited. There are 18 labels in this component.
Blue vertices have weight zero and rust vertices have weight one. A line crossing away from a marked vertex does not create an edge in the label graph. The window tests and the
enumeration generate this picture. The theorem must also control every other starting point.

:::lemma_ "one_step" (lean := "TDCSG.Five.Walls.confined") (uses := "terminal_crossing")
Suppose each edge crossing out of a region has a terminal endpoint and the start and its
neighbors lie inside. Every reachable vertex is inside or immediately adjacent to the inside.
:::

:::proof "one_step"
Follow a path until it first leaves. Its inside endpoint already has a neighbor inside, so
the outside endpoint must be the leaf. The next step can only return along the same edge.
:::

:::theorem "label_box" (lean := "TDCSG.Five.Walls.CenterBox, TDCSG.Five.Walls.centerBox_of_walls") (uses := "all_walls, one_step")
Apply confinement between the two walls of each coordinate. Adding one to the common bound
contains all reachable labels in one finite integer box, uniformly over the permitted windows.
:::

:::lemma_ "uniform_orbits" (lean := "MulAction.finite_of_encard_orbit_le")
A finitely generated group acting faithfully on a set is finite if the sizes of all point
orbits share one finite bound.
:::

:::theorem "box_finite" (lean := "TDCSG.Five.Walls.finite_GG_of_centerBox") (uses := "label_box, group_orbit, uniform_orbits")
The label, one of five orientations, and a choice of left or right center determine the orbit
point in the moving frame. For $`r\le4` the uniform box bounds every orbit's size.
This uniform bound implies finiteness of the two-generator permutation group.
:::

:::proof "box_finite"
The orbit of any point outside both disks is a singleton. For a point inside, there are at
most ten frames per label. A finitely generated group has only finitely many permutation
actions on sets of bounded cardinality up to relabeling. The action on the plane is faithful,
so the product of these finite actions detects each group element.
:::

:::theorem "subcritical" (lean := "TDCSG.CriticalRadius.finiteBelowClosedFormFive") (uses := "all_walls, box_finite")
The group is finite for every $`r<R`. The wall argument covers $`0\le r<R`; at negative
radius both closed disks are empty.
:::
