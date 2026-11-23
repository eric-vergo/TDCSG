/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.Five

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Two disks and a fifth-turn" =>

%%%
tag := "disks"
%%%

![Two overlapping closed disks centered at minus one and one. The segment from the left center to zero turns clockwise through 72 degrees.](/figures/disks.svg)

Choose a point in the plane. The left generator $`a` turns it clockwise through 72 degrees about
$`-1` if it belongs to the closed disk about $`-1`, including the boundary. Outside that disk the
point stays put. The right generator $`b` uses the same rule about $`1`. In the picture the radius
is 1.5 and the marked point is zero. It belongs to both disks, so the choice of generator matters.

:::definition "disk_rotation" (lean := "TDCSG.diskRotation, TDCSG.genA, TDCSG.genB")
For a center $`c`, order $`n` and radius $`r`, the disk rotation sends $`z` to
$`c+\exp(-2\pi i/n)(z-c)` if $`|z-c|\le r`, and fixes $`z` otherwise. The generators $`a` and
$`b` are the disk rotations about $`-1` and $`1`.
:::

:::definition "group_orbit" (lean := "TDCSG.GG, TDCSG.GG_eq_closure, TDCSG.orbit") (uses := "disk_rotation")
The generators $`a` and $`b` generate a group $`GG_n(r)` of permutations of the whole plane.
The orbit of $`z` consists of the images of $`z` under all finite words in $`a`, $`b` and their
inverses.
:::

:::definition "critical_radius_def" (lean := "TDCSG.infiniteRadii, TDCSG.criticalRadius") (uses := "group_orbit")
The critical radius of order $`n` is the infimum of the radii $`r` at which $`GG_n(r)` is
infinite.
:::

:::lemma_ "critical_radius_of_iff" (lean := "TDCSG.criticalRadius_eq_of_forall_finite_iff") (uses := "critical_radius_def")
If $`GG_n(r)` is finite exactly for $`r<r_0`, then the critical radius of order $`n` is $`r_0`.
:::

:::proof "critical_radius_of_iff"
The radii with an infinite group are then the closed half-line $`[r_0,\infty)`, whose infimum
is $`r_0`.
:::

:::lemma_ "infinite_of_orbit" (lean := "TDCSG.infinite_GG_of_infinite_orbit") (uses := "group_orbit")
If some point has an infinite orbit, the group is infinite.
:::

:::proof "infinite_of_orbit"
The orbit of $`p` is the image of the group under $`g\mapsto g(p)`. The image of a finite
group is finite.
:::

At order five, let $`R=\sqrt{3+\varphi}`, where $`\varphi=(1+\sqrt5)/2`. The radius in the
picture lies below $`R`. Every word then belongs to a finite group. At $`R` itself, even the single
point zero has an infinite orbit. The next four chapters explain how the finiteness proof finds
a uniform bound. The last geometric chapter shows why that bound stops at exactly $`R`.
