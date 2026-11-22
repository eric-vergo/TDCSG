/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.FiveSharp

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Two disks and a fifth-turn" =>

%%%
tag := "disks"
%%%

![Two overlapping closed disks centered at minus one and one. The segment from the left center to zero turns clockwise through 72 degrees.](/figures/disks.svg)

Choose a point in the plane. Applying the left generator turns it clockwise through 72 degrees if
it belongs to the left disk, including the boundary. Outside that disk the point stays put. The
right generator uses the same rule about the other center. In the picture the radius is 1.5 and
the marked point is zero. It belongs to both disks, so the choice of generator matters.

:::definition "disk_rotation" (lean := "TDCSG.diskRotation")
For a center $`c` and order $`n`, the active rule sends $`z` to
$`c+\exp(-2\pi i/n)(z-c)`. The test is $`|z-c|\le r`.
:::

:::definition "group_orbit" (lean := "TDCSG.GG, TDCSG.orbit") (uses := "disk_rotation")
The generators with centers $`-1` and $`1` generate a group of permutations of the whole plane.
The orbit of $`z` consists of the images of $`z` under all finite words, including inverses.
:::

At order five, let $`R=\sqrt{3+\varphi}`, where $`\varphi=(1+\sqrt5)/2`. The radius in the
picture lies below $`R`. Every word then belongs to a finite group. At $`R` itself, even the single
point zero has an infinite orbit. The next four chapters explain how the finiteness proof finds
a uniform bound. The last geometric chapter shows why that bound stops at exactly $`R`.
