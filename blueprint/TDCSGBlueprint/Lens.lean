/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.FiveSharp

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Where the lens stops" =>

%%%
tag := "lens"
%%%

![At the critical radius the rightmost intersection of two disks lies on the vertical cut. At radius 1.8 the rightmost intersection lies strictly to its left.](/figures/lens.svg)

Suppose two different center changes are possible. Rotate the coordinates so the crossing
direction is horizontal. Their simultaneous tests put a vector $`v` in two disks of radius
$`r/2`, centered at 0 and a unit vector $`u`. The shaded overlap is the lens. The relevant
horizontal components of $`u` are $`c=(\varphi-1)/2` and $`d=-\varphi/2`. The drawing uses the
tighter case $`u=\zeta`, with real part $`c`.

:::lemma_ "sharp_lens" (lean := "TDCSG.Five.Walls.lens") (uses := "active_graph")
Put $`L=c-d` and $`a=(1+L)/2`. If $`0\le r<R`, $`|v|\le r/2`, and
$`\operatorname{Re}(v)\ge a-(3+\varphi-r^2)/16`, then $`|v-u|>r/2`.
:::

:::proof "sharp_lens"
For real part $`c`, take a weighted sum of the two squared disk inequalities, with weights
$`1-t` and $`t`, where $`t=1/2-c`. Completing squares gives the bound on the horizontal
coordinate. For real part $`d`, the horizontal distance from the second center already
exceeds the available radius. The strict margin is positive exactly below $`R`.
:::

At equality the two circles meet at $`v=1+t u` with real part $`a`. Shrinking the circles opens
a gap even after the vertical cut moves left by $`(3+\varphi-r^2)/16`. This gap supplies the
room needed to choose integer-coordinate walls.
