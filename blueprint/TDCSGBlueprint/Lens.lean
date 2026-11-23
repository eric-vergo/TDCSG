/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.Five

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Where the lens stops" =>

%%%
tag := "lens"
%%%

![At the critical radius the rightmost intersection of two disks lies on the vertical cut. At radius 1.8 the rightmost intersection lies strictly to its left.](/figures/lens.svg)

Suppose two different center changes are possible. Rotate the coordinates so the crossing
direction is horizontal. Their simultaneous tests put a vector $`v` in two disks of radius
$`r/2`, centered at 0 and a unit vector $`u`. The shaded overlap is the lens. The relevant
horizontal components of $`u` are $`c_1=(\varphi-1)/2` and $`c_2=-\varphi/2`. The drawing uses
the tighter case $`u=\zeta`, with real part $`c_1`.

:::lemma_ "sharp_lens" (lean := "TDCSG.Five.div_two_lt_norm_sub_of_le_re")
Put $`L=c_1-c_2=\varphi-1/2` and $`\kappa=(1+L)/2=(2\varphi+1)/4`. Let $`0\le r<R` and let
$`u` be a unit vector with real part $`c_1` or $`c_2`. If $`|v|\le r/2` and
$`\operatorname{Re}(v)\ge \kappa-(3+\varphi-r^2)/16`, then $`|v-u|>r/2`.
:::

:::proof "sharp_lens"
Suppose also $`|v-u|\le r/2`. For real part $`c_1`, put $`t=1/2-c_1` and $`v_*=1+tu`. Then
$`\operatorname{Re}(v_*)=\kappa` and $`|v_*|^2=|v_*-u|^2=(3+\varphi)/4`. Expanding about $`v_*` gives
$`(1-t)|v|^2+t|v-u|^2=(3+\varphi)/4+2(\operatorname{Re}(v)-\kappa)+|v-v_*|^2`. Both moduli are at most
$`r/2`, so $`\operatorname{Re}(v)\le \kappa-(3+\varphi-r^2)/8`, which contradicts the hypothesis
because $`r<R`. For real part $`c_2`, the second disk alone gives
$`\operatorname{Re}(v)\le r/2+c_2`, which lies below $`\kappa-(3+\varphi-r^2)/16` for every
$`0\le r<R`.
:::

At equality the two circles meet at $`v=1+t u` with real part $`\kappa`. Shrinking the circles opens
a gap even after the vertical cut moves left by $`(3+\varphi-r^2)/16`. This gap supplies the
room needed to choose integer-coordinate walls.
