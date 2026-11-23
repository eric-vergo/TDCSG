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

#doc (Manual) "The lens estimate" =>

%%%
tag := "lens"
%%%

This chapter of Part II is where the threshold $`\sqrt{3+\varphi}` enters the finite half. Its
lemma is an estimate on the overlap of two disks, sharp exactly at the
threshold; Chapter 6 turns its margin into barriers for the walks of Chapter 4.

:::figure TDCSGFigures.Lens.lensEstimate (label := "lens-estimate") (inline := true) (proves := TDCSGFigures.Lens.lensEstimate_spec) (alt := "Two overlapping circles of radius 0.9 about 0 and u = zeta, their shaded lens, and two shaded vertical half-planes on the right, the lighter one with a dashed edge. The tip of the lens lies left of both half-planes; the point v-star lies on the edge of the darker one.")
The two window tests $`|v|\le r/2` (solid circle) and $`|v-u|\le r/2` (dashed circle) for
$`u=\zeta` at $`r=1.8`, their lens, and the half-planes $`\operatorname{Re}v\ge\kappa-\eta`
(lightly shaded strip with a dashed edge, together with everything to its right) and
$`\operatorname{Re}v\ge\kappa` (darker), with $`\kappa=(2\varphi+1)/4`,
$`\eta=(3+\varphi-r^2)/16` (the width of the strip, marked at the top) and
$`c_1=\operatorname{Re}u=(\varphi-1)/2` (the foot of $`u` on the real axis). The tip of the lens, its
point of largest real part, lies on both circles and left of both half-planes; its real part is at
most $`\kappa-2\eta`. The point $`v_*=1+tu`, $`t=1/2-c_1`, lies on the line
$`\operatorname{Re}v=\kappa` at distance $`R/2` from $`0` and $`u`, outside both disks. At this
radius the whole disk $`|v|\le r/2` lies left of the dashed edge.
:::

Suppose two different center changes are possible. Rotate the coordinates so the crossing
direction is horizontal. Their simultaneous tests put a vector $`v` in two disks of radius
$`r/2`, centered at 0 and a unit vector $`u`. The shaded overlap in {figref "lens-estimate"}[] is the lens. The relevant
horizontal components of $`u` are $`c_1=(\varphi-1)/2` and $`c_2=-\varphi/2`. {figref "lens-estimate"}[]
draws the tighter case $`u=\zeta`, with real part $`c_1`.

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

At equality, $`r=R`, the two circles meet at the point $`v_*=1+tu` of the proof, where
$`t=1/2-c_1=(2-\varphi)/2`; its real part is $`\kappa`. Below $`R` the proof gives more than the
lemma states: every point of the lens has real part at most $`\kappa-2\eta`, with
$`\eta=(3+\varphi-r^2)/16`, so the tip of the lens stays at least $`\eta` left of the line
$`\operatorname{Re}v=\kappa-\eta`. The estimate is sharp in the sense that this bound on the tip
holds with equality only at $`r=R`, where $`\eta=0` and the tip is $`v_*` on the line
$`\operatorname{Re}v=\kappa`. The margin $`\eta` supplies the room needed to choose the good
levels of Chapter 6; at $`r=R` it is zero, which is why the argument stops at the threshold.

For most radii below $`R` the lemma holds for want of any $`v`. The disk $`|v|\le r/2` reaches the
line $`\operatorname{Re}v=\kappa-\eta` only when $`r/2\ge\kappa-\eta`, that is, when
$`r^2-8r+7\varphi+1\le0`. For $`0\le r<4-\sqrt{15-7\varphi}\approx2.083` this fails: every $`v`
with $`|v|\le r/2` has real part less than $`\kappa-\eta`, and the hypothesis of the lemma is met
by no $`v` at all. The estimate has content only for $`4-\sqrt{15-7\varphi}\le r<R`, a narrow
range just below $`R\approx2.149`. This is the same threshold as the one beyond which, by
Chapter 6, an edge of the center graph can cross a good level at all.

:::figure_explorer TDCSGFigures.Lens.lensRadius (label := "lens-radius") (proves := TDCSGFigures.Lens.lensRadius_spec) (alt := "The lens picture at r = 1.8, 2, 2.08, 2.12 and R: as r grows the tip of the lens moves right towards the shaded half-planes and reaches the line Re v = kappa exactly at R.")
The lens of the disks $`|v|\le r/2` and $`|v-\zeta|\le r/2` with the half-planes
$`\operatorname{Re}v\ge\kappa-\eta` (dashed edge) and $`\operatorname{Re}v\ge\kappa` for
$`r=1.8, 2, 2.08, 2.12` and $`R=\sqrt{3+\varphi}`. As $`r` grows the strip between the two edges
narrows and the tip moves right; below $`R` the tip stays left of the dashed edge, and at $`R`,
where $`\eta=0`, the tip is $`v_*` on the line $`\operatorname{Re}v=\kappa`. Notice where the solid
circle $`|v|\le r/2` lies: at $`r=1.8`, $`2` and $`2.08` it stays entirely left of the dashed edge,
so no $`v` meets the hypothesis of the lemma; at $`r=2.12`, above $`4-\sqrt{15-7\varphi}`, it
crosses the edge and the lens still does not.
:::
