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

#doc (Manual) "Good levels" =>

%%%
tag := "levels"
%%%

This chapter of Part II uses the lens estimate of Chapter 5 to build barriers for the walks of
Chapter 4. A good level of a coordinate, defined below, is an integer value of that coordinate
whose phase, a real number computed from the level, the window center and the coordinate, lies
far from a fixed lattice in the real line. Below the threshold, the lens estimate shows that every
edge of the center graph that raises the coordinate from a good level by one has an endpoint with
no other neighbor. Good levels recur within a bounded distance, uniformly in the
window, and Chapter 7 uses one good level below and one above the starting labels, in every
coordinate, to confine the walks.

:::figure TDCSGFigures.Levels.terminalCrossing (label := "terminal-crossing") (links := TDCSGFigures.Levels.terminalCrossing_spec) (alt := "Two panels. Above, a label n inside a circular window with four neighbors inside it and a thick edge to n plus e zero on the window's right edge, in a shaded half-plane; a circle walks from n along the thick edge to n plus e zero, four open rings appear outside the window joined to n plus e zero by dashed lines, and the circle walks back to n. Below, the end of the edge enlarged: the circle crosses the edge of the shaded half-plane and stops at n plus e zero, just inside the window's edge.")
A crossing at a good level, at $`r=2.12`, $`x=0.472` and coordinate $`j=0`. The label
$`n=(4,-3,1,1,-3)` (a dot) has weight zero, projects to $`P(n)=7-4\varphi`, and its coordinate
$`n_0=4` is a good level; the thick edge from $`n` to $`n+e_0` raises $`n_0` from $`4` to $`5`.
A circle follows the thick edge from level $`4` to level $`5`; the lower panel shows the end of
the edge enlarged, where the step crosses the cut. The leaf $`n+e_0` (a square: weight one) sits
at the window's edge, in the shaded half-plane
$`\operatorname{Re}w\ge\operatorname{Re}x+\kappa-\eta`, so by the lens estimate its four other
candidates $`n+e_0-e_k` (open rings at the ends of dashed spokes) lie outside the window, while
$`n` keeps its neighbors $`n+e_k` (squares inside the window). The only way to take another step is
back along the same edge to level $`4`. The centre of the small square around the leaf is enlarged, with a scale
bar, in {figref "terminal-zoom"}[]. The key frames are exact and the last one is the figure its
theorem states (`TDCSGFigures.Levels.terminalCrossing_spec`, the other frames in
`TDCSGFigures.Levels.terminalCrossing_keys`); between them the browser slides the circle along the
edge.
:::

:::figure TDCSGFigures.Levels.terminalZoom (label := "terminal-zoom") (inline := true) (links := TDCSGFigures.Levels.terminalZoom_spec) (alt := "An enlargement near the leaf: the edge from n ends at the leaf, which lies right of the cut and left of the window's edge, with a scale bar of length 0.005.")
The neighborhood of the leaf $`n+e_0` of {figref "terminal-crossing"}[], enlarged, with a scale bar
of length $`0.005`. The leaf $`P(n+e_0)=8-4\varphi` lies between $`0.0045` and $`0.0046` beyond the
cut $`\operatorname{Re}w=\operatorname{Re}x+\kappa-\eta` (the left edge of the shaded half-plane)
and between $`0.0041` and $`0.0042` inside the window's edge $`x+r/2=1.532`. In
{figref "terminal-crossing"}[] both gaps are smaller than a pixel.
:::

A good level acts as a wall in the integer coordinates, not as a line in the projected disk.
Crossing a wall in the $`j`th coordinate changes $`n_j` by one. {figref "terminal-crossing"}[]
shows the local effect:
one endpoint of the crossing edge has no neighbor other than the other endpoint, and the dashed
spokes ending in open rings mark the rejected candidates. The lemma below shows that every crossing at a good
level ends this way.

Crossings at good levels are rare. If an edge from $`n` to $`n+e_j` has both ends in the window,
the proof below writes the phase of the level $`n_j`, up to a multiple of $`L`, as
$`\operatorname{Re}(q)+1/2` with $`|q|\le r/2` and $`|q+1|\le r/2`. Then
$`-r/2\le\operatorname{Re}(q)\le r/2-1`, so the phase lies within $`r/2-1/2` of $`L\mathbb Z`,
while a good level has its phase farther than $`L/2-\eta` from $`L\mathbb Z`, with $`L` and
$`\eta` as in the definition below. Both can hold only
if $`r/2-1/2>L/2-\eta`, that is, $`r^2-8r+7\varphi+1<0`, which for $`r<R` means
$`r>4-\sqrt{15-7\varphi}\approx2.083`. So such an edge exists only for radii close to
$`R\approx2.149`, which is why {figref "terminal-crossing"}[] uses $`r=2.12`. This is the
threshold of Chapter 5 below which the lens estimate holds for want of any point. For smaller
radii, such as $`r=1.8` in {figref "level-phases"}[], no edge of the center graph crosses a good
level at all.
The theorem at the end of the chapter chooses walls for arbitrary windows and both sides of each
coordinate.

:::figure TDCSGFigures.Levels.levelPhases (label := "level-phases") (inline := true) (links := TDCSGFigures.Levels.levelPhases_spec) (alt := "A plot of the phase of each level m from minus 13 to 9, in units of L, between minus one half and one half. The levels minus 10, minus 2 and 3 land in the shaded good bands next to plus and minus L over 2; dashed vertical lines mark lo = minus 10 and hi = 3, and a shaded column marks the gap |m| ≤ 2.")
The phase $`(1+\varphi/2)m+1/2-\operatorname{Re}x` of each level $`m` of coordinate $`0` at
$`x=0.87` and $`r=1.8`, reduced modulo $`L=\varphi-1/2` and drawn in units of $`L`. A level is good
when its phase lies in one of the shaded bands labelled good, farther than $`L/2-\eta` from
$`L\mathbb Z`; here the good levels are $`-10`, $`-2` and $`3` (large markers). The confinement
proof of Chapter 7 looks for $`lo` among the levels from $`-2K-3` to $`-3` and for $`hi` among those
from $`3` to $`2K+3`, where $`K` is the bound of the theorem at the end of this chapter; in the range
drawn its only candidates are $`lo=-10` and $`hi=3` (on the dashed vertical lines), while the good
level $`-2` lies in the gap $`|m|\le2` (shaded column) between the two ranges. It is left out because
of where the proof searches, not because of the starting labels: as $`lo` it would also keep the
starting labels $`0`, $`e_0` and their neighbors, whose coordinates lie between $`-1` and $`1`,
inside the slab $`lo<n_0\le hi`.
:::

{figref "level-phases"}[] uses another window, $`x=0.87` and $`r=1.8`, and coordinate $`0`. Each dot gives the
phase of an integer level, reduced to the interval from minus to plus half a period. The two
shaded bands are the good phases, and the levels $`-10`, $`-2` and $`3` land there. Chapter 7
takes one good level at most $`-3` and one at least $`3`, here $`-10` and $`3`, so that the
starting labels and their neighbors lie strictly between them. The theorem at the end of this
chapter finds such levels within a bounded distance, uniformly in the window.
:::figure TDCSGFigures.Levels.levelWinding (label := "level-winding") (alt := "Two panels. Above, a circle with a shaded arc at the top; a hand at its center turns counterclockwise by a little more than half a turn from each level to the next, and a point lands on the circle for each level from minus 13 to 9; the levels minus 10, minus 2 and 3 land in the shaded arc and are named. Below, the plot of the phases of the same levels filling in level by level, a ring sliding from each point to the next.")
The levels of {figref "level-phases"}[] arriving one at a time, $`m=-13,\dots,9`. Above, the
phase, reduced modulo $`L`, is a point of a circle of circumference $`L`, with phase $`0` at the
bottom and $`\pm L/2` at the top, in the shaded arc of the good phases. From one level to the next
the phase grows by $`1+\varphi/2=\varphi L`, that is by $`\varphi` periods, so the reduced phase
winds round by $`\varphi-1` of a turn; the hand turns by that much. Below, the same levels fill in
the plot. Which levels are good is decided exactly, and the points below are at their exact
phases; above, each point is placed, in floating point, from a rational within $`2^{-62}` of its
exact phase, and each turn of the hand is the difference of two such rationals, within
$`2^{-62}` of $`\varphi-1`. Between the key frames the browser turns the hand and slides the
ring.
:::

Because $`\varphi` is irrational, the reduced phases of the levels never repeat and come back
within any distance of every phase, which is why good levels recur; {figref "level-winding"}[]
shows the first 23 of them winding round.

:::definition "good_level" (lean := "TDCSG.Five.IsGoodLevel") (uses := "center_projection")
Fix the radius $`r`, the window center $`x` and a coordinate $`j`. Put $`L=\varphi-1/2` and
$`\eta=(3+\varphi-r^2)/16`. The phase of the integer level $`m` is
$`(1+\varphi/2)m+1/2-\operatorname{Re}(x\zeta^{-j})`. The level is good when its phase is farther
than $`L/2-\eta` from every point of $`L\mathbb Z`.
:::

:::lemma_ "terminal_crossing" (lean := "TDCSG.Five.IsGoodLevel.leaf") (uses := "good_level, active_graph, unit_step, sharp_lens")
Let $`0\le r<R`. Let $`n` be a weight-zero label whose coordinate $`n_j` is a good level, with
$`n` and $`n+e_j` both in the window, so that $`n` and $`n+e_j` are joined by an edge of the
center graph. Then no label $`n+e_k` with $`k\ne j` lies in the window,
or no label $`n+e_j-e_k` with $`k\ne j` does. So one endpoint of the edge has no other neighbor.
:::

:::proof "terminal_crossing" (lean := "TDCSG.Five.re_proj_mul_conj_dir")
Turn by $`\zeta^{-j}` and put $`q=(P(n)-x)\zeta^{-j}`, so that $`|q|\le r/2` and
$`|q+1|\le r/2`. For a weight-zero label,
$`\operatorname{Re}(P(n)\zeta^{-j})=(1+\varphi/2)n_j+L(n_{j+1}+n_{j-1})`. Hence
$`\operatorname{Re}(q)+1/2` differs from the phase of the level $`n_j` by a multiple of $`L`,
and $`|\operatorname{Re}(q)+1/2|>L/2-\eta`.

If $`\operatorname{Re}(q)+1/2>L/2-\eta`, put $`v=q+1`, the turned position of $`n+e_j`. Its real
part exceeds $`\kappa-\eta`. The turned candidates $`n+e_j-e_k` sit at $`v-\zeta^{k-j}`, and
$`\zeta^{k-j}` has real part $`c_1` or $`c_2` for $`k\ne j`, so the sharp lens estimate puts
them outside the window. Otherwise put $`v=-q`, the reflection of $`n` through the window
center. Its real part again exceeds $`\kappa-\eta`, and the turned candidates $`n+e_k` sit at
$`-(v-\zeta^{k-j})`. The same estimate excludes them.
:::

:::lemma_ "bounded_returns" (lean := "DenseRange.exists_natAbs_le_zsmul_add_mem, Irrational.exists_abs_le_lt_norm_zsmul_add")
Let $`G` be an additive group with a compact topology in which addition is continuous, and let
the integer multiples of $`g\in G` be dense. For each nonempty open set $`U` there is a bound
$`K` such that every $`y` has a translate $`ig+y\in U` with $`|i|\le K`. In particular, for $`L>0`, $`\eta>0` and irrational $`\alpha/L`, every point of the
circle $`\mathbb R/L\mathbb Z` has a translate by $`i\alpha`, with $`|i|\le K`, at distance more
than $`L/2-\eta` from zero.
:::

:::proof "bounded_returns"
By density, the open sets $`-ig+U` with $`i\in\mathbb Z` cover the group. Compactness gives a
finite subcover, and $`K` is the largest $`|i|` that occurs. On the circle the multiples of
$`\alpha` are dense because $`\alpha/L` is irrational. The points at distance more than
$`L/2-\eta` from zero form an open set containing the half period.
:::

:::lemma_ "irrational_levels" (lean := "TDCSG.Five.exists_abs_le_forall_lt_abs_add_mul") (uses := "bounded_returns")
For $`L>0`, $`\eta>0` and irrational $`\alpha/L` there is a bound $`K` with the following
property. For every real phase $`\beta` and every integer $`m_0`, some level $`m_0+i` with
$`|i|\le K` satisfies $`|\alpha(m_0+i)+\beta+Lp|>L/2-\eta` for every integer $`p`.
:::

:::proof "irrational_levels"
Apply the bounded return time to the point $`m_0\alpha+\beta` of the circle. The distance from
$`\alpha(m_0+i)+\beta` to zero on the circle is at most $`|\alpha(m_0+i)+\beta+Lp|` for every
$`p`.
:::

:::theorem "all_walls" (lean := "TDCSG.Five.exists_isGoodLevel") (uses := "good_level, irrational_levels")
Let $`0\le r<R`. There is a bound $`K` such that, for every window center $`x`, every
coordinate $`j` and every integer $`m_0`, one of the levels $`m_0+i` with $`|i|\le K` is good.
:::

:::proof "all_walls"
Take $`\alpha=1+\varphi/2`, $`L=\varphi-1/2` and $`\eta=(3+\varphi-r^2)/16`, which is positive
below $`R`. The ratio $`\alpha/L=\varphi` is irrational. The phase
$`\beta=1/2-\operatorname{Re}(x\zeta^{-j})` is the only place where $`x` and $`j` enter, and the
bound for irrational levels does not depend on it.
:::
