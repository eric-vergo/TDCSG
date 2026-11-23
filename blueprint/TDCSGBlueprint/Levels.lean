/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.Five

open Verso.Genre Verso.Genre.Manual Informal

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

![A label n in a gray window with its edge to n plus e zero. Beyond a dashed cut, the four other candidate neighbors of n plus e zero lie outside the window, so n plus e zero is a leaf.](/plates/terminal.svg)
*Figure 7.* A crossing at a good level, computed for $`r=2.12`, $`x=0.472` and coordinate $`j=0`. The label $`n=(4,-3,1,1,-3)` has weight zero, projects to $`P(n)=7-4\varphi`, and its coordinate $`n_0=4` is a good level; the edge from $`n` to $`n+e_0` crosses it. The leaf $`n+e_0` lies beyond the cut $`\operatorname{Re}w=\operatorname{Re}x+\kappa-\eta` (enlarged at right), so by the lens estimate its four other candidates $`n+e_0-e_k` (gray open rings, dashed) lie outside the window, while $`n` keeps its other neighbors $`n+e_k` (vermilion filled dots). Such crossings occur only for $`r>4-\sqrt{15-7\varphi}\approx2.083`; at $`r=1.8` no edge crosses a good level.

A good level acts as a wall in the integer coordinates, not as a line in the projected disk.
Crossing a wall in the $`j`th coordinate changes $`n_j` by one. The figure shows the local effect:
one endpoint of the crossing edge has no neighbor other than the other endpoint, and the dashed
gray spokes mark the rejected candidates. The lemma below shows that every crossing at a good
level ends this way.

Crossings at good levels are rare. If an edge from $`n` to $`n+e_j` has both ends in the window,
the proof below writes the phase of the level $`n_j`, up to a multiple of $`L`, as
$`\operatorname{Re}(q)+1/2` with $`|q|\le r/2` and $`|q+1|\le r/2`. Then
$`-r/2\le\operatorname{Re}(q)\le r/2-1`, so the phase lies within $`r/2-1/2` of $`L\mathbb Z`,
while a good level has its phase farther than $`L/2-\eta` from $`L\mathbb Z`, with $`L` and
$`\eta` as in the definition below. Both can hold only
if $`r/2-1/2>L/2-\eta`, that is, $`r^2-8r+7\varphi+1<0`, which for $`r<R` means
$`r>4-\sqrt{15-7\varphi}\approx2.083`. So such an edge exists only for radii close to
$`R\approx2.149`, which is why Figure 7 uses $`r=2.12`. For smaller radii, such as $`r=1.8` in
Figure 8, no edge of the center graph crosses a good level at all.
The theorem at the end of the chapter chooses walls for arbitrary windows and both sides of each
coordinate.

![Phases of the levels minus 13 to 9 of one coordinate, plotted modulo the period. The good levels minus ten, minus two and three land in the shaded bands near half a period.](/plates/levels.svg)
*Figure 8.* The phase $`(1+\varphi/2)m+1/2-\operatorname{Re}x` of each level $`m` of coordinate $`0`, reduced modulo $`L=\varphi-1/2`, for $`x=0.87` and $`r=1.8`. A level is good when its phase lies in one of the two green bands labelled good, farther than $`L/2-\eta` from $`L\mathbb Z`; in the range drawn the good levels are $`-10`, $`-2` and $`3` (large dots). The confinement proof of Chapter 7 looks for $`lo` among the levels from $`-2K-3` to $`-3` and for $`hi` among those from $`3` to $`2K+3`, where $`K` is the bound of the theorem at the end of this chapter. In the range drawn its only candidates are $`lo=-10` and $`hi=3` (filled dots on dashed lines). The good level $`-2` (open ring) lies in the gap $`|m|\le2` between the two search ranges. It is left out because of where the proof searches, not because of the starting labels: as $`lo` it would also keep the starting labels $`0`, $`e_0` and their neighbors, whose coordinates lie between $`-1` and $`1`, inside the slab $`lo<n_0\le hi`.

Figure 8 uses another window, $`x=0.87` and $`r=1.8`, and coordinate $`0`. Each dot gives the
phase of an integer level, reduced to the interval from minus to plus half a period. The two
shaded bands are the good phases, and the levels $`-10`, $`-2` and $`3` land there. Chapter 7
takes one good level at most $`-3` and one at least $`3`, here $`-10` and $`3`, so that the
starting labels and their neighbors lie strictly between them. The theorem at the end of this
chapter finds such levels within a bounded distance, uniformly in the window.

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
