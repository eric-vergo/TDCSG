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
Chapter 4. A good level of a coordinate, defined below, is an integer value of that coordinate at
which every edge of the center graph that raises the coordinate from that value by one has an
endpoint with no other neighbor. Good levels recur within a bounded distance, uniformly in the
window, and Chapter 7 uses one good level below and one above the starting labels, in every
coordinate, to confine the walks.

![Four candidate unit edges from the rust leaf end outside the blue window. The horizontal edge leads to the only retained neighbor.](/figures/terminal.svg)

A good level acts as a wall in the integer coordinates, not as a line in the projected disk.
Crossing a wall in the $`j`th coordinate changes $`n_j` by one. The figure isolates the local effect: one endpoint has only
the crossing edge left. In this illustration $`x=0.87` and $`r=1.8`. Gray spokes mark rejected
candidates. In this window the drawn edge is not at a good level; the lemma below shows that at
a good level a crossing must end this way. The theorem chooses walls for arbitrary windows and
both sides of each coordinate.

![Phases at integer levels plotted modulo the period. The selected levels minus ten and three land in the shaded bands near a half-period.](/figures/levels.svg)

For the same window in direction zero, each dot gives the phase of an integer level, reduced
to the interval from minus to plus half a period. The two shaded bands are the allowed phases.
The levels $`-10`, $`-2` and $`3` land there. The proof takes one good level at most $`-3` and
one at least $`3`, here $`-10` and $`3`, so that the starting labels and their neighbors lie
strictly between them. The following argument finds such a pair without searching separately
for each window.

:::definition "good_level" (lean := "TDCSG.Five.IsGoodLevel") (uses := "center_projection")
Fix the radius $`r`, the window center $`x` and a coordinate $`j`. Put $`L=\varphi-1/2` and
$`\eta=(3+\varphi-r^2)/16`. The phase of the integer level $`m` is
$`(1+\varphi/2)m+1/2-\operatorname{Re}(x\zeta^{-j})`. The level is good when its phase is farther
than $`L/2-\eta` from every point of $`L\mathbb Z`.
:::

:::lemma_ "terminal_crossing" (lean := "TDCSG.Five.IsGoodLevel.leaf") (uses := "good_level, active_graph, unit_step, sharp_lens")
Let $`0\le r<R`. Let $`n` be a weight-zero label whose coordinate $`n_j` is a good level, with
$`n` and $`n+e_j` both in the window. Then no label $`n+e_k` with $`k\ne j` lies in the window,
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
