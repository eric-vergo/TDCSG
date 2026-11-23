/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.Five

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "A crossing with nowhere to go" =>

%%%
tag := "walls"
%%%

![Four candidate unit edges from the red leaf end outside the blue window. The horizontal edge leads to the only retained neighbor.](/figures/terminal.svg)

A wall is a good level of an integer coordinate, not a line in the projected disk. Crossing the
$`j`th wall changes $`n_j` by one. The figure isolates the local effect: one endpoint has only
the crossing edge left. In this illustration $`x=0.87` and $`r=1.8`. Gray spokes mark rejected
candidates. The theorem chooses walls for arbitrary windows and both sides of each coordinate.

![Phases at integer levels plotted modulo the period. The selected levels minus ten and three land in the shaded bands near a half-period.](/figures/levels.svg)

For the same window in direction zero, each dot gives the phase of an integer level, reduced
to the interval from minus to plus half a period. The two shaded bands are the allowed phases.
The levels $`-10` and $`3` land there, outside the initial labels on opposite sides.
The following argument finds such a pair without searching separately for each window.

:::definition "good_level" (lean := "TDCSG.Five.IsGoodLevel") (uses := "center_projection")
Fix the radius $`r`, the window center $`x` and a coordinate $`j`. Put $`L=\varphi-1/2` and
$`\eta=(3+\varphi-r^2)/16`. The integer level $`m` is good when
$`(1+\varphi/2)m+1/2-\operatorname{Re}(x\zeta^{-j})` is farther than $`L/2-\eta` from every point
of $`L\mathbb Z`.
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
$`\operatorname{Re}(q)+1/2` differs from the phase of the good level by a multiple of $`L`, and
$`|\operatorname{Re}(q)+1/2|>L/2-\eta`.

If $`\operatorname{Re}(q)+1/2>L/2-\eta`, put $`v=q+1`, the turned position of $`n+e_j`. Its real
part exceeds $`a-\eta`. The turned candidates $`n+e_j-e_k` sit at $`v-\zeta^{k-j}`, and
$`\zeta^{k-j}` has real part $`c` or $`d` for $`k\ne j`, so the sharp lens estimate puts them
outside the window. Otherwise put $`v=-q`, the reflection of $`n` through the window center. Its
real part again exceeds $`a-\eta`, and the turned candidates $`n+e_k` sit at
$`-(v-\zeta^{k-j})`. The same estimate excludes them.
:::

:::lemma_ "bounded_returns" (lean := "DenseRange.exists_natAbs_le_zsmul_add_mem, Irrational.exists_abs_le_lt_norm_zsmul_add")
In a compact additive topological group, let the multiples of $`a` be dense. For each nonempty
open set $`U` there is a bound $`K` such that every $`y` has a translate $`ia+y\in U` with
$`|i|\le K`. In particular, for $`L>0`, $`\eta>0` and irrational $`\alpha/L`, every point of the
circle $`\mathbb R/L\mathbb Z` has a translate by $`i\alpha`, with $`|i|\le K`, at distance more
than $`L/2-\eta` from zero.
:::

:::proof "bounded_returns"
By density, the open sets $`-ia+U` with $`i\in\mathbb Z` cover the group. Compactness gives a
finite subcover, and $`K` is the largest $`|i|` that occurs. On the circle the multiples of
$`\alpha` are dense because $`\alpha/L` is irrational. The points at distance more than
$`L/2-\eta` from zero form an open set containing the half period.
:::

:::lemma_ "irrational_levels" (lean := "TDCSG.Five.exists_abs_le_forall_lt_abs_add_mul") (uses := "bounded_returns")
For $`L>0`, $`\eta>0` and irrational $`\alpha/L` there is a bound $`K` with the following
property. For every real phase $`b` and every integer $`z`, some level $`z+i` with $`|i|\le K`
satisfies $`|\alpha(z+i)+b+Lp|>L/2-\eta` for every integer $`p`.
:::

:::proof "irrational_levels"
Apply the bounded return time to the point $`z\alpha+b` of the circle. The distance from
$`\alpha(z+i)+b` to zero on the circle is at most $`|\alpha(z+i)+b+Lp|` for every $`p`.
:::

:::theorem "all_walls" (lean := "TDCSG.Five.exists_isGoodLevel") (uses := "good_level, irrational_levels")
Let $`0\le r<R`. There is a bound $`K` such that, for every window center $`x`, every
coordinate $`j` and every integer $`z`, one of the levels $`z+i` with $`|i|\le K` is good.
:::

:::proof "all_walls"
Take $`\alpha=1+\varphi/2`, $`L=\varphi-1/2` and $`\eta=(3+\varphi-r^2)/16`, which is positive
below $`R`. The ratio $`\alpha/L=\varphi` is irrational. The phase
$`b=1/2-\operatorname{Re}(x\zeta^{-j})` is the only place where $`x` and $`j` enter, and the
bound for irrational levels does not depend on it.
:::
