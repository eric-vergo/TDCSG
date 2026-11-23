/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.Five
import TDCSGBlueprint.TwoDisks

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Proof of the main theorem" =>

%%%
tag := "main-theorem"
%%%

This chapter joins the two halves. Let $`R=\sqrt{3+\varphi}`. Part I shows that $`GG_5(r)` is
infinite for every $`r\ge R`, and Part II shows that it is finite for every $`r<R`. Together they
decide every radius, which is the {bpref "critical_radius_five"}[main theorem] stated in
Chapter 2: $`GG_5(r)` is finite if and only if $`r<R`, and the critical radius of order five is
exactly $`R`.

:::proof "critical_radius_five" (uses := "subcritical, threshold_infinite, critical_radius_of_iff")
Let $`r` be real. If $`r<R`, the group $`GG_5(r)` is finite by the
{bpref "subcritical"}[finite half]. If $`r\ge R`, it is infinite by the
{bpref "threshold_infinite"}[infinite half], so it is not finite. This is the equivalence. The
radii with an infinite group are then exactly the closed half-line $`[R,\infty)`, whose infimum
is $`R`, so the critical radius is $`R`.
:::

The equivalence is the Lean theorem `TDCSG.CriticalRadius.finite_GG_five_iff`, and the value of
the critical radius is `TDCSG.CriticalRadius.criticalRadius_five`; both appear in the Lean panel
of the main theorem. The library records three further consequences.

:::corollary "five_corollaries" (lean := "TDCSG.CriticalRadius.sSup_setOf_finite_GG_five, TDCSG.CriticalRadius.infinite_GG_five, TDCSG.CriticalRadius.infinite_orbit_zero_five") (uses := "critical_radius_five, threshold_infinite")
The supremum of the radii $`r` at which $`GG_5(r)` is finite is $`R`. For every $`r\ge R`,
the critical radius included, the group $`GG_5(r)` is infinite and the orbit of zero is infinite.
:::

:::proof "five_corollaries"
By the main theorem the radii with a finite group form the open half-line $`(-\infty,R)`, whose
supremum is $`R`. The other two statements are the infinite half.
:::

Both endpoints of the threshold are therefore settled: below $`R` every orbit is bounded by one
number depending only on $`r`, and at $`R` a single orbit, that of zero, is already infinite. The
Lean proof obtains the bound below $`R` from density and compactness, without an explicit value.
The [written proof](https://github.com/eric-vergo/TDCSG/blob/main/notes/proofs/sharp-lower-bound-n5-pentagrid.md)
makes the bound explicit. By its Lemma 4 and its proof, every $`M` consecutive levels contain a
good level, for an $`M\le16\sqrt5/\delta` where $`\delta=R^2-r^2`; this $`M` plays the role of
$`2K+1` for the recurrence bound $`K` of Chapter 6. Every orbit then has at most
$`1+10(2M+7)^5` points. These explicit bounds are not part of the Lean development.
