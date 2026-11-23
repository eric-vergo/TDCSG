# Ideas for later rounds

Authors: Eric Vergo, Claude and OpenAI GPT-6.2 Astra

Open directions that are not part of the current work. Each entry says what the question is and what it
depends on.

## The continuation gap

Depends on: [`proofs/analytic-radius.md`](proofs/analytic-radius.md) (the result $r_A(n) = \sec(\pi/n)$),
[`proofs/regularity-scale.md`](proofs/regularity-scale.md) (thresholds of function classes) and
[`gap-structure.md`](gap-structure.md) (the group on $[r_A, r_c)$, computed).

Functions on the union of the two open disks that are invariant under each disk's rotation are forced
to be constant once $r > r_A(n)$, while the piecewise group $GG_n(r)$ stays finite up to $r_c(n)$. The
piecewise group is what the two local symmetries generate when continuation across piece boundaries is
not imposed. The interval $(r_A, r_c)$ measures that freedom.

1. **Group structure inside the gap.** [`gap-structure.md`](gap-structure.md) computes where the group
   changes in $(r_A, r_c)$ and certified lower bounds for its order. What remains: proving that the
   sampled orders are the orders, and whether the change radii accumulate only at $r_c$.
2. **Intermediate pseudogroups.** Allow continuation across some piece boundaries only (for example
   where the maps on adjacent pieces agree). This gives groups between $GG_n(r)$ and the analytic hull,
   each with its own critical radius.
3. **The ratio.** Is $(r_c - 1)/(r_A - 1)$ governed by the units of $\mathbb{Z}[\zeta_n]$, or is it
   elementary geometry?
4. **Laplace eigenfunctions.** Do invariant eigenfunctions survive at or below $r_A$? Relation to the
   Euclidean Hecke-group picture in [`analytic-continuation.md`](analytic-continuation.md).
5. **Bump thresholds and the Hausdorff picture.** The questions left open in
   [`proofs/regularity-scale.md`](proofs/regularity-scale.md) §9: is every bump-class threshold equal
   to $\max(2, d_n)$ (Conjecture 6.1); can $C^0$, $C^\infty$ and Gevrey rigidity differ below the
   ergodicity radius; do infinite orbits have positive measure just above $r_c$ ($r_{\rm sep} = r_c$?);
   and a referee's check of the parts written after its report (Lemma 1.3, Proposition 8.2 part 2 for
   all $r > r_A$).

## Finiteness below the closed forms for n = 8, 10, 12

Depends on: [`certificates.md`](certificates.md), [`relative-certificates.md`](relative-certificates.md),
the sharp-lower-bound notes ([`proofs/sharp-lower-bound-n8.md`](proofs/sharp-lower-bound-n8.md),
[`-n12`](proofs/sharp-lower-bound-n12.md), [`-combined`](proofs/sharp-lower-bound-combined.md),
[`-limit-system`](proofs/sharp-lower-bound-limit-system.md)), the fivefold proof
[`proofs/sharp-lower-bound-n5-pentagrid.md`](proofs/sharp-lower-bound-n5-pentagrid.md) and
[`open-problem-critical-radius.md`](open-problem-critical-radius.md).

Finiteness of $GG_5(r)$ for every $r < \sqrt{3+\varphi}$ is a theorem (the pentagrid note); the
open cases are $n = 8, 10, 12$.

1. **Integer-coordinate walls for $n = 8, 10, 12$.** The fivefold proof labels the active disk
   centres by integer vectors and finds, in each coordinate, cuts at which every crossing edge of the
   centre graph has an endpoint of degree one; uniformly spaced cuts confine all labels to a box and
   bound every orbit. Test whether the same argument works for the other closed forms. Two
   ingredients must be redone for each $n$. (a) The geometric step (Lemma 2 of the pentagrid note):
   below $r_c(n)$, a vertex whose supporting abscissa exceeds a threshold $a(n)$ has no second
   active neighbour. (b) The arithmetic step: the midpoint abscissae of the edges in one coordinate
   form an irrational rotation with a target interval of positive length. For $n = 5$ the cosines of
   the other directions take only two values, so the abscissa depends on one integer combination
   and the rotation number is $\varphi$. For $n = 8, 10, 12$ more cosine values occur, the abscissa
   depends on several integer combinations, and a good cut must keep all of them away from a bad
   set. First compute, for each $n$, whether good cuts exist at $r$ close to $r_c(n)$; where they
   do not, find the configuration of active centres that blocks them.
2. **Monotone growth across levels for $n = 12$.** First-return sets and core orbit classes are
   observed only to grow with the level (`sharp-lower-bound-n12.md` §8). Prove it. The natural
   argument, that the rescaled disks contain the previous ones so orbit monotonicity in $r$ applies,
   fails: the rescaled generators rotate about different centres, so the level-$m$ and
   level-$(m+1)$ systems are not one system at two radii. A proof would reduce the core statement for
   $n = 12$ to a bound on the classes of one limit relation.
3. **Diophantine control of lune points uniform in the level.** Every observed change between
   levels is preceded by a lune point (a lattice point where the circle test and its tangent-line
   test disagree). The lune lemma controls them only at bounded zoomed internal radius; a bound
   uniform in the level, or a count of lune points at growing internal radius, would control where
   changes can occur.
4. **Exact period one for $n = 12$ from a deeper level.** Exact period one is refuted from every
   starting level $m_0 \le 3$; whether it holds from some $m_0 \ge 4$ is open, and the data fit both
   answers; the smallest internal radius of a change grows with the level, so a test needs
   deeper levels on samples of larger internal radius, or an argument.
5. **Period two for $n = 8$ and $n = 10$.** The total-positivity rule predicts period two for
   both (units of norm $-1$). For $n = 5$ exact period two of first-return sets is refuted
   (`sharp-lower-bound-limit-system.md` §5), and period two survives only as monotone coarsening of
   orbit classes (the archived note `sharp-bound-n5-period-two.md` in the companion repository
   TDCSG-archive). $n = 8$ has only floating-point germ samples, $n = 10$ nothing; repeat the exact
   tight-point tests of `sharp-lower-bound-limit-system.md` §5 and the orbit-partition test of that
   archived note (§6.6) for both.
6. **The limit of the first-return maps.** The fixed-word straight-cut limit is trivial
   (`sharp-lower-bound-limit-system.md` §3); the object to construct is the limit of the first-return
   maps to the tight cores, whose words have unbounded length, with a proof that the level-$k$
   system matches it (with the right period) from an explicit level. Conjecture S (S2) of
   `sharp-lower-bound-n8.md` is the $n = 8$ form.
7. **Self-similarity of the critical system.** For the bulk statement (S1) of
   `sharp-lower-bound-n8.md`, and its analogue for $n = 12$: compute the first-return systems on
   consecutive annuli at $r_c$, for instance from the face graph of a certified relative closure, and
   test whether their combinatorics stabilize (the method of `sharp-lower-bound-combined.md` §7,
   suggestion 3).
8. **Memory-efficient certificates.** Deep closures are large: for $n = 5$, level two needs about
   $6.9 \cdot 10^7$ maximal arcs modulo symmetry, some 39 GB in the symmetric generator, and the
   hybrid (windowed) storage saves at most about 2.5× (`relative-certificates.md` §9). Options: a
   packed arc store (fixed-width coefficients, as in `Store.lean`), disk-backed or streaming closure
   and checking, or a coarser invariant partition than the arc arrangement (for example by the set of
   available first-return germs). Finishing the check of the $n = 12$, $\delta = 1/250$ closure
   (generated, check stopped unfinished) and the window shapes for $n = 8$, $10$ that did not close
   need this.
9. **The conjugate cut-off for $n = 8, 10, 12$.** For $n = 5$ the chord part of the orbit of $0$
   reaches conjugate modulus of order $1/\delta$ (Theorem 6 of the archived note
   `sharp-bound-n5-conjugate.md` in the companion repository TDCSG-archive), and the pentagrid note
   bounds every conjugate translation by $O(1/\delta)$. The analogues for the chord of $n = 10$ and
   the self-similar chord families at $p^\ast$ for $n = 8, 12$: a lower bound of order $1/\delta$ on
   the conjugate reach, the exit index, and whether an upper bound of the same order holds.

## Fine structure of the fivefold system

Depends on: [`proofs/sharp-lower-bound-n5-pentagrid.md`](proofs/sharp-lower-bound-n5-pentagrid.md)
and the archived fivefold notes in the companion repository TDCSG-archive. These questions are not
needed for any threshold; they ask how the finite groups below $\sqrt{3+\varphi}$ and the infinite
group at it are organized.

1. **The sharp constant of the conjugate reach.** The pentagrid note gives
   $M(r) \le (160\sqrt5 + 32 r_c^2)/\delta$ for the largest conjugate modulus $M(r)$ of a word-map
   translation. The orbit of $0$ alone reaches order $1/\delta$ (the archived note
   `sharp-bound-n5-conjugate.md`, Theorem 6). Determine $\liminf$ and $\limsup$ of $\delta M(r)$ as
   $r \uparrow r_c$. Data: at levels $0$–$4$ the orbit of $0$ meets $\mathbb RE$ in exactly the
   cut-and-project set $\{sE: s\in2\mathbb Z+\mathbb Z\varphi,\ sE\in D_1\cup D_2,\ |\sigma s|\le
   T_k\}$ with $\delta_kT_k\to\varphi^7/10$ (Conjecture D of the archived note
   `sharp-bound-n5-orbit-of-zero.md`); the chord exit of the orbit of $0$ at level $k$ is
   $(F_{3k+7}-1)/2$ at the first levels; and at $r_c$ the largest conjugate modulus in breadth-first
   generation $g$ of the orbit of $0$ is the chord rate $1.514\,g$. Is the chord the fastest escape
   route, for every starting point?
2. **The renormalization inclusion at $E$, and the chord-free orbits.** Conjecture RI of the archived
   note `sharp-bound-n5-critical-renormalization.md`
   ($y\sim_\delta y'\Rightarrow\Psi y\sim_{\varepsilon\delta}\Psi y'$ near $E$, $\Psi(z)=E-\varepsilon(z-E)$,
   small $\delta$) would make the orbit of $-\zeta^2$ at $r_c$ infinite (witness already computed),
   showing that infinite orbits at $r_c$ need not contain chord points: the orbits of $-\zeta^2$ and
   $(-2,-2,-1,-2)$ provably never meet the chord and exceed $3\cdot10^7$ points. The first exact
   instance suggested by its referee: RI on one chord-parallel line, in the linear model of the
   holes, with the second-order deviation controlled on lattice points by $|s||\sigma y|\ge1/4$; and
   an exact proof of RI from level 0 to level 1 by atoms. RI holds on all tested pairs within $0.76$
   of $E$ and fails at $0.775$; find the exact region (candidates: bounded by circles through $\bar E$
   and through the critical point $(-1,1,-1,-1)$ at distance $\varphi^{-1}$; the failures involve a
   40-point island).
3. **The sign flip at $E$ itself.** The first-return set of $E$ (zoomed $\eta=0$) at level $k+1$ is
   exactly the negative of that at level $k$, for $k=3,4$ (and level 5 equals levels 1 and 3), so at
   $E$ the unit $-\varepsilon$ renormalizes the returns with period one, although cuts cannot match
   (the archived note `sharp-bound-n5-period-two.md`, §6.5). Prove $R_k(0)=(-1)^{k-3}R_3(0)$ for all
   $k\ge3$ (the non-linear return defects $\tau$ with $g(E)=Q'+\varepsilon^k\tau$ satisfy
   $\tau_{k+1}=-\tau_k$), and test whether it extends to other points with an extra symmetry.
4. **Exceptional set versus growth exponent.** The orbit of $0$ at $r_c$ has box-counting dimension
   about $1.8$, close to the exponent of $|O_r(0)|$ in $1/(r_c - r)$. Test this relation on other
   orbits and for $n = 8, 12$, and ask whether the closure of the cut set at $r_c$ has measure zero.

## Formalization

Depends on: [`certificates.md`](certificates.md) §7, [`relative-certificates.md`](relative-certificates.md)
§11 and [`proofs/sharp-lower-bound-n5-pentagrid.md`](proofs/sharp-lower-bound-n5-pentagrid.md) §5.

1. **The certificate theorem in Lean.** The library has no Lean counterpart of the cut-set
   certificate: the certificate theorem is a refereed written result, and the certified ranges are
   proved modulo the computation. Formalizing it needs a Lean definition of a certificate (a finite
   arc set with conditions (C1)–(C4)) and a proof of the theorem itself, whose main cost is the cell
   decomposition of a finite arc arrangement.
2. **A verified checker.** The certificate checker as a Lean function on a certificate data type, with
   a soundness theorem from `check cert = true` to that Lean definition. With item 1 this would turn
   each certified range for $n = 8, 10, 12$ into a Lean theorem.
3. **The relative-certificate theorem in Lean.** Theorem 4.2 of `sharp-lower-bound-combined.md`
   (with Theorem H of `relative-certificates.md` as its window-free case), and the non-norm lemma
   (Lemma 2.2 of `sharp-lower-bound-n5.md`) in the form needed for $n = 8, 10, 12$.
4. **The quantitative fivefold bounds.** The Lean proof of the fivefold threshold obtains its cut
   spacing by density and compactness. Formalize the explicit spacing $N \le 16\sqrt5/\delta$ from
   the Fibonacci return time and the conjugate bound $|\sigma(b)| \le 10N + 32$ (pentagrid note,
   Lemma 4 and §4). The natural Lean form is a Fibonacci version of the good-level recurrence
   `TDCSG.Five.exists_isGoodLevel`, with the explicit gap in place of the compactness bound; it
   gives the $O(1/\delta)$ bound on the conjugate translations.
5. **A ring structure on the model of $\mathbb Z[\zeta_5]$.** Give `TDCSG.Five.Cyc` a `CommRing`
   instance and make `embed` a ring homomorphism to $\mathbb C$, so that the `embed_*` lemmas become
   instances of `map_add`, `map_mul` and their companions. The same applies to the model
   `TDCSG.CycQ` used for $n = 8, 12$.
6. **Irrational rotations by piecewise translations.** A general lemma: if finitely many words act
   on closed sub-intervals of a segment as translations that together realize an irrational circle
   rotation, then the orbit of a point of the segment is infinite. The three-translation arguments
   for $n = 5$ (`TDCSG.Five.infinite_orbit_zero`) and $n = 10$ (`TDCSG.Ten.infinite_orbit_zero`)
   would then share one proof.
7. **A scoped notation for $\zeta$.** `Five/Cyclotomic.lean`, `Five/Labels.lean`,
   `Five/Chord.lean` and `Ten.lean` each declare a local notation for $\zeta = \exp(2\pi i/5)$;
   one scoped notation in `TDCSG.Five` would replace them.
8. **Mathlib candidates.** The two `TDCSG/ForMathlib` files: bounded return times of a dense cyclic
   subgroup of a compact group (`DenseRange.exists_natAbs_le_zsmul_add_mem`, with its irrational
   rotation form `Irrational.exists_abs_le_lt_norm_zsmul_add`), and walks that cross a cut only
   through leaves (`SimpleGraph.Reachable.mem_or_exists_adj_of_leaf`). Upstream, the first could
   instead be phrased through an `AddAction.IsMinimal` instance for a dense cyclic subgroup, which
   would reduce it to `IsCompact.exists_finite_cover_vadd`.

## Other open questions

1. **The rank conjecture for $n = 7$.** The exact threshold data stop just short of a second period
   of the origin's pattern; testing rank 2 needs deeper orbits (some $2 \cdot 10^9$ points) or a seed
   whose orbit grows through many thresholds ([`rank-conjecture.md`](rank-conjecture.md)).
2. **The large-$n$ table.** Whether the paper's large-$n$ critical radii are true critical radii or the
   onset of very large finite orbits is undetermined; orbits at the paper's scale need a deeper
   engine ([`large-n-table.md`](large-n-table.md)).

3. **Attainment of the group-level critical radius.** For any rotation order with a nonempty set
   of infinite-group radii, does the group already have an infinite orbit at their infimum?
   A proposed compactness proof takes radii decreasing to the infimum and chooses arbitrarily
   long simple paths of orbit points. Delete inactive letters and record the affine isometry
   at each prefix. The rooted tree of active prefixes has finite branching. A diagonal argument
   and König's lemma should select an infinite branch whose every finite prefix is legal at the
   limiting radius. The closed disks give nested compact sets of seeds for those prefixes.
   For any common seed, at most one translation per rotation index takes it to a specified
   point. An infinite branch with distinct affine prefixes would therefore visit infinitely
   many points. Check that arbitrarily long paths retain distinct affine prefixes across the
   limit and that all prefix domains lie in a common compact set. This proposed proof for
   general orders has not been checked here.
