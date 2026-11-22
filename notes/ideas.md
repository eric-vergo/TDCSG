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

## Finiteness below the closed forms

Depends on: [`certificates.md`](certificates.md), [`relative-certificates.md`](relative-certificates.md),
the sharp-lower-bound notes ([`proofs/sharp-lower-bound-n5.md`](proofs/sharp-lower-bound-n5.md),
[`-n8`](proofs/sharp-lower-bound-n8.md), [`-combined`](proofs/sharp-lower-bound-combined.md),
[`-limit-system`](proofs/sharp-lower-bound-limit-system.md), [`-n12`](proofs/sharp-lower-bound-n12.md))
and [`open-problem-critical-radius.md`](open-problem-critical-radius.md).

1. **Monotone growth across levels.** For $n = 12$, first-return sets and core orbit classes are
   observed only to grow with the level (`sharp-lower-bound-n12.md` §8). For $n = 5$ the tight-core
   orbit classes only merge from level $k$ to $k+2$ at $1\to3$ and $2\to4$ (hypothesis (M$_5$) of
   Proposition 4.5 of [`proofs/sharp-bound-n5-period-two.md`](proofs/sharp-bound-n5-period-two.md)),
   although first-return sets also shrink. Prove either. The natural argument, that the rescaled
   disks contain the previous ones so orbit monotonicity in $r$ applies, fails: the rescaled
   generators rotate about different centres, so the level-$m$ and level-$(m+1)$ systems are not one
   system at two radii. A proof would reduce (R-core-t) to a bound on the classes of one limit
   relation. For $n = 5$ the next test is the orbit-partition test at $3\to5$, which needs more
   memory than used so far (a packed or disk-backed point store).
2. **Diophantine control of lune points uniform in the level.** Every observed change between
   levels is preceded by a lune point (a lattice point where the circle test and its tangent-line
   test disagree). The lune lemma controls them only at bounded zoomed internal radius; a bound
   uniform in the level, or a count of lune points at growing internal radius, would control where
   changes can occur.
3. **Exact period one for $n = 12$ from a deeper level.** Exact period one is refuted from every
   starting level $m_0 \le 3$; whether it holds from some $m_0 \ge 4$ is open, and the data fit both
   answers; the smallest internal radius of a change grows with the level, so a test needs
   deeper levels on samples of larger internal radius, or an argument.
4. **Period two for $n = 8$ and $n = 10$.** The total-positivity rule predicts period two for
   both (units of norm $-1$). For $n = 5$ exact period two of first-return sets is refuted, and
   period two survives only as monotone coarsening of orbit classes (item 1). $n = 8$ has only
   floating-point germ samples, $n = 10$ nothing; repeat the exact tight-point tests of
   `sharp-lower-bound-limit-system.md` §5 and the orbit-partition test of the period-two note §6.6
   for both.
5. **The limit of the first-return maps.** The fixed-word straight-cut limit is trivial
   (`sharp-lower-bound-limit-system.md` §3); the object to construct is the limit of the first-return
   maps to the tight cores, whose words have unbounded length, with a proof that the level-$k$
   system matches it (with the right period) from an explicit level. Conjecture S (S2) of
   `sharp-lower-bound-n8.md` is the $n = 8$ form.
6. **Self-similarity of the critical system.** The annulus reduction of (R-bulk): compute the
   first-return systems on consecutive annuli at $r_c$, for instance from the face graph of a
   certified relative closure, and test whether their combinatorics stabilize
   (`sharp-lower-bound-combined.md` §7, suggestion 3).
7. **Memory-efficient certificates.** $n = 5$ level two needs about $6.9 \cdot 10^7$ maximal arcs
   modulo symmetry, some 39 GB in the symmetric generator; the hybrid (windowed) storage saves at most
   about 2.5× (`relative-certificates.md` §9). Options: a packed arc store (fixed-width coefficients,
   as in `Store.lean`), disk-backed or streaming closure and checking, or a coarser invariant
   partition than the arc arrangement (for example by the set of available first-return germs). The
   same applies to finishing the check of the $n = 12$, $\delta = 1/250$ closure (generated, check
   stopped unfinished), to $n = 5$ window 9 at $r_c$, and to the window shapes for $n = 8$, $10$ that
   did not close.
8. **The face count $F$.** $\beta_W = 1 + 20nF$ and the word-length bound of Proposition 4.4 of
   `sharp-lower-bound-combined.md` are not explicit, because $F$ (bounded faces of the complement of
   a restricted closure) was never computed. It needs every crossing of two arcs, with exact
   identification of points on three or more circles.

The items below concern $n = 5$ through the Galois-conjugate coordinate and the chord tokens; the
guide [`sharp-bound-n5.md`](sharp-bound-n5.md) explains the terms and lists the formulations that
are refuted or closed.

9. **Uniform chaining of token components, (K).** Finiteness gives a bound at each subcritical
   radius. The open problem asks for a radius-independent bound on the number of connector letters needed to reach every state of an orbit,
   equivalently on the diameter of its component graph
   ([`proofs/sharp-bound-n5-component-graph.md`](proofs/sharp-bound-n5-component-graph.md)
   Proposition 1; computed: at most 9 wherever measured exactly, on 18 named and 878 random orbits).
   With (T), proved, it gives finiteness below $\sqrt{3+\varphi}$. Renormalizing the component
   graph by $\varepsilon$, alone or through an atlas of $\pm\varepsilon$ charts, leaves a
   reverse-type coverage and gluing step that is (K) in relative form; the referees conclude that a
   new idea is needed. Items 10–14 are the candidates recorded so far.
10. **A wall or monotone quantity for connectors.** The cut-off of token components
    ([`proofs/sharp-bound-n5-token-components.md`](proofs/sharp-bound-n5-token-components.md)) comes
    from a wall: the $\bar E$-line through $-F$ carries no forward $E$-step below $r_c$, up to dead
    ends. Look for walls of the same kind for the full group in the lifted state space: sets of
    states, defined by position relative to finitely many lines through corners, that no letter
    crosses except through dead ends, or a quantity that connectors cannot increase. A wall family
    with spacing $O(1/\delta)$ exists for the integer labels of active centers and proves the
    exact threshold. Bounding the number of connectors uniformly is a separate question.
    [Integer-coordinate walls](proofs/sharp-lower-bound-n5-pentagrid.md)
11. **Renormalize the cut set rather than orbit graphs.** Test whether the cut set $K(\varepsilon\delta)$
    is $\varepsilon K(\delta)$ together with finitely many explicitly described arc families: compute
    $K(r)$ at $\delta = 1/55$ and $\varepsilon/55$ with `certify`, map the first by $\varepsilon$ and
    describe the difference (referee report of
    [`proofs/sharp-bound-n5-graph-renormalization.md`](proofs/sharp-bound-n5-graph-renormalization.md),
    §4). The tangent-disk mechanism of that note's Lemma 2 is what such a statement would need. It
    would prove finiteness directly and avoid (K).
12. **Gluing by completeness near $0$.** Near $0$ a child orbit collects its states from a growing
    number of parent orbits (9, 105, 1 561 for the orbit of $0$ at levels 1–3), all glued into the token
    components of the main one at distance $0$ or $1$
    ([`proofs/sharp-bound-n5-atlas.md`](proofs/sharp-bound-n5-atlas.md) §4.6). A forward-type
    statement would explain this: every lattice point of the right $\Gamma$-class near $0$, with internal
    coordinate in a window of size $c/\delta$, lies in one of boundedly many large token components
    whose mutual distance is bounded. On the chord line the analogue is the passage model set
    (Proposition 13 of the orbit-of-zero note). Test first how much of the window near $0$ the large
    components fill, at two levels.
13. **Renormalize the radius instead of the plane.** Worked out in
    [`proofs/sharp-bound-n5-rim-graph.md`](proofs/sharp-bound-n5-rim-graph.md): a uniform bound on
    the diameter of the rim graph (parent-radius orbits of a child orbit, joined by rim letters)
    gives finiteness without (T); the data give at most 29, and the bound is open. Items 38–41 are
    its follow-ups.
14. **Box types for a renormalization of (K).** Every token component sits in one box of the grid of
    fence columns and rows of its seed; box widths are golden-rotation return times to an arc of length
    $\kappa_0\delta$, whose zoomed return map is exactly $\varepsilon^2$-periodic. Compute the graph of
    boxes joined by connectors along an orbit, in zoomed coordinates, at two levels $\delta$ and
    $\varepsilon^2\delta$, and test whether it is the same finite graph up to $O(\delta)$. A box type
    must record the physical position and the rotation index, not only the index box (referee of the
    (T) note, §4).
15. **The word behind the cut-set extent at $\delta = 1/55$.** The closure's largest centre has
    internal modulus $1407.2$, while about $1.2 \cdot 10^5$ sampled orbits reach only $1223.05$. Find
    that word map and count its connectors and token components; it is a strong test of (K) and of
    the constant in Conjecture A.
16. **A uniform diameter from the hub.** The hub's eccentricity is 3–5 on every named orbit and at
    most 6 on 878 random ones. A non-additive version of Theorem 3 of the component-graph note would
    give Conjecture A, not just (B): show that births at each step lie within a fixed distance of the
    image of the hub, not just of some image.
17. **Births in the component graph.** Each $\varepsilon$-step creates new components within a few
    connectors of the images of the previous level (component-graph note, Computation 4.6(5);
    transport note §5.4), and every child component outside $|y|<0.75$ is born. Find where they come
    from: test whether every birth at $\varepsilon\delta$ is the $\varepsilon$-image of a region of
    the parent outside the success region $G$ (item 18), which would make the coverage step a
    statement about $G$ alone.
18. **The success region $G$ of the $\varepsilon$-transport.** Whether $\varepsilon y$ lies in the
    child orbit is a function of the physical position of $y$, up to a thin layer; $G$ contains
    $|y|<1$ (for the orbit of $0$, every $y$ with $|y|<1.067$ at levels $0$–$3$), consists of whole
    clusters of the orbit, and fills about $68\%$ of every large orbit. Describe $G$ by circles and
    test whether it is the set where the transport words of the four generators act: the
    two-dimensional analogue of the one-line window and the natural domain for the forward step
    (R1). The disk curvatures differ, so the correspondence can only be partial; locate where it
    breaks.
19. **Finite proofs of the local transport lemmas.** The forward half of any renormalization of the
    component graph needs: domains of the 11- and 13-token detour words that join the images of
    $w_1$-edges where the 3-token transport word fails (transport note, Theorem 4 and §5);
    a covering proof for connector transport (two tokens and one letter, the letter possibly
    exchanged) by a cell decomposition in circles of radii $r$ and $\varphi^3r'$; and, for each
    nonzero chart of the atlas note, its own word list near the 3–10 circles that cut the chart-$0$
    words ((A1)–(A3) of Theorem 8 there). These are finite problems, but by Proposition 7 of the atlas
    note they cannot give the reverse-type step without a gluing mechanism (items 10–13).
20. **Level 4 of the orbit of $0$.** It has $7.6\cdot10^7$ states, above the memory used here. The
    level-3 marginal satellites (rescaled extent $1.53$) are the first test of whether births grow
    into permanent satellites or merge into hubs.
21. **A two-dimensional version of the window self-similarity.** The one-line first-return map to
    the blocked window satisfies $R_{\varepsilon\delta}=R_\delta^{-1}$ exactly (Proposition 2 of
    [`proofs/sharp-bound-n5-chaining.md`](proofs/sharp-bound-n5-chaining.md)). The rescaled extents of
    the largest token components converge along $\delta\varepsilon^k$ ($15.64, 15.73, 15.75$;
    $23.13, 23.63, 23.65$; $32.25, 33.49, 33.51$). Look for the limit object: a piecewise translation
    in rescaled coordinates whose components are the limits of the large token components.
22. **Tokens of length 4.** The critical words factor through $u_1=AAbb$, $u_2=abAA$, $u_3=bbAB$, which
    realize the rotation of the long segment $[-\varphi^2E,\varphi^2E]$. Redo the token-component analysis
    of the chaining note with the $u$-tokens and their mirror images; the components may be simpler,
    and the offset-line holes of the long segment are one-sided at $-\varphi^{-1}$ and $\pm\varphi^2$.
23. **The symmetry behind the equal fence widths.** The critical width $\kappa(\delta)\delta$ of the
    fence is the same, to six digits at every $\delta$ tested, for the corner $-F$ (domains $U_1,U_2$) and
    for the corner $X^\ast=-\varphi^2E+2\bar E$ (domain $\overline{U_2}$). Find the isometry of the system
    that carries one configuration to the other; it may organize all corners into a few classes.
24. **A sharper constant in (T).** The proved bound is $72.07/\delta$, the data reach $34.3/\delta$
    and index ranges $3.0/\delta$ against the proved $5.24/\delta$. Combine the forward fence at $-F$
    with the backward fence at $+F$ (its image under $z\mapsto-z$) and with the row holes of the chaining
    note's Theorem 1, which are wider than the fence on rows near the chord.
25. **Sharp constants of the chord cut-off.** Prove that the chord exit of the orbit of $0$ at level
    $k$ is exactly $(F_{3k+7}-1)/2$ for every $k$ (checked at the first levels), using the exact slopes
    ($\sqrt5$ and $5$) of the tight tests at all breakpoints, and determine $\liminf$ and $\limsup$ of
    $\delta K(\delta)$ and of $\delta M_0(\delta)$. For single runs and chord passages from every
    start, the computed $\delta\sup L$ lies in $[1.8, 2.6]$ (runs) and is about $1.05$ (chord seeds),
    against the proved $\varphi^3=4.24$; a gap theorem for the union of the holes at all breakpoints
    should give the sharp values.
26. **The tight first returns in the conjugate coordinate.** The chord part of the orbit of $0$
    reaches conjugate modulus $\Theta(1/\delta)$
    ([`proofs/sharp-bound-n5-conjugate.md`](proofs/sharp-bound-n5-conjugate.md) Theorem 6). A scalar
    form of (R-core-t): every first return to the tight windows adds at most $C/\delta$ to the
    conjugate coordinate. Test it with `orbit --conj-points` on the tight samples of
    `sharp-lower-bound-limit-system.md` §5, then look for a proof.
27. **A height function beyond the chord words.** $\operatorname{Re}(\sigma x/\sigma E) -
    \operatorname{Re}(x/E)$ drops by exactly $2\sqrt5$ under each chord word. Look for a
    similar function, or a finite family of them, that is monotone along the first returns to the
    tight windows.
28. **A speed limit at $r_c$.** In the orbit of $0$ at $r_c$ the largest conjugate modulus in
    breadth-first generation $g$ is the chord rate $1.514\,g$. Is the chord the fastest escape route, for
    every starting point?
29. **The conjugate cut-off for $n = 8, 10, 12$.** The analogue of Theorem 6 of
    `sharp-bound-n5-conjugate.md` for the chord of $n = 10$ and the self-similar chord families at $p^\ast$
    for $n = 8, 12$: a lower bound of order $1/\delta$ on the conjugate reach, and the exit index.
30. **The transverse cascade at $r_c$.** Large orbits at $r_c$ run along chord-parallel lines at
    offsets $\pm\tfrac12\varphi^{-m}$, $\pm\tfrac{\sqrt5}2\varphi^{-m}$
    ([`proofs/sharp-bound-n5-critical-orbits.md`](proofs/sharp-bound-n5-critical-orbits.md) §4.3).
    Find the finitely many words that carry a run ending near a tight point at offset $s$ to the
    lines of offset $\pm\varphi^{-j}s$, prove a renormalization of this one-dimensional offset map,
    and bound the number of runs per offset scale (§6.3 there). The uniform offset cut-off K3 is
    false; the corrected K3, which involves the internal coordinate, follows from Conjecture A.
31. **The renormalization inclusion at $E$, and the chord-free orbits.** Conjecture RI of
    [`proofs/sharp-bound-n5-critical-renormalization.md`](proofs/sharp-bound-n5-critical-renormalization.md)
    ($y\sim_\delta y'\Rightarrow\Psi y\sim_{\varepsilon\delta}\Psi y'$ near $E$, $\Psi(z)=E-\varepsilon(z-E)$,
    small $\delta$) would make the orbit of $-\zeta^2$ at $r_c$ infinite (witness already computed),
    showing that infinite orbits at $r_c$ need not contain chord points: the orbits of $-\zeta^2$ and
    $(-2,-2,-1,-2)$ provably never meet the chord and exceed $3\cdot10^7$ points. RI gives lower
    bounds only. The first exact instance suggested by its referee: RI on one chord-parallel line, in
    the linear model of the holes, with the second-order deviation controlled on lattice points by
    $|s||\sigma y|\ge1/4$; and an exact proof of RI from level 0 to level 1 by atoms.
32. **Where the window counts grow.** Under the $-\varepsilon$ zoom the sets
    $S_k=\Psi^{-k}(O(\Psi^kx)\cap B(E,\rho\varepsilon^k))$ grow and then stabilize. Test whether each new
    point of $S_{k+1}\setminus S_k$ comes from a lune point or a non-critical near miss at scale $k$;
    a "lune-free implies $S_{k+1}=S_k$" statement would be a usable form of the missing bound on
    $S_\infty$.
33. **The natural window for RI.** RI holds on all tested pairs within $0.76$ of $E$ and fails at
    $0.775$. Find the exact region (candidates: bounded by circles through $\bar E$ and through the
    critical point $(-1,1,-1,-1)$ at distance $\varphi^{-1}$; the failures involve a 40-point island),
    and test the zoom $-\varepsilon$ about the other natural centres $-\varphi^{-1}E$ and $\pm\varphi^2E$
    (breakpoints of the long-segment rotation).
34. **The sign flip at $E$ itself.** The first-return set of $E$ (zoomed $\eta=0$) at level $k+1$ is
    exactly the negative of that at level $k$, for $k=3,4$ (and level 5 equals levels 1 and 3), so at
    $E$ the unit $-\varepsilon$ renormalizes the returns with period one, although cuts cannot match
    ([`proofs/sharp-bound-n5-period-two.md`](proofs/sharp-bound-n5-period-two.md) §6.5). Prove
    $R_k(0)=(-1)^{k-3}R_3(0)$ for all $k\ge3$ (the non-linear return defects $\tau$ with
    $g(E)=Q'+\varepsilon^k\tau$ satisfy $\tau_{k+1}=-\tau_k$), and test whether it extends to other
    points with an extra symmetry. A test case, not a route to finiteness.
35. **Prove the chord-line model set.** At levels $0$–$4$ the orbit of $0$ meets $\mathbb RE$ in
    exactly the cut-and-project set $\{sE: s\in2\mathbb Z+\mathbb Z\varphi,\ sE\in D_1\cup D_2,\
    |\sigma s|\le T_k\}$ with $\delta_kT_k\to\varphi^7/10$
    ([`proofs/sharp-bound-n5-orbit-of-zero.md`](proofs/sharp-bound-n5-orbit-of-zero.md) Conjecture D).
    The inclusion "$\supseteq$" asks for explicit words reaching every window point (the chord passage
    gives only $2\mathbb Z[\varphi]\cap[-1,1)$; at $r_c$ the long-segment words supply the part
    $2\mathbb Z[\varphi]E$); the inclusion "$\subseteq$" is a conjugate bound on one line and would be
    the first exact upper bound on part of an orbit below $r_c$ that is not a finite computation. Its
    referee's next statement: on each chord-parallel line near the chord, the orbit is a finite union
    of passages of Fibonacci lengths, with window shapes depending only on $\varepsilon^{-k}m$.
36. **A line graph for the orbit of $0$.** The chord-parallel lines met by $O_{r_k}(0)$ near the chord
    are the same in rescaled offset $d/\delta_k$ at levels 1–4, with $\delta d'$ changing sign each
    level. Tabulate each line's window in $(s,\delta s')$ and the letters connecting lines; a finite
    line graph that repeats with period two would be a checkable renormalization statement for this
    orbit, and with Theorem 11 of that note would bound $M_0$. A concrete test: record, for each run at
    level $k+1$, the run at level $k$ whose $\varepsilon$-image it extends, and check whether this run
    graph is the same at every level.
37. **Exceptional set versus growth exponent.** The orbit of $0$ at $r_c$ has box-counting dimension
    about $1.8$, close to the exponent of $|O_r(0)|$ in $1/(r_c - r)$. Test this relation on other
    orbits and for $n = 8, 12$, and ask whether the closure of the cut set at $r_c$ has measure zero.
38. **The exact gluing windows of the rim.** Parent orbits are glued only along the two arcs of the
    lens boundary, and in the data only in seven fixed angular windows per quarter-arc (rim note
    §4.2; for example $[14.26^\circ,14.97^\circ]$ about $-1$). Find their endpoints exactly: test
    whether they are arcs of the cut set at $r_c$ or images of critical points under short words,
    and whether the parent orbits met in each window are of finitely many types.
39. **A rim model set.** Describe the essential gluing sites in the coordinates (angle, rescaled
    internal coordinate $\delta\sigma y$) at several levels, and test whether they converge to a
    fixed set, as the chord-line model set does on the chord. A proved limit description would make
    rim distances a finite problem.
40. **A rim renormalization with additive growth.** Under $y\mapsto\varepsilon y$ the rim depth of
    every non-singleton piece never increases, and every new piece lies within 2 rim steps of an
    image (rim note §4.4, three level pairs). Proving both would give $R_k=O(k)$, which suffices
    for finiteness through the rim recursion. The coverage half is the reverse-type step.
41. **Rim graphs as a function of the step.** The rim-graph diameter grows with the step ratio (at
    most 4, 8, 11, 20, 29, 84 for ratios $0.99$, $0.9$, $\varphi^{-1}$, $1/2$, $\varepsilon$,
    $\varepsilon^2$), and over a fixed base like $1/\delta$ ($12,38,164$). A one-step bound
    $R(r_0,r)=O(1/\delta)$ from a fixed certified radius would give Conjecture A directly; test
    its constant on more orbits and radii.

## Formalization

Depends on: `TDCSG/CriticalRadius/Certificate.lean`, [`certificates.md`](certificates.md) §7 and
[`relative-certificates.md`](relative-certificates.md) §11.

1. **A verified checker.** The certificate checker as a Lean function on a certificate data type, with
   a soundness theorem `check cert = true → TDCSG.Certificate n r (arcs cert)`.
2. **The certificate theorem in Lean.** A proof of `TDCSG.CutSetCertificate n` (the cell
   decomposition of a finite arc arrangement), which would make `TDCSG.finite_GG_of_certificate`
   applicable.
3. **The non-norm lemma and the relative-certificate theorem in Lean.** Lemma 2.2 and Theorem 3.1 of
   `sharp-lower-bound-n5.md`, and Theorem 4.2 of `sharp-lower-bound-combined.md` (with Theorem H of
   `relative-certificates.md` as its window-free case).
4. **A `FiniteBelowTen` proposition** for $n = 10$, matching the refereed Theorem B of
   [`proofs/critical-radius-n10.md`](proofs/critical-radius-n10.md), alongside the existing ones for
   $n = 5, 8, 12$.

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
