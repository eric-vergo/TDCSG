# Ideas for later rounds

Authors: Eric Vergo, Claude

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

1. **Monotone growth of first-return sets across levels.** For $n = 12$, first-return sets and core
   orbit classes are observed only to grow with the level (`sharp-lower-bound-n12.md` §8). Prove it.
   The natural argument, that the rescaled disks contain the previous ones so orbit monotonicity in
   $r$ applies, fails: the rescaled generators rotate about different centres, so the level-$m$ and
   level-$(m+1)$ systems are not one system at two radii. A proof would reduce (R-core-t₁₂) to a
   bound on the classes of one limit relation.
2. **Diophantine control of lune points uniform in the level.** Every observed change between
   levels is preceded by a lune point (a lattice point where the circle test and its tangent-line
   test disagree). The lune lemma controls them only at bounded zoomed internal radius; a bound
   uniform in the level, or a count of lune points at growing internal radius, would control where
   changes can occur.
3. **Exact period one for $n = 12$ from a deeper level.** Exact period one is refuted from every
   starting level $m_0 \le 3$; whether it holds from some $m_0 \ge 4$ is open, and the data fit both
   answers; the smallest internal radius of a change grows with the level, so a test needs
   deeper levels on samples of larger internal radius, or an argument.
4. **Period-two test for $n = 8$ and $n = 10$.** The total-positivity rule predicts period two for
   both (units of norm $-1$). $n = 8$ has only floating-point germ samples, $n = 10$ nothing; repeat
   the exact tight-point tests of `sharp-lower-bound-limit-system.md` §5 for both.
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
9. **The tight first returns in the conjugate coordinate.** The chord part of the orbit of $0$ reaches
   conjugate modulus $\Theta(1/\delta)$ ([`proofs/sharp-bound-n5-conjugate.md`](proofs/sharp-bound-n5-conjugate.md)
   Theorem 6). A scalar form of (R-core-t): every first return to the tight windows adds at most
   $C/\delta$ to the conjugate coordinate. Test it with `orbit --conj-points` on the tight samples of
   `sharp-lower-bound-limit-system.md` §5, then look for a proof.
10. **Sharp constants of the chord cut-off.** Prove that the chord exit at level $k$ is exactly
    $(F_{3k+7}-1)/2$ for every $k$, using the exact slopes ($\sqrt5$ and $5$) of the tight tests at all
    breakpoints, and determine $\liminf$ and $\limsup$ of $\delta K(\delta)$ and of $\delta M_0(\delta)$.
11. **A speed limit at $r_c$.** In the orbit of $0$ at $r_c$ the largest conjugate modulus in
    breadth-first generation $g$ is the chord rate $1.514\,g$. Is the chord the fastest escape route, for
    every starting point?
12. **The conjugate cut-off for $n = 8, 10, 12$.** The analogue of Theorem 6 of
    `sharp-bound-n5-conjugate.md` for the chord of $n = 10$ and the self-similar chord families at $p^\ast$
    for $n = 8, 12$: a lower bound of order $1/\delta$ on the conjugate reach, and the exit index.

13. **The transverse cascade at $r_c$.** Large orbits at $r_c$ run along chord-parallel lines at
    offsets $\pm\tfrac12\varphi^{-m}$, $\pm\tfrac{\sqrt5}2\varphi^{-m}$
    ([`proofs/sharp-bound-n5-critical-orbits.md`](proofs/sharp-bound-n5-critical-orbits.md) §4.3).
    Find the finitely many words that carry a run ending near a tight point at offset $s$ to the
    lines of offset $\pm\varphi^{-j}s$, and prove a renormalization of this one-dimensional offset
    map; with a cut-off at offset of order $\delta$ below $r_c$ (Conjecture K3 there) it would bound
    orbits level by level.
14. **Infinitude of a chord-free orbit.** The orbits of $-\zeta^2$ and $(-2,-2,-1,-2)$ at $r_c$
    provably never meet the chord (congruence classes modulo $2(1-\zeta)$) and exceed $3 \cdot 10^7$
    points. Proving one of them infinite, for instance by a family of partial isometries of
    chord-parallel lines closed under rescaling as for $n = 8$, would show that infinite orbits at
    $r_c$ need not contain chord points.
15. **The long chord $[-\varphi^2E, \varphi^2E]$.** Its ends are critical points, and populated
    chord-parallel lines are spread uniformly over its full length. Test whether it carries an exact
    interval exchange at $r_c$ with the golden rotation on $E'E$ as induced map.
16. **A height function beyond the chord words.** $\operatorname{Re}(\sigma x/\sigma E) -
    \operatorname{Re}(x/E)$ drops by exactly $2\sqrt5$ under each chord word. Look for a
    similar function, or a finite family of them, that is monotone along the first returns to the
    tight windows.
17. **Exceptional set versus growth exponent.** The orbit of $0$ at $r_c$ has box-counting dimension
    about $1.8$, close to the exponent of $|O_r(0)|$ in $1/(r_c - r)$. Test this relation on other
    orbits and for $n = 8, 12$, and ask whether the closure of the cut set at $r_c$ has measure zero.
18. **Bounded chaining of token components.** Conjecture B$^\sharp$(K) of
    [`proofs/sharp-bound-n5-chaining.md`](proofs/sharp-bound-n5-chaining.md): every word map is
    realized with boundedly many non-token letters (observed: at most 7 on 11 orbits at 10 radii;
    6, 5, 6 along $\delta=\varphi^{-3k}/55$). The single-line window map is the
    wrong object there, because connectors between large token components occur all over the disks.
    Find the renormalization of the component graph.
19. **A two-dimensional free-token cut-off.** Theorem 1 of
    [`proofs/sharp-bound-n5-chaining.md`](proofs/sharp-bound-n5-chaining.md) bounds free-token walks on
    one chord-parallel line. Prove the same $O(1/\delta)$ internal bound for walks that mix the tokens
    of $\mathbb RE$ and $\mathbb R\bar E$ (B$^\sharp$(T); observed $\delta\cdot$extent $\le34.3$ from
    134 000 random seeds). It is a statement about a piecewise translation of the plane on six
    explicit convex domains; in coordinates $X=sE+t\bar E$ both $s$ and $t$ perform the golden
    rotation modulo 2.
20. **The word behind the cut-set extent at $\delta = 1/55$.** The closure's largest centre has internal
    modulus $1407.2$, while about $1.2 \cdot 10^5$ sampled orbits reach only $1223.05$. Find that word map
    and decompose it into chord runs; it is the strongest test of Conjecture B$^\ast$ in hand.
21. **Sharp constant of the single run.** Computed $\delta \sup L$ lies in $[1.8, 2.6]$ against the proved
    $5.86$; using the bad intervals at all four breakpoints in the three-distance argument should give
    the sharp $\limsup$.
22. **The sign flip at $E$ itself.** The first-return set of $E$ (zoomed $\eta=0$) at level $k+1$ is
    exactly the negative of that at level $k$, for $k=3,4$ (and level 5 equals levels 1 and 3), so at
    $E$ the unit $-\varepsilon$ renormalizes the returns with period one, although cuts cannot match
    ([`proofs/sharp-bound-n5-period-two.md`](proofs/sharp-bound-n5-period-two.md) §6.5). Explain it
    (the non-linear return defects $\tau$ with $g(E)=Q'+\varepsilon^k\tau$ satisfy
    $\tau_{k+1}=-\tau_k$), and test whether it extends to other points with an extra symmetry.
23. **A measure-theoretic period two.** Lune points per tight excursion fall by about $\varepsilon$ per
    level while visits near critical points stay bounded (`sharp-bound-n5-period-two.md` §6.4). Prove
    that the zoomed starts whose level-$k$ excursion meets a lune have measure $O(\varepsilon^k)$; with
    the lune criterion this would give exact period two for almost every start from a finite level,
    and reduce the problem to an exceptional set.
24. **Return defects as the finite object.** Non-linear returns of a zoomed start are coded by lattice
    defects $\tau=\varepsilon^{-k}(g(E)-Q')$ in a bounded window of $\Lambda\subset\mathbb C^2$ if the
    internal drift is $O(\varphi^{3k})$. Tabulate the defect sets per level and parity; stabilization of
    the even and odd defect sets would be a finite, checkable form of period two.
25. **Period two for orbit partitions, and level 5 without selection.** The $n = 5$ period-two tests
    of `sharp-bound-n5-period-two.md` cover first-return sets at $2\to4$ fully but orbit partitions
    only at $1\to3$, and level 5 only for starts whose excursions stay below $1.2 \cdot 10^8$ points
    (biased towards stable starts). A packed or disk-backed point store would allow the $2\to4$
    partition test (Conjecture M$_5$) and the capped level-5 starts.
26. **Prove the chord-line model set.** At levels $0$–$4$ the orbit of $0$ meets $\mathbb RE$ in
    exactly the cut-and-project set $\{sE: s\in2\mathbb Z+\mathbb Z\varphi,\ sE\in D_1\cup D_2,\
    |\sigma s|\le T_k\}$ with $\delta_kT_k\to\varphi^7/10$
    ([`proofs/sharp-bound-n5-orbit-of-zero.md`](proofs/sharp-bound-n5-orbit-of-zero.md) Conjecture D).
    The inclusion "$\supseteq$" asks for explicit words reaching every window point (the chord passage
    gives only $2\mathbb Z[\varphi]\cap[-1,1)$); the inclusion "$\subseteq$" is a conjugate bound on one
    line and would be the first exact upper bound on part of an orbit below $r_c$ that is not a
    finite computation.
27. **A line graph for the orbit of $0$.** The chord-parallel lines met by $O_{r_k}(0)$ near the chord
    are the same in rescaled offset $d/\delta_k$ at levels 1–4, with $\delta d'$ changing sign each
    level. Tabulate each line's window in $(s,\delta s')$ and the letters connecting lines; a finite
    line graph that repeats with period two would be a checkable renormalization statement for this
    orbit, and with Theorem 11 of that note would bound $M_0$.
28. **Why $\varepsilon\,O_{r_k}(0)$ sits inside $O_{r_{k+1}}(0)$ near $0$.** Every $y\in O_{r_k}(0)$ with
    $|y|<1.07$ has $\varepsilon y\in O_{r_{k+1}}(0)$ ($k=0,1,2$). Find, for each generator $g$, a word
    $W_g$ with $W_g(\varepsilon y)=\varepsilon g(y)$ at level $k+1$; the disk curvatures differ, so the
    correspondence can only be partial; locate where it breaks.
29. **Sharp passage constant on the chord.** For chord seeds the computed $\sup\delta L$ is about $1.05$
    against the proved $\varphi^3=4.24$; a gap theorem for the union of the three holes (at $b_1$, $b_3$
    and $1$) should give the sharp value.
30. **A two-dimensional version of the window self-similarity.** The one-line first-return map to
    the blocked window satisfies $R_{\varepsilon\delta}=R_\delta^{-1}$ exactly (Proposition 2 of
    [`proofs/sharp-bound-n5-chaining.md`](proofs/sharp-bound-n5-chaining.md)). The rescaled extents of
    the largest token components converge along $\delta\varepsilon^k$ ($15.64, 15.73, 15.75$;
    $23.13, 23.63, 23.65$; $32.25, 33.49, 33.51$). Look for the limit object: a piecewise translation
    in rescaled coordinates whose components are the limits of the large token components.
31. **Prove the renormalization inclusion at $E$.** Conjecture RI of
    [`proofs/sharp-bound-n5-critical-renormalization.md`](proofs/sharp-bound-n5-critical-renormalization.md)
    ($y\sim_\delta y'\Rightarrow\Psi y\sim_{\varepsilon\delta}\Psi y'$ near $E$, $\Psi(z)=E-\varepsilon(z-E)$)
    would follow from a finite check: for each first-return germ $g$ of a four-window closure at $r_c$,
    a word realizing $\Psi g\Psi^{-1}$ on $\Psi(\operatorname{dom}g)$, with containment of arc-bounded
    domains. It would make the orbit of $-\zeta^2$ infinite (witness already computed).
32. **Where the window counts grow.** Under the $-\varepsilon$ zoom the sets
    $S_k=\Psi^{-k}(O(\Psi^kx)\cap B(E,\rho\varepsilon^k))$ grow and then stabilize. Test whether each new
    point of $S_{k+1}\setminus S_k$ comes from a lune point or a non-critical near miss at scale $k$, as in
    the lune criterion of the period-two note; a "lune-free implies $S_{k+1}=S_k$" statement would be a
    usable form of the missing bound on $S_\infty$.
33. **The natural window for RI.** RI holds on all tested pairs within $0.76$ of $E$ and fails at
    $0.775$. Find the exact region (candidates: bounded by circles through $\bar E$ and through the
    critical point $(-1,1,-1,-1)$ at distance $\varphi^{-1}$), and test the zoom $-\varepsilon$ about the
    other natural centres $-\varphi^{-1}E$ and $\pm\varphi^2E$ (breakpoints of the long-segment rotation).
34. **Tokens of length 4.** The critical words factor through $u_1=AAbb$, $u_2=abAA$, $u_3=bbAB$, which
    realize the rotation of the long segment $[-\varphi^2E,\varphi^2E]$. Redo the token-component analysis
    of the chaining note with the $u$-tokens and their mirror images; the components may be simpler,
    and the offset-line holes of $M$ are one-sided at $-\varphi^{-1}$ and $\pm\varphi^2$.
35. **Fences for the connectors.** The cut-off of token components
    ([`proofs/sharp-bound-n5-token-components.md`](proofs/sharp-bound-n5-token-components.md)) comes from
    a wall: the $\bar E$-line through $-F$ carries no forward $E$-step below $r_c$, up to dead ends. Look
    for walls of the same kind for the full group in the lifted state space: sets of states, defined by
    position relative to finitely many lines through corners, that no letter crosses except through dead
    ends. A wall family with spacing $O(1/\delta)$ in each of the five rotated frames would give (K).
36. **The symmetry behind the equal fence widths.** The critical width $\kappa(\delta)\delta$ of the
    fence is the same, to six digits at every $\delta$ tested, for the corner $-F$ (domains $U_1,U_2$) and
    for the corner $X^\ast=-\varphi^2E+2\bar E$ (domain $\overline{U_2}$). Find the isometry of the system
    that carries one configuration to the other; it may organize all corners into a few classes.
37. **A sharper constant in (T).** The proved bound is $72.07/\delta$, the data reach $34.3/\delta$
    and index ranges $3.0/\delta$ against the proved $5.24/\delta$. Combine the forward fence at $-F$
    with the backward fence at $+F$ (its image under $z\mapsto-z$) and with the row holes of the chaining
    note's Theorem 1, which are wider than the fence on rows near the chord.
38. **Box types for a renormalization of (K).** Every token component sits in one box of the grid of
    fence columns and rows of its seed; box widths are golden-rotation return times to an arc of length
    $\kappa_0\delta$, whose zoomed return map is exactly $\varepsilon^2$-periodic. Compute the graph of
    boxes joined by connectors along an orbit, in zoomed coordinates, at two levels $\delta$ and
    $\varepsilon^2\delta$, and test whether it is the same finite graph up to $O(\delta)$.
39. **Detours for the $w_1,w_2$ transport.** Transport of $w_3$-type token edges by $\varepsilon$ is proved,
    and the domain of the $w_1$ transport word is exactly cut by two circles of radius $\varphi^3r'$
    ([`proofs/sharp-bound-n5-graph-renormalization.md`](proofs/sharp-bound-n5-graph-renormalization.md)
    Theorems 3, 4). Near the two corners of the cut region, images are joined by 11- and 13-token detours
    through family-2 tokens. Compute the domains of these detour words and test whether, with the
    two-circle domain, they cover every $w_1$-edge whose endpoints both lie in the success region.
40. **The success region $G$ of the $\varepsilon$-transport.** Whether $\varepsilon y$ lies in the
    child orbit is a function of the physical position of $y$, up to a thin layer. The region contains
    $|y|<1$ and $|y|\ge2.7$, and it fills $68\%$ of every large orbit. Describe $G$ by circles,
    and test whether $G$ is the set where the transport words of the four generators act. That would
    be the two-dimensional analogue of the one-line window and the natural domain for (R1).
41. **Births in the component graph.** Each $\varepsilon$-step creates new large components within
    1–2 connectors of the image of the previous level (component-graph note, Computation 4.6(5)). Find
    where they come from: test whether every birth at $\varepsilon\delta$ is the $\varepsilon$-image of
    a region of the parent that lies outside $G$, which would make (R2) a statement about $G$ alone.
42. **A uniform diameter from the hub.** The hub's eccentricity is 3–5 on every named orbit and at
    most 6 on 878 random ones. A non-additive version of Theorem 3 of the component-graph note would
    give Conjecture A, not just (B): show that births at each step lie within a fixed distance of the
    image of the hub, not just of some image.
43. **Level 4 of the orbit of $0$.** It has $7.6\cdot10^7$ states, above the memory used here. The
    level-3 marginal satellites (rescaled extent $1.53$) are the first test of whether births grow
    into permanent satellites or merge into hubs.
44. **The local half of the atlas recursion.** Theorem 8 of
    [`proofs/sharp-bound-n5-atlas.md`](proofs/sharp-bound-n5-atlas.md) needs, besides three global
    hypotheses, the local statements (A1)–(A3): edge transport per chart, a cover of the parent region
    by chart regions, and bounded transitions (exactly 2 connectors in the data). Each is a cell problem
    in circles of radii $r$ and $\varphi^3r'$; for nonzero charts the chart-$0$ transport words are cut
    by 3–10 circles, so each chart needs its own word list near those circles.
45. **A covering proof for connector transport.** For each letter, the transport words (two tokens
    and one letter, the letter possibly exchanged) cover the letter's domain inside the success region
    except an orbit-free lune in a gap. Prove the covering on an explicit region by a cell decomposition
    in circles of radii $r$ and $\varphi^3r'$, using the tangent-disk lemma at tight corners.
46. **Gluing by completeness near $0$.** Near $0$ a child orbit collects its states from a growing
    number of parent orbits (9, 105, 1 561 for the orbit of $0$ at levels 1–3), all glued into the token
    components of the main one at distance $0$ or $1$
    ([`proofs/sharp-bound-n5-atlas.md`](proofs/sharp-bound-n5-atlas.md) §4.6). A forward-type
    statement would explain this: every lattice point of the right $\Gamma$-class near $0$, with internal
    coordinate in a window of size $c/\delta$, lies in one of boundedly many large token components
    whose mutual distance is bounded. On the chord line the analogue is the passage model set
    (Proposition 13 of the orbit-of-zero note). Test first how much of the window near $0$ the large
    components fill, at two levels.
47. **Renormalize the radius instead of the plane.** By orbit monotonicity the orbits at the parent
    radius $r$ of the points of a child orbit at $r'>r$ partition it, and they are joined only by letters
    acting in the rim $r<|y\mp1|\le r'$. If a shortest path in the child needs boundedly many rim letters,
    uniformly, then $D(\varepsilon\delta)\le(P+1)D(\delta)+P$ and (B) follows. Compute the rim-crossing
    number on the orbit of $0$ at levels 1–3 and on random children; the rim is an $O(\delta)$ annulus,
    so a bound on its crossings is a statement about a thin set, which may be easier to control than
    the lunes of the atlas.

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
