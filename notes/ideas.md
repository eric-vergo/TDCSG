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
