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

Depends on: [`certificates.md`](certificates.md) (the exact generator and checker),
[`proofs/sharp-lower-bound-n5.md`](proofs/sharp-lower-bound-n5.md),
[`proofs/sharp-lower-bound-n8.md`](proofs/sharp-lower-bound-n8.md) and
[`proofs/sharp-lower-bound-combined.md`](proofs/sharp-lower-bound-combined.md).

1. **The limiting straight-cut system.** In coordinates zoomed by $\varepsilon^{-k}$ about a critical
   point, the collapsing faces converge to a piecewise isometry with straight cuts and a finite germ
   set. Certify that this limit system has uniformly bounded orbits, and prove that from an explicit
   level on the level-$k$ induced system coincides with it face by face
   (`sharp-lower-bound-combined.md` §7, suggestion 4; Conjecture S (S2) of `sharp-lower-bound-n8.md`).
2. **Hybrid certificates.** Combine one fixed bulk certificate at $r_c$ with a closure of the induced
   system inside the windows at $r_k$, using the finite word set of Proposition 4.4 of
   `sharp-lower-bound-combined.md`, to certify levels the full closure cannot reach.
3. **Self-similarity of the critical system.** The annulus reduction of (R-bulk): compute the
   first-return systems on consecutive annuli at $r_c$ and test whether their combinatorics stabilize
   (`sharp-lower-bound-combined.md` §7, suggestion 3).
4. **Renormalization of cut sets.** Compare $K(r)$ at $\delta$ and at $\delta/u$ ($u = \varphi^3$,
   $1 + \sqrt2$, $2 + \sqrt3$) exactly near the critical points. For $n = 8$ the cut set itself has no
   locally finite limit (`sharp-lower-bound-n8.md` §4), so the comparison is meaningful for the induced
   pseudogroups, not for $K(r)$.
5. **Certifying the n = 5 level two.** The level-two closure is computed by one program with
   floating-point ordering; it needs the engine's checker with a symmetry-reduced or streaming mode, or
   an error analysis and an independent checker (`sharp-lower-bound-n5.md` §5.1).
6. **Interval of validity.** The symbolic arc set of $K(r)$ is the same on a whole interval of radii,
   which ends only at an event (a tangency to $\partial D_p$, a triple point, or two endpoints changing
   order) at an exact algebraic radius. The engine computes that interval (`tdcsg-orbit
   validity-interval`); applied to the deepest certificates it would extend each certified range to its
   next event without a larger closure.
7. **Memory.** A packed arc store (fixed-width coefficients, as in `Store.lean`) would roughly
   halve the generator's memory, which limits $n = 5$ below the jump at $\delta \approx 0.0181$.

## Formalization

Depends on: `TDCSG/CriticalRadius/Certificate.lean` and [`certificates.md`](certificates.md) §7.

1. **A verified checker.** The certificate checker as a Lean function on a certificate data type, with
   a soundness theorem `check cert = true → TDCSG.Certificate n r (arcs cert)`.
2. **The certificate theorem in Lean.** A proof of `TDCSG.CutSetCertificate n` (the cell
   decomposition of a finite arc arrangement), which would make `TDCSG.finite_GG_of_certificate`
   applicable.
3. **The non-norm lemma and the relative-certificate theorem in Lean.** Lemma 2.2 and Theorem 3.1 of
   `sharp-lower-bound-n5.md`, and Theorem 4.2 of `sharp-lower-bound-combined.md`.
4. **A `FiniteBelowTen` proposition** for $n = 10$, matching the refereed Theorem B of
   [`proofs/critical-radius-n10.md`](proofs/critical-radius-n10.md), alongside the existing ones for
   $n = 5, 8, 12$.
