# Ideas for later rounds

Authors: Eric Vergo, Claude

Open directions that are not part of the current work. Each entry says what the question is and what it
depends on.

## The continuation gap

Depends on: [`proofs/analytic-radius.md`](proofs/analytic-radius.md) (the result $r_A(n) = \sec(\pi/n)$).

Functions on the union of the two open disks that are invariant under each disk's rotation are forced
to be constant once $r > r_A(n)$, while the piecewise group $GG_n(r)$ stays finite up to $r_c(n)$. The
piecewise group is what the two local symmetries generate when continuation across piece boundaries is
not imposed. The interval $(r_A, r_c)$ measures that freedom.

1. **Group structure inside the gap.** $GG_n(r)$ is one fixed group on $[1, r_A)$. List exactly the
   radii in $(r_A, r_c)$ at which the group changes, and the group order at each. Do they accumulate
   only at $r_c$? Computable with the exact orbit engine.
2. **Regularity scale.** For a function class $\mathcal{C}$ (smooth, Gevrey, Denjoy–Carleman
   quasi-analytic and non-quasi-analytic classes, continuous), let $r_{\mathcal{C}}(n)$ be the radius
   beyond which invariant functions in $\mathcal{C}$ are constant. Analytic classes give $r_A$.
   Do quasi-analytic classes all give $r_A$, and do non-quasi-analytic classes give thresholds that
   fill the gap up to $r_c$?
3. **Intermediate pseudogroups.** Allow continuation across some piece boundaries only (for example
   where the maps on adjacent pieces agree). This gives groups between $GG_n(r)$ and the analytic hull,
   each with its own critical radius.
4. **The ratio.** Is $(r_c - 1)/(r_A - 1)$ governed by the units of $\mathbb{Z}[\zeta_n]$, or is it
   elementary geometry?
5. **Laplace eigenfunctions.** Do invariant eigenfunctions survive at or below $r_A$? Relation to the
   Euclidean Hecke-group picture in [`analytic-continuation.md`](analytic-continuation.md).
