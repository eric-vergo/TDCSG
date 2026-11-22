# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: a guide to the notes

Authors: Eric Vergo, Claude

The target is statement **(B)**: $GG_5(r)$ is finite for every $r<r_c=\sqrt{3+\varphi}$. Infinitude
at and above $r_c$ is proved in Lean (`infinite_GG_five`), so (B) is the remaining half of
$r_{\rm crit}(5)=r_c$. **(B) is not proved.** Twelve notes in [`proofs/`](proofs/) attack it. This
guide says what each proves, how they depend on each other, what the present reduction is, which
formulations are refuted or closed, and which new ideas have been proposed. Every statement below
is labelled **proved** (written proof, refereed unless said otherwise), **computed** (exact
arithmetic unless said otherwise) or **conjectured**; the notes themselves carry the details.

## Terms

- $\delta=r_c^2-r^2$ is the *defect* of the radius $r$, and $\varepsilon=\varphi^{-3}$, a unit of
  $\mathbb Z[\varphi]$. The *level radii* are $r_k^2=r_c^2-\varepsilon^k/10$; passing from one level
  to the next multiplies the defect by $\varepsilon$.
- Every group element acts at each point as $x\mapsto\zeta^jx+t$ with $t$ in $\mathbb Z[\zeta]$.
  The *internal* (or *conjugate*) *coordinate* of a lattice point $y$ is $\sigma(y)$, where $\sigma$
  is the Galois automorphism $\zeta\mapsto\zeta^2$. $GG_5(r)$ is finite exactly when the conjugates
  $\sigma(t)$ of all translation parts are bounded (proved in Lean:
  `TDCSG.Five.finite_GG_iff_conjugatesBounded`). Write $M(r)$ for the supremum of $|\sigma(t)|$.
- The *chord* is the segment $[-E,E]$, $E=\zeta-\zeta^2$. At $r_c$ three words $w_1,w_2,w_3$ act on
  it as translations that together form the golden rotation $t\mapsto t+2\varphi^{-1}\pmod 2$; this
  is why the orbit of $0$ is infinite at $r_c$.
- A *token* is one of the twelve words obtained from $w_1,w_2,w_3$ by the symmetries $z\mapsto-z$,
  $z\mapsto\bar z$. A token *acts* at a point when each of its letters acts there as the full
  rotation; it then translates the point along $E$ or along $\bar E$.
- A *token component* is a connected component of the graph that joins each point to its images
  under the tokens acting there. Its *internal diameter* is the largest $|\sigma(t)|$ over the
  translations $t$ of token paths inside it.
- A *connector* is a single letter $a^{\pm1}$ or $b^{\pm1}$ that moves its point: a step that is
  not part of a token.
- Orbits are *lifted* to states $(y,j)$, with $j\in\mathbb Z/5$ the rotation index of a word from
  the seed. Tokens keep $j$, and a connector changes it by $\pm1$; the states with a given $j$ form
  a *sheet*. The *component graph* of an orbit has its token components as vertices and an edge for
  each connector between two of them. $D(r)$ is the supremum of the diameters of these graphs.
- *Parent* and *child*: for an orbit at defect $\delta$, the child is the orbit at defect
  $\varepsilon\delta$ of $\varepsilon$ times the seed. A *renormalization* statement compares the
  two.

## The twelve notes

Listed in the order they build on each other. Each note's top paragraph records the referee's
verdict and links its report.

1. [`sharp-bound-n5-conjugate.md`](proofs/sharp-bound-n5-conjugate.md) ("Part I", "line 1").
   Proves that at $r_c$ the conjugate coordinate escapes along the chord at a constant rate, and
   that below $r_c$ ($0<\delta\le1/20$) the chord passage of the orbit of $0$ lasts between
   $0.059/\delta-1.18$ and $2.12/\delta$ steps; so no bound on conjugates can be independent of $r$. States Conjecture A,
   $M(r)\le C/\delta$. *Referee:* correct, several items after minor fixes; Corollary 8 is
   conditional on a certified relative certificate.
   ([report](proofs/referee-report-sharp-bound-n5-conjugate.md))
2. [`sharp-bound-n5-critical-orbits.md`](proofs/sharp-bound-n5-critical-orbits.md). The system at
   $r_c$: the chord survives opening the disks (so the limit of the systems below $r_c$ is
   infinite), exact holes of width about $\delta/\sqrt5$ of the chord words below $r_c$, the
   congruence classes modulo $2(1-\zeta)\mathbb Z[\zeta]$ (20 classes, the chord lines in only 2 of
   them, so orbits in the other 18 never meet the chord), and openness of finiteness at non-norm
   radii. *Referee:* all proofs correct, Theorem 2 after minor fixes; Conjecture K3 false as stated.
   ([report](proofs/referee-report-sharp-bound-n5-critical-orbits.md))
3. [`sharp-bound-n5-invariant.md`](proofs/sharp-bound-n5-invariant.md) ("line 4"). Proves that exact
   invariants, congruence classes and symmetries cannot prove (B), and that every chord run, from
   every starting point $sE+hN$ with $s\in[-1,1)$, ends within $5.86/\delta$ steps with internal
   translation at most $58.4/\delta+9.6$ ($0<\delta\le2/5$). *Referee:* correct after minor fixes;
   Conjecture B$^\ast$ restated in structural form.
   ([report](proofs/referee-report-sharp-bound-n5-invariant.md))
4. [`sharp-bound-n5-orbit-of-zero.md`](proofs/sharp-bound-n5-orbit-of-zero.md) ("Part II"). Extends
   the cut-off to every lattice seed on the chord and to every chord passage from any point
   ($<\varphi^3/\delta$ steps on the chord, $<2\varphi^3/\delta$ in general, conjugate change
   $<72.07/\delta+3.81$), proves exact chord-parallel coordinates and a tube theorem, and reduces
   finiteness of the orbit of $0$ to the level radii. Computed: period-two structure of the orbit
   of $0$ near critical points and a model set on the chord line (levels 0–4). *Referee:* correct,
   with range fixes. ([report](proofs/referee-report-sharp-bound-n5-orbit-of-zero.md))
5. [`sharp-bound-n5-period-two.md`](proofs/sharp-bound-n5-period-two.md). Tests the period-two
   conjecture at the tight points $\pm E,\pm\bar E$. Refutes it in its unrestricted form (exact);
   proves a positivity lemma explaining why only $\varepsilon^2$ can preserve the cuts, and that
   this gives no conjugacy. *Referee:* correct, some lemmas after minor fixes; recommends closing
   the first-return/lune-criterion formulation, and keeping the monotone orbit-class version
   (Proposition 4.5). ([report](proofs/referee-report-sharp-bound-n5-period-two.md))
6. [`sharp-bound-n5-critical-renormalization.md`](proofs/sharp-bound-n5-critical-renormalization.md).
   Proves K4: the long segment $[-\varphi^2E,\varphi^2E]$ carries at $r_c$ the rotation by $2\varphi$
   of $\mathbb R/2\varphi^2\mathbb Z$ with the chord rotation as first return. Proves K3 false and
   gives its corrected form. Computed: the zoom about $E$ by $-\varepsilon$ is an inclusion of orbit
   relations (Conjecture RI), never the reverse inclusion. *Referee:* correct, several items after
   minor fixes; RI false as first stated, restricted to small $\delta$.
   ([report](proofs/referee-report-sharp-bound-n5-critical-renormalization.md))
7. [`sharp-bound-n5-chaining.md`](proofs/sharp-bound-n5-chaining.md). Proves the cut-off for free
   token walks on every chord-parallel line and an exact self-similarity of the one-line window map.
   Computed: the breakpoint-window return map is not the dynamics, because token components are
   two-dimensional. Replaces B$^\ast$ by Conjecture B$^\sharp$ = (T) + (K) and proves
   B$^\sharp\Rightarrow$ (B). *Referee:* correct, after minor fixes; one negative computational
   claim corrected; the evidence for (K) is the component-graph diameter (6 to 9).
   ([report](proofs/referee-report-sharp-bound-n5-chaining.md))
8. [`sharp-bound-n5-token-components.md`](proofs/sharp-bound-n5-token-components.md) ("the (T)
   note"). **Proves (T)** by a fence (a line through the corner $-F$ that no forward token step
   crosses below $r_c$): every token component of any point has internal diameter
   $<72.07/\delta+41.82$ for $0<\delta\le2/5$ (and $<222.1$ for $\delta>2/5$). Consequently, at each
   fixed $r$, $GG_5(r)$ is finite iff $D(r)<\infty$. *Referee:* correct after minor fixes (wording
   only). ([report](proofs/referee-report-sharp-bound-n5-token-components.md))
9. [`sharp-bound-n5-component-graph.md`](proofs/sharp-bound-n5-component-graph.md). Proves which
   forms of (K) suffice (Proposition 1) and that a renormalization hypothesis (R) for the component
   graph implies (B) (Theorem 3). Computed: diameter at most 9 on every orbit where it was computed
   exactly (18 named orbits, 878 random ones), one hub per sheet. *Referee:* correct after minor
   fixes; (R) has content only with a fixed constant $b$; **Conjecture 5.1 false as stated**.
   ([report](proofs/referee-report-sharp-bound-n5-component-graph.md))
10. [`sharp-bound-n5-graph-renormalization.md`](proofs/sharp-bound-n5-graph-renormalization.md)
    ("the transport note"). Proves the weakest renormalization hypothesis that suffices
    (Theorem 1) and the local transport of token edges by $\varepsilon$: everywhere for the
    $w_3$-type tokens, on an exact two-circle domain for the $w_1,w_2$-type. Computed: a token
    edge whose images split. *Referee:* correct after minor fixes (Theorem 3 holds for every
    $\delta\ge0$); the gap is (K) in essentially the same form as before; a new idea is needed.
    ([report](proofs/referee-report-sharp-bound-n5-graph-renormalization.md))
11. [`sharp-bound-n5-atlas.md`](proofs/sharp-bound-n5-atlas.md). Proves the algebra of the
    $\pm\varepsilon$ charts $z\mapsto\pm\varepsilon z+t$, that no chart is a local conjugacy (the
    lune lemma, Proposition 7), and an atlas recursion (Theorem 8) that gives (B) from three local
    and three global hypotheses. Its own assessment: the global, reverse-type hypotheses (coverage
    and gluing) are not reduced, so the atlas does not reduce (K). *Referee:* correct after minor
    fixes; one computed claim corrected (transitions are free for a third of the states); the
    conclusion that the atlas does not reduce (K) is an assessment supported by evidence, not a
    proof. ([report](proofs/referee-report-sharp-bound-n5-atlas.md))
12. [`sharp-bound-n5-rim-graph.md`](proofs/sharp-bound-n5-rim-graph.md) ("the rim note").
    Renormalizes the radius instead of the plane: the parent-radius orbits (pieces) of a child
    orbit, joined by letters acting only in the rim. Proves the rim recursion
    $M(r')+c\le(R+1)(M(r)+c)$ (and $D(r')+1\le(R+1)(D(r)+1)$), so finite rim-graph diameters
    along the level radii give (B) without (T); proves that parent orbits are glued only along the
    two arcs of the lens boundary, by one partial translation by $v=2(\zeta^{-1}-1)\in\Lambda_T$,
    plus junctions at the cusps. Computed: rim-graph diameter $12,14,14,14$ on the orbit of $0$ at
    levels 1–4, at most 29 on 1 573 random children at 30 radii. Its assessment: a uniform bound is
    (K) in a new, localized form. *Referee:* not refereed.

**Dependencies.** Part I (1) starts from `critical-radius-n5.md` and `sharp-lower-bound-n5.md`.
The critical-orbits note (2) and line 4 (3) build on Part I; Part II (4) continues Part I and uses
(2) and (3). The period-two note (5) tests Conjecture 5.1 of `sharp-lower-bound-limit-system.md`.
The critical-renormalization note (6) proves K4 of (2) and feeds Proposition 4.5 of (5). The
chaining note (7) continues line 4. The (T) note (8) proves part (T) of the chaining note's
Conjecture B$^\sharp$. The component-graph note (9) uses (7) and (8); the transport note (10) uses
(8) and (9); the atlas note (11) uses (8), (9) and (10); the rim note (12) uses the atlas referee's §4, and (8) and (9) only for its component-graph form. Notes 9–11 also use the certified
finiteness at $\delta=1/55$ ([`certificates.md`](certificates.md)) as base case.

## The present reduction

- **(T), proved** ([(T) note](proofs/sharp-bound-n5-token-components.md), Theorem 4). Every token
  component of every point of the plane has internal diameter less than $72.07/\delta+41.82$ for
  $0<\delta\le2/5$.
- **Reduction, proved** (same note, Corollary 5). (T) and (K) imply (B). At each fixed $r<r_c$,
  $GG_5(r)$ is finite if and only if $D(r)<\infty$. A uniform bound $D(r)\le K_0$ also gives
  Conjecture A, $M(r)\le(K_0+1)(72.07/\delta+41.82)+1.903K_0$.
- **(K), open.** It is the single remaining statement on this route. Its weakest sufficient form
  is stated in [`proofs/sharp-bound-n5-component-graph.md`](proofs/sharp-bound-n5-component-graph.md),
  Proposition 1:

  > **(K$'$), per radius.** For every non-norm radius $r$ in a set of radii accumulating at $r_c$
  > (for instance the level radii $r_k$) there is $K_0(r)<\infty$ with this property: every
  > lattice orbit of $GG_5(r)$ has a state from which every state is reached by a word with at
  > most $K_0(r)$ connectors.

  The bound may depend on $r$ in any way (Proposition 1(3)); $D(r)=O(\log(1/\delta))$, for
  instance, would suffice. Proposition 1(3) gives finiteness at each such non-norm $r$, and group
  monotonicity (`finite_GG_of_le`) carries it to every smaller radius. A dust-tolerant variant (K$_s$), in which connectors may be many as long
  as they pass only through components with at most $s_0$ states, also suffices (Proposition 1(2)).
- **What the per-radius form is worth.** Given (T), (K$'$) at a radius $r$ is *equivalent* to
  finiteness of $GG_5(r)$ (a finite group has at most $5|GG_5(r)|$ states per lifted orbit). So it
  is a reformulation of (B) in terms of connector letters, not an easier problem. Likewise every
  renormalization recursion $D(\varepsilon\delta)\le F_\delta(D(\delta))$ with constants depending
  on $\delta$ is equivalent to (B)
  ([transport note](proofs/sharp-bound-n5-graph-renormalization.md), Theorem 1). Statements with
  content are those with uniform constants: $D(r)\le K_0$ for small $\delta$, or
  $D(\varepsilon\delta)\le D(\delta)+C$.
- **The rim route.** The rim note (12) gives a second sufficient condition, independent of (T):
  finite rim-graph diameters between consecutive level radii. Per step it is again equivalent to
  (B); its uniform form (Conjecture 7 there, at most 29 in the data) is open and is (K) in a
  localized form.
- **Evidence for (K), computed.** Component-graph diameter 6 to 9 wherever computed exactly; at
  most 9 on 878 random orbits at six radii from $\delta=1/30$ to $\varepsilon^3/10$, with no growth
  as $\delta$ decreases. Conjectured: diameter at most 9 for $\delta\le1/30$ (Conjecture 5.2 of the
  component-graph note).
- **Why the fence does not give (K).** A connector changes the rotation index, so the next token
  component lives in a frame rotated in internal space, and fence columns of different components
  are unrelated ((T) note, §2.4).

## Refuted conjectures and closed formulations

Do not retry these in the form stated.

1. **The forcing argument** (an infinite orbit below $r_c$ must create a structure that exists only
   at $r\ge r_c$): dead as stated. The limit of the systems below $r_c$ is itself infinite, and
   arithmetic excludes only exact boundary contact, not accumulation (critical-orbits note §6).
2. **Exact invariants, congruence invariants, symmetries:** every one present at $r_c$ is
   compatible with an infinite group, so none proves (B) (line 4, Proposition 3). No invariant
   region can be a product $X\times U$ or independent of $r$ (Part I, Proposition 3, Corollary 7).
3. **Uniform K3** (no orbit below $r_c$ meets a chord-parallel line at offset in $(0,c_1\delta)$
   often): false, as a theorem (critical-renormalization note, Theorem 3). The corrected K3 depends
   on the internal coordinate and follows from Conjecture A.
4. **Period two in the unrestricted form** (first-return sets at the tight points equal at levels
   $k$ and $k+2$): refuted exactly (293 of 811 sample points differ at $k=2$, including $E$). The
   first-return/lune-criterion formulation is closed on the referee's recommendation: its
   induction needs a base at level 9, about $10^{12}$ points per excursion. The hypothesis of
   Proposition 4.4 (exact period two of orbit partitions) is refuted at $k_0=1,2$. Exact
   $\varphi^{-3}$ matching was refuted earlier (`sharp-lower-bound-limit-system.md`).
5. **Renormalization inclusion RI for every defect:** false at $\delta=1/2$ and $\delta=1$;
   conjectured only for small $\delta$. **The reverse inclusion** fails at every defect tested, so
   the descent argument "a depth-$\delta$ orbit sees only $\log(1/\delta)/\log\varphi^3$ scales" is
   dead in that form (critical-renormalization note §6).
6. **Conjecture B$^\ast$ as "a sum of arbitrary chord runs":** equivalent to Conjecture A, so not a
   reduction (line 4 referee). In the literal form "boundedly many single-line runs for every word
   map" it is not supported: the number of runs needed grows (6, 9, 11, 12 over levels 0–3).
   Replaced by B$^\sharp$.
7. **The breakpoint-window return map** as the object for chaining: the wrong object, because
   connectors between large token components occur all over the disks, not in $O(\delta)$ windows
   (chaining note, Computation 3).
8. **Conjecture 5.1 (R) of the component-graph note** (parent large components carried by the
   plurality map, $N_0=40$, $b=4$): false as stated; child orbits of 155 to 1 757 states have only
   parents without large components. Taking all components instead breaks non-expansion. A
   repaired two-part form is Conjecture 7.1 of the transport note.
9. **"Token edges with both images present map into one child component":** false (transport
   note §6.2). **Every child state is an image** (pointwise reverse inclusion): false by a factor of
   about 13 in size.
10. **The zoom about $E$ as a global transport of the component graph:** fails (edges split and
    stretch); the right global unit is $\varepsilon$ about $0$ (component-graph note §5).
11. **The atlas of $\pm\varepsilon$ charts as a reduction of (K) to local statements:** dead in the
    author's assessment, because no chart is a local conjugacy and chart validity is not determined
    by position (atlas note §6). Its referee agrees; this is an assessment supported by evidence,
    not a proof.

## Candidate new ideas

Recorded by the authors and referees; none is tested beyond what is said. Each also appears in
[`ideas.md`](ideas.md).

1. **A wall or monotone quantity for connectors**, doing for sheet changes what the fence does for
   token indices ((T) note §2.4; transport referee, §4). It would attack (K) directly. No candidate
   is known.
2. **Renormalize the cut set instead of orbit graphs** (transport referee, §4): show that
   $K(\varepsilon\delta)$ is $\varepsilon K(\delta)$ plus finitely many explicitly described arc
   families. The proposed first test is to compute the cut sets at $1/55$ and $\varepsilon/55$ and
   compare.
3. **Gluing by completeness near $0$** (atlas note §6): every lattice point of the right class in a
   window near $0$ lies in one of boundedly many large token components, as the model set does on
   the chord line.
4. **Renormalize the radius instead of the plane**: worked out in the rim note (12). A uniform bound
   on rim-graph diameters gives (B); it is supported by the data (at most 29) and open. Its
   follow-ups (exact gluing windows, a rim model set, a rim renormalization) are in
   [`ideas.md`](ideas.md).
5. **Box types** ((T) note §2.4 and its referee): a finite graph of fence boxes joined by
   connectors, invariant under $\delta\mapsto\varepsilon^2\delta$; it must carry the physical
   position and the rotation index, not only the index box.
6. **Monotone orbit classes at the tight points** (period-two referee, §5): prove (M$_5$), monotone
   coarsening of the tight-core orbit relation with period two, which holds on all data, together
   with bounded eventual classes (L$_5$). This is the form that served as a reduction for $n=12$.
7. **A one-dimensional cascade** (critical-orbits note §6.3): a renormalization of the offset of
   chord-parallel lines with a bound on runs per offset scale.
