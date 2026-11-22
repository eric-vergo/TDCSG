# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: the token-component graph, one hub per sheet, and its transport by $\varepsilon$

Authors: Eric Vergo, Claude

**Review.** Not refereed. It continues [`sharp-bound-n5-chaining.md`](sharp-bound-n5-chaining.md) (refereed; "the chaining note") and its referee report, and uses [`sharp-bound-n5-token-components.md`](sharp-bound-n5-token-components.md) (not refereed; "the (T) note"), which proves part (T) of Conjecture B$^\sharp$. From the (T) note it uses Theorem 4 (internal diameter of every token component $<72.07/\delta+41.82$ for $\delta\le\tfrac25$) and Corollary 5(2) (at a fixed radius, $GG_5(r)$ is finite iff the component graphs of its orbits have bounded diameter).

**What is established and what is not.** Let $r_c=\sqrt{3+\varphi}$, $\delta=r_c^2-r^2$, $\varepsilon=\varphi^{-3}$.

- **Not established: (B).** Finiteness of $GG_5(r)$ for every $r<r_c$ is **not** proved. Neither is (K) or (K$'$), in any form uniform in $\delta$ or even at a single small $\delta$.
- **Proved.**
  1. *Formulation* (Proposition 1). (K$'$) (from one state of each orbit, every state within $K_0$ connectors) suffices, and so does a dust-tolerant form (K$_s$) in which connectors may number $O(1/\delta)$ as long as only boundedly many token segments lie in components with more than $s_0$ states. With (T) each gives $M(r)<\infty$. A component with $n$ states has internal diameter at most $9.960\,(n-1)$, so a detour through small components costs a bounded amount per connector: dust cannot carry growth unless it is visited unboundedly often.
  2. *Uniformity in $\delta$ is not needed for (B)* (Proposition 1(3)). For (B) it suffices that each fixed $r$ has a finite bound, so a bound on the component-graph diameter that grows like $\log(1/\delta)$ is enough.
  3. *Long passages reach the chord tube* (Lemma 2). A chord passage along a line parallel to $\mathbb R\bar E$ at offset $|h|\le0.15$ with $L+1\ge3$ points contains a point at distance less than $\varphi^2/(2(L+1))$ from $\mathbb RE$. So a component containing such a passage of length $\lambda/\delta$ meets the tube $|d|\le(\varphi^2/2\lambda)\,\delta$.
  4. *Renormalization implies (B)* (Theorem 3). Suppose (R) holds: there are $N_0$ and $b$ such that for every $\delta<\delta_\ast/\varepsilon$, every orbit at $\varepsilon\delta$ with more than $N_0$ states has a parent orbit at $\delta$ and a map $\kappa$ from token components of the parent to those of the child that (R1) does not increase component-graph distances and (R2) has every child component within $b$ connectors of its image. Then (B) holds for every $r<r_c$. Here $\delta_\ast=1/55$ (certified finiteness, modulo the certificate computation). (R1) is the forward, inclusion-type direction. The only reverse-type requirement is (R2), and it asks for coverage up to bounded graph distance, not pointwise.
- **Computed (exact orbits; method in §6).**
  1. *Exact diameters* of 18 named orbits (Table 4.1), new among them: level 3 of the orbit of $0$ (8), rows 7 and 8 of the chaining note ($\varphi^{-3}/55$: 9; $\varphi^{-6}/55$, $2\cdot10^7$ states: 9), row 10 ($\varphi^{-3}/30$: 8), and orbits of $E$ and in the chord-free class of $-\zeta^2$ at levels 1–3 (7, 7, $\ge7$; 7, 7, 8). Over **878** distinct random orbits at six radii from $\delta=1/30$ to $\delta=\varepsilon^3/10$ (Table 4.3), the diameter is at most **9** wherever it is exact (all but 5 orbits at $\varepsilon^3/10$, where it is $\ge7$). It does not grow as $\delta$ decreases, and 9 occurs only at the radii of the $1/55$ family.
  2. *One hub per sheet* (Computation 4.2). Token moves preserve the lifted rotation index $j\in\mathbb Z/5$ and connectors change it by $\pm1$. In every orbit examined from level 1 on, the five largest components (the *hubs*) lie one in each sheet $j=0,\dots,4$, reach essentially the whole internal range of the orbit, and cover the whole physical region. A connector changes $j$ by $\pm1$, so hub $j$ can only be adjacent to hubs $j\pm1$; on all nine orbits checked, all five of these adjacencies occur, so the hubs form a 5-cycle. Every other large component lies within 1 connector of a hub (2 on the $1/55$ witness), and on every named orbit every component lies within 3 connectors of a large component (all components 3 away are single points).
  3. *Distance to the chord tube* (Computation 4.4). From every state, the least number of connectors needed to reach the tube $|d|\le\delta$ about $\mathbb RE$ or $\mathbb R\bar E$ is at most 3 on every named orbit and at most 4 on every random orbit. The tube meets 5 to 11 large components, pairwise at most 4 connectors apart.
  4. *The type graph is invariant* (Computation 4.5). The graph of large components (labelled by rescaled extent, rescaled centre, sheet), with edge weights equal to the least number of connectors through small components, is **identical** at levels 1, 2, 3 of the orbit of $0$ on its 11 main components. What changes from level to level is small satellites merging into the hubs, and new marginal satellites (rescaled extent $\le1.6$) appearing next to existing ones.
  5. *Transport by $\varepsilon$* (Computation 4.6), on 15 named parent–child pairs (units $\varepsilon$, $-\varepsilon$, $\varepsilon^2$) and 102 random ones ($\varepsilon$). Every token edge whose two ends have images in the child orbit maps into one child component, with no exception. Every connector edge between large components with both images present maps to two components at distance exactly 1 (or, in one pair, 0). The plurality map $\kappa$ never increases a pairwise distance (0 violations). New large components are born within distance 2 of the image, and every child component lies within 4 of an image. (R1) and (R2) therefore hold on all 117 tested pairs, with $b\le4$. The zoom $\Psi(z)=E-\varepsilon(z-E)$ of the critical-renormalization note does **not** have these properties globally: token edges split ($4\,470$ cases) and connector edges stretch to distance 3 ($1\,356$ cases).
  6. *Where transport fails* (Computation 4.7). A fixed $68.0\%$ of each orbit's states have $\varepsilon y$ in the child orbit ($77.5\%$ for $\varepsilon^2$). Failure is decided by the physical position of $y$ up to a boundary layer: at cell size $0.005$, 52 of $400\,519$ states lie in mixed cells. The success region contains $|y|<1.0$, and its radial profile is the same at two levels. The failures are spread over all component sizes, so they are **not** confined to dust; the graph statements hold anyway.
  7. *The two-dimensional form of the one-line return reversal* (Computation 4.8). The $\varepsilon$-image of each forward token step is realized by a fixed backward word of 3 tokens (for $w_1,w_2$) or 5 tokens (for $w_3$), the two-dimensional shadow of $R_{\varepsilon\delta}=R_\delta^{-1}$. For $w_3$ the word acts at $\varepsilon X$ wherever $w_3$ acts at $X$, on every state tested; for $w_1,w_2$ only on $54\%$.
- **Conjectured.** (R) (Conjecture 5.1), and the uniform form (K$_{\rm u}$): every orbit at every $\delta\le1/30$ has component-graph diameter at most 9 and a hub with eccentricity at most 6 (Conjecture 5.2).

**The remaining gap.** Statement (R) of Theorem 3, or directly a bound $D(r)<\infty$ at each $r$. In the data (R) holds with $N_0=40$ and $b=4$, but nothing here proves it. A proof of (R1) is a statement about transporting the token and connector relations by $\varepsilon$ on the physical success region. A proof of (R2) needs to control the components born at each step. Both are statements about the dynamics at $\varepsilon\delta$ near $0$ against the dynamics at $\delta$ on the whole disk union: a renormalization of the induced map near $0$, which is not attempted here.

Labels: **proved** (argument written here; cited results with their labels), **computed** (exact arithmetic in $\mathbb Z[\zeta]$ for every membership, token, letter and graph decision; quantities printed as decimals, such as rescaled extents, physical positions and the "large" threshold, are double-precision evaluations of exact points and are used only to label and select), **conjecture**.

---

## 1. Setting

As in the chaining note §1 and the (T) note §1. Lattice orbits are lifted: a state is $(y,j)$ with $y\in\Lambda$ an orbit point and $j\in\mathbb Z/5$ the rotation index of a word from the seed; $V(y,j)=\zeta^{-2j}\sigma y$. For two states the word map between them has internal translation of modulus $|V_2-V_1|$, and $M(r)$ is the supremum of $\operatorname{diam}V$ over orbits (chaining note §6, line 4 Computation 9).

- **Sheets.** Every token has rotation part $0$, so token moves preserve $j$; a connector letter changes $j$ by $\pm1$. The *sheet* $S_j$ of an orbit is its set of states with index $j$. Every token component lies in one sheet.
- **Component graph** $\mathcal C(O)$ of an orbit $O$: token components as vertices, an edge when a connector maps a state of one into the other. $d_O$ is its graph distance, $\operatorname{diam}(O)$ its diameter, $e_O(K)$ the eccentricity of $K$. $D(r)=\sup_O\operatorname{diam}(O)$.
- **Large, small, dust.** A component is *large* if $\delta\cdot\mathrm{ext}>1$, where $\mathrm{ext}$ is the diagonal of the bounding box of its $V$-values (the chaining note's convention). Otherwise it is *small*. *Dust* means components with one or two states. The *hubs* of an orbit are its five components with the most states, and *the hub* is the largest of them; $e$(hub) is its eccentricity.
- **Tube.** $\mathcal T_c$ is the set of states whose point lies within physical distance $c\delta$ of $\mathbb RE$ or of $\mathbb R\bar E$. The test is exact: by Theorem 10 of `sharp-bound-n5-orbit-of-zero.md` the offset from $\mathbb RE$ is $d=\tfrac\varphi2m$ with $m\in\mathbb Z[\varphi]$, from $y\bar E$; for $\mathbb R\bar E$, from $yE$.
- **Transport.** For a unit $u$ and a centre $c$, $\Phi(y)=c+u(y-c)$. The main case is $u=\varepsilon$, $c=0$. For an orbit $O$ at $\delta$ (the *parent*) the *child* is the orbit at $\varepsilon\delta$ of $\Phi(\text{seed})$. $\kappa(K)$ is the child component that contains the most images $\Phi(y)$, $y\in K$ (the *plurality map*).

## 2. Statements

### 2.1 Formulation

**Proposition 1 (what suffices).** Let $r<r_c$, and suppose every token component of $\mathcal T(r)$ has internal diameter at most $C_T(\delta)<\infty$ (true for $\delta\le\tfrac25$ with $C_T=72.07/\delta+41.82$ by the (T) note, Theorem 4).
1. (K$'$) If every lattice orbit has a state from which every state is reached by a path with at most $K_0$ connectors, then $M(r)\le2\bigl((K_0+1)C_T+1.903K_0\bigr)$.
2. (K$_s$) Fix $s_0\ge1$. If every lattice orbit has a state from which every state is reached by a path with at most $K_1$ maximal token segments in components with more than $s_0$ states and at most $K_2$ connectors, then $M(r)\le2\bigl(K_1C_T+K_2(1.903+9.960(s_0-1))+9.960(s_0-1)\bigr)$.
3. In either case $GG_5(r)$ is finite if $r$ is not a norm radius, and if the hypotheses hold at every $r$ of an interval $(r_1,r_c)$, then $GG_5(r)$ is finite for every $r<r_c$. The constants may depend on $\delta$ in any way. In particular $D(r)=O(\log(1/\delta))$ for $\delta\to0$ would give (B), though not Conjecture A.

**[proved]** Item 2 with $K_2=O(1/\delta)$ and $K_1=O(1)$ still gives $M(r)=O(1/\delta)$: connectors may be many if they only lead through small components.

**Lemma 1 (small components).** A token component with $n$ states has internal diameter at most $(n-1)\,2\varphi^2|\sigma E|=9.960\,(n-1)$. **[proved]**

So a path that leaves a large component, crosses $m$ components of at most $s_0$ states and enters another adds at most $m\,(1.903+9.960(s_0-1))+1.903$ to the internal translation. This settles the question whether dust can carry growth: a dust component adjacent to a large one adds a bounded displacement per visit. Whether dust is visited boundedly often is part of (K); in the data it is (Computation 4.2(4): depth at most 3).

### 2.2 Long passages and the tube

**Lemma 2 (long $\bar E$-passages meet the $\mathbb RE$-tube).** Let $\ell$ be a line parallel to $\mathbb R\bar E$ at signed offset $h$ with $|h|\le0.15$. Let $X_k=s_k\bar E+h\bar N$, $\bar N=\overline{iE/|E|}$, $k=0,\dots,L$, be a chord passage of class $\iota$ or $\iota\nu$ on $\ell$, meaning that $s_k=T^k(s_0)\in[-1,1)$ (the images under $z\mapsto\bar z$ of the passages of `sharp-bound-n5-orbit-of-zero.md` §1). If $L+1\ge3$, some $X_k$ satisfies
$$\operatorname{dist}(X_k,\mathbb RE)<\frac{\varphi^2}{2(L+1)}=\frac{1.30902}{L+1}.$$
The same holds with $E$ and $\bar E$ exchanged. **[proved]**

By Theorem 1(2) of the chaining note (for lines parallel to $\mathbb R\bar E$, its item 4), passages with more than 8 points exist only at $|h|<0.15$, so the hypothesis on $h$ is no restriction for long passages. A component that contains a passage of length at least $\lambda/\delta$ therefore meets $\mathcal T_c$ with $c=\varphi^2/(2\lambda)$. The lemma does not say that every orbit has such passages: lower bounds on passage lengths (Theorem 11(3) of the orbit-of-zero note) need small internal coordinates.

### 2.3 Renormalization of the component graph implies (B)

**Hypothesis (R) at $\delta$, with constants $N_0,b$.** For every lattice orbit $O'$ at defect $\varepsilon\delta$ with more than $N_0$ states there are a lattice orbit $O$ at defect $\delta$, a set $\mathcal D$ of token components of $O$ and a map $\kappa\colon\mathcal D\to\mathcal C(O')$ such that
- (R1) $d_{O'}(\kappa K_1,\kappa K_2)\le d_O(K_1,K_2)$ for all $K_1,K_2\in\mathcal D$;
- (R2) every component of $O'$ is within $d_{O'}$-distance $b$ of $\kappa(\mathcal D)$.

**Theorem 3.** Let $\delta_\ast>0$ be a defect at which $GG_5$ is finite. Suppose (R) holds with fixed $N_0,b$ at every $\delta\in(0,\delta_\ast/\varepsilon)$. Then for every $\delta\in(0,\delta_\ast)$, writing $\delta=\varepsilon^k\delta'$ with $\delta'\in[\delta_\ast,\delta_\ast/\varepsilon)$,
$$D(r)\le\max\bigl(N_0,\ 5\,|GG_5(r_\ast)|+2bk\bigr),\qquad r_\ast^2=r_c^2-\delta_\ast,$$
and $GG_5(r)$ is finite for every $r<r_c$. With $\delta_\ast=1/55$ the hypothesis on $\delta_\ast$ is the certified finiteness of [`../certificates.md`](../certificates.md) (modulo that computation). **[proved, given (R) and the (T) note's Theorem 4]**

(R1) is a forward statement, of the same direction as Conjecture RI of `sharp-bound-n5-critical-renormalization.md`: what is related at $\delta$ stays related at $\varepsilon\delta$. For orbit relations that direction gives lower bounds. For graph *distances* it gives upper bounds, because a non-expanding map bounds the distances among images from above. The reverse-type input is only (R2): every child component lies near the image. The pointwise reverse inclusion (every child state an image) is false by a factor of about 13 in size, and it is not needed.

### 2.4 Computations

Stated in §4: Table 4.1 (named orbits), Computation 4.2 (hubs and sheets), Table 4.3 (random orbits), Computation 4.4 (tube), Computation 4.5 (type graph), Computation 4.6 (transport), Computation 4.7 (failure region), Computation 4.8 (transport words).

### 2.5 Conjectures

**Conjecture 5.1 (R).** Hypothesis (R) holds at every $\delta\in(0,1/(55\varepsilon))$ with $u=\varepsilon$, $c=0$, $N_0=40$, $b=4$, $\mathcal D$ the large components of the parent orbit and $\kappa$ the plurality map. **[conjecture]** Evidence: Computation 4.6 (117 pairs, no violation of (R1), (R2) with $b\le4$) and Computation 4.6(5) (every random orbit with more than 40 states, of 100 tested, has a point within $0.236$ of $0$, hence a parent candidate).

**Conjecture 5.2 (K$_{\rm u}$).** For $0<\delta\le1/30$, every lattice orbit has component-graph diameter at most 9, and its hub has eccentricity at most 6. **[conjecture]** Evidence: Tables 4.1 and 4.3. With (T) and Proposition 1(1) ($K_0=6$) it gives $M(r)\le2(7\cdot88.8/\delta+6\cdot1.903)\le1\,266/\delta$ for $\delta\le1$, i.e. Conjecture A with constant about 1 266 (the computed $\delta M$ is at most $25$).

---

## 3. Proofs

### 3.1 Lemma 1

The twelve token translations are $\pm\tau_iE$ and $\pm\tau_i\bar E$ with $\tau_i\in\{2\varphi^{-1},-2\varphi^{-2}\}$. Their conjugates have modulus $|\sigma\tau_i|\,|\sigma E|\le2\varphi^2|\sigma E|=9.9596$, because $\sigma(2\varphi^{-1})=-2\varphi$, $\sigma(-2\varphi^{-2})=-2\varphi^2$ and $|\sigma\bar E|=|\sigma E|$. Two states of one component lie in one sheet, so the word map between them is a translation $t$, determined by the two states. Along any path in a spanning tree of the component, which has at most $n-1$ edges, $|\sigma t|$ is at most the sum of the edge contributions. $\square$

### 3.2 Proposition 1

The word map between two states $s_1,s_2$ of an orbit has internal translation of modulus $|V(s_2)-V(s_1)|$, and $M(r)$ is the supremum of these over all lattice orbits. At a non-norm radius this is the quantity of Lemma 1 of `sharp-bound-n5-conjugate.md` (refereed), which by group monotonicity is all that (B) needs.

1. Let $b$ be the base state. A path from $b$ with at most $K_0$ connectors splits into at most $K_0+1$ token paths, each inside one component, and the connectors. Composition of affine maps makes $|\sigma t|$ subadditive. A token path contributes at most $C_T$ and a connector $|1-\zeta^{\mp2}|=1.90211$ (chaining note, proof of Proposition 6). So $|V(s)-V(b)|\le(K_0+1)C_T+1.903K_0$ for every $s$. The triangle inequality through $b$ gives the bound on $\operatorname{diam}V$.
2. The same, with each segment in a component of at most $s_0$ states bounded by Lemma 1. Such segments number at most $K_2+1$, because consecutive segments are separated by connectors.
3. At a non-norm radius a bound on the lattice orbits bounds all word maps, and finiteness follows (Part I Lemma 1 with `critical-radius-n5.md` Lemma 4.1). Non-norm radii are dense, so on an interval group monotonicity (`boundary-contact.md` Theorem 3.4) gives every radius. Nothing in 1–2 used a relation between the constants and $\delta$. If $D(r)\le c\log(1/\delta)$, item 1 applies with $K_0=D(r)$ at each $r$. $\square$

(Item 3 is the content of Corollary 5(2) of the (T) note, stated there with the diameter. It is repeated here because it changes what a renormalization argument must deliver: additive growth per scale is enough for (B).)

### 3.3 Lemma 2

With $|E|=\sqrt{3-\varphi}$ and $\arg E=18^\circ$, the signed distance of $X$ from $\mathbb RE$ is $\operatorname{Im}(X\bar E)/|E|$. For $X=s\bar E+h\bar N$, $\bar N=-i\bar E/|E|$, this is $-(s\,|E|\sin36^\circ+h\cos36^\circ)$, with $|E|\sin36^\circ=(5-\sqrt5)/4=0.690983$ and $\cos36^\circ=\varphi/2$. It vanishes at $s^\ast=-1.170820\,h$, and $|s^\ast|\le0.1757$ for $|h|\le0.15$.

In the coordinate $x=(s+1)/2\in\mathbb R/\mathbb Z$ the points $s_0,\dots,s_L$ are $L+1$ consecutive points of the rotation by $\varphi^{-1}$. Let $j$ be the largest index with $F_j\le L+1$, so $j\ge4$. By the three-distance theorem (chaining note, proof of Theorem 1), $F_j$ consecutive points cut the circle into arcs of length at most $\varphi^{-(j-2)}$, which is $2\varphi^{-(j-2)}$ in $s$. So some $s_k$ is within $\varphi^{-(j-2)}\le\varphi^{-2}=0.382$ of $s^\ast$ in the circle metric. Since $|s^\ast|+0.382<1$, the arc of that radius about $s^\ast$ lies inside $(-1,1)$, so the circle distance is the real distance: $|s_k-s^\ast|\le\varphi^{-(j-2)}$.

By maximality, $L+1\le F_{j+1}-1<\varphi^{j+1}/\sqrt5$ (Binet). So $\varphi^{-(j-2)}=\varphi^3\varphi^{-(j+1)}<\varphi^3/(\sqrt5(L+1))$, and
$$\operatorname{dist}(X_k,\mathbb RE)=0.690983\,|s_k-s^\ast|<\frac{0.690983\,\varphi^3}{\sqrt5\,(L+1)}=\frac{\varphi^2}{2(L+1)}.$$
The exchanged statement follows by complex conjugation, which fixes the system up to $a\leftrightarrow a^{-1}$, $b\leftrightarrow b^{-1}$ (line 4, Proposition 3). $\square$

### 3.4 Theorem 3

Write $D(\delta)$ for $D(r)$ at defect $\delta$.

*Base.* Let $\delta'\in[\delta_\ast,\delta_\ast/\varepsilon)$, so $r'\le r_\ast$. By orbit monotonicity (`boundary-contact.md` Theorem 3.1, refereed and Lean-checked), $O_{r'}(y)\subseteq O_{r_\ast}(y)$, and $|O_{r_\ast}(y)|\le|GG_5(r_\ast)|$. A lifted orbit has at most 5 states per point. A graph has diameter less than its number of vertices, so $D(\delta')\le5|GG_5(r_\ast)|$.

*Step.* Let $O'$ be an orbit at $\varepsilon\delta$ with more than $N_0$ states, and $O,\kappa,\mathcal D$ as in (R). For components $X',Y'$ of $O'$ choose $K_1,K_2\in\mathcal D$ with $d(X',\kappa K_1)\le b$ and $d(Y',\kappa K_2)\le b$ (R2). Then $d(X',Y')\le2b+d(\kappa K_1,\kappa K_2)\le2b+d_O(K_1,K_2)\le2b+D(\delta)$ (R1). Orbits with at most $N_0$ states have diameter less than $N_0$. So $D(\varepsilon\delta)\le\max(N_0,D(\delta)+2b)$.

*Induction* over $k$ gives the bound on $D(\varepsilon^k\delta')$. Finiteness of $D(r)$ at each $r$ with $\delta<\delta_\ast$ gives finiteness of $GG_5(r)$ by Proposition 1(1), (3) with $K_0=D(r)$ and the (T) note's Theorem 4 (this is Corollary 5(2) of the (T) note). Radii with $\delta\ge\delta_\ast$ are covered by group monotonicity (`boundary-contact.md` Theorem 3.4). $\square$

---

## 4. Computations

All orbits are exact lifted breadth-first searches. Sizes agree with the chaining note and its referee report wherever both exist (for example $111\,107$; $1\,448\,901$; $1\,467\,539$; $20\,057\,921$; $5\,673\,561$ states). Diameters are exact by iFUB, the exact eccentricity-bounding diameter algorithm, unless marked $\ge$ (when the BFS budget was reached).

### 4.1 Named orbits

**Table 4.1.** Columns: states; components; large components; exact diameter; $e$(hub); the largest distance of any component from the set of large components ("depth"); "hops", the largest number of large components other than the hub that a path from the hub must enter, minimized over paths; the largest connector distance from any state to $\mathcal T_1$; the number of large components meeting $\mathcal T_1$ and their largest pairwise distance.

| orbit | $\delta$ | states | comps | large | diam | $e$(hub) | depth | hops | tube | tube comps / dist |
|---|---|---|---|---|---|---|---|---|---|---|
| $0$, level 0 | $1/10$ | 1 433 | 447 | 19 | 6 | 3 | 2 | 1 | 2 | 11 / 2 |
| $0$, level 1 | $\varepsilon/10$ | 30 165 | 9 553 | 23 | 6 | 4 | 2 | 1 | 3 | 9 / 2 |
| $0$, level 2 | $\varepsilon^2/10$ | 400 519 | 126 165 | 11 | 7 | 4 | 3 | 1 | 3 | 9 / 2 |
| $0$, level 3 | $\varepsilon^3/10$ | 5 673 561 | 1 787 929 | 15 | **8** | 4 | 3 | 1 | 3 | 9 / 2 |
| $E$, level 1 | $\varepsilon/10$ | 20 424 | 6 405 | 15 | 7 | 4 | 2 | 1 | 3 | 5 / 2 |
| $E$, level 2 | $\varepsilon^2/10$ | 256 247 | 80 394 | 6 | 7 | 4 | 3 | 1 | 3 | 5 / 2 |
| $E$, level 3 | $\varepsilon^3/10$ | 3 444 159 | 1 085 072 | 5 | $\ge7$ | 4 | 3 | 1 | 3 | 5 / 2 |
| $-\zeta^2$, level 1 | $\varepsilon/10$ | 62 095 | 19 468 | 25 | 7 | 4 | 2 | 1 | 3 | 5 / 2 |
| $-\zeta^2$, level 2 | $\varepsilon^2/10$ | 256 931 | 80 740 | 5 | 7 | 4 | 3 | 1 | 3 | 5 / 2 |
| $\varepsilon\cdot(-\zeta^2)$, level 2 | $\varepsilon^2/10$ | 793 108 | 249 267 | 10 | 7 | 4 | 3 | 1 | 3 | 5 / 2 |
| $\varepsilon^2\cdot(-\zeta^2)$, level 3 | $\varepsilon^3/10$ | 11 123 374 | 3 504 877 | 13 | 8 | 5 | 3 | 1 | 3 | 5 / 2 |
| $1/55$ witness | $1/55$ | 111 107 | 34 750 | 15 | 9 | 5 | 3 | 2 | 3 | 11 / 4 |
| row 6 | $\varphi^{-3}/55$ | 1 448 901 | 455 528 | 14 | 9 | 5 | 3 | 2 | 3 | 11 / 4 |
| row 7 | $\varphi^{-3}/55$ | 1 467 539 | 461 690 | 16 | **9** | 5 | 3 | 2 | 3 | — |
| row 8 | $\varphi^{-6}/55$ | 20 057 921 | 6 321 176 | 20 | **9** | 5 | 3 | 2 | 3 | 11 / 4 |
| $1/30$ witness | $1/30$ | 54 210 | 17 021 | 21 | 6 | 4 | 2 | 1 | 2 | 5 / 2 |
| row 10 | $\varphi^{-3}/30$ | 747 936 | 235 591 | 15 | **8** | 5 | 3 | 2 | 3 | 5 / 2 |
| $\varepsilon\cdot(437,-36,293,235)$ | $\varphi^{-3}/30$ | 925 886 | 291 645 | 19 | 8 | 5 | 3 | 2 | 3 | 7 / 2 |

Seeds: rows 6–8 and 10 are those of the chaining note's Computation 4; $E=(0,1,-1,0)$, $-\zeta^2=(0,0,-1,0)$, $\varepsilon\cdot(-\zeta^2)=(0,-2,1,-2)$, $\varepsilon^2\cdot(-\zeta^2)=(0,8,-5,8)$. Bold entries are new exact values; the referee report had $\ge8$, $\ge9$, $\ge9$, $\ge8$. The least eccentricity over large components equals $e$(hub) on every row, so the best base state for (K$'$) can always be taken in the hub.

### 4.2 Hubs and sheets

1. On the orbits checked (the orbit of $0$ at level 2, $E$ at level 2, $-\zeta^2$ at level 1, the $1/55$ witness, the $1/30$ witness and row 10), the five components with the most states lie in the five different sheets. Their sizes agree to within $4\%$ on the orbits of $E$, of $-\zeta^2$, of the $1/30$ witness and of row 10 (for example $76\,857, 76\,857, 76\,743, 76\,743, 76\,736$ on row 10), and to within $10\%$ on the $1/55$ witness and rows 6, 7. On the orbit of $0$ the hub of sheet 0 is smaller: $21\,779$ states against $37\,946$–$42\,106$ at level 2, and rescaled extent $11.97$ against $15.73$. Their physical points fill the bounding box of $D_1\cup D_2$ ($[-2.50,2.50]\times[-2.14,2.14]$ at level 2).
2. The hub reaches the whole internal range of the orbit. The largest $\delta|V-V(\text{seed})|$ over the hub's states is $6.42,\ 6.48,\ 6.49$ against $6.45,\ 6.49,\ 6.49$ over the whole orbit of $0$ at levels 1–3, $13.87$ against $13.87$ on the $1/55$ witness, $13.89$ against $13.89$ on row 6, and $19.27$ against $19.29$ on the $1/30$ witness.
3. On the nine orbits of Table 4.1 with the weight matrix computed (levels 0–3 of the orbit of $0$, the $1/55$ witness, rows 6, 7, 10 and the $1/30$ witness), each of the five largest components is adjacent through a single connector to exactly two of the other four, and at distance 2 from the remaining two: a 5-cycle. Where the hubs lie one per sheet, this is the most that is possible, since a connector changes $j$ by $\pm1$ and hub $j$ can only be adjacent to hubs $j\pm1$.
4. On the same nine orbits every large component other than the five largest lies within 1 connector of one of them through small components (within 2 on the $1/55$ witness). On every orbit of Table 4.1, every component lies within 3 connectors of a large component, and the components at distance 3 are single points. The largest component at distance 2 from the large set has 8 states.

### 4.3 Random orbits

Seeds: a physical point uniform in $D_1\cup D_2$ and an internal point uniform in a disk of radius $R$, rounded to $\Lambda$ (chaining note §6). Two batches per radius, with $R\approx8/\delta$ and $R\approx25/\delta$. Duplicate orbits were removed (same size and same $V$-width). "Large orbits" have at least 1 000 states.

**Table 4.3.**

| $\delta$ | distinct orbits | diameters, all orbits | large orbits | diameters, large orbits | max $e$(hub) | max depth | tube distance |
|---|---|---|---|---|---|---|---|
| $1/30$ | 164 | 0:1, 4:3, 5:3, 6:117, 7:37, 8:3 | 122 | 6:102, 7:20 | 5 | 2 | 2–3 |
| $\varepsilon/10$ | 170 | 0:1, 4:3, 5:1, 6:98, 7:61, 8:6 | 127 | 6:85, 7:42 | 4 | 2 | 2–3 |
| $1/55$ | 201 | 0:1, 4:3, 6:107, 7:80, 8:5, 9:5 | 163 | 6:95, 7:63, 9:5 | 6 | 3 | 2–3 |
| $\varepsilon^2/10$ | 166 | 0:1, 4:3, 6:52, 7:82, 8:28 | 135 | 6:42, 7:70, 8:23 | 5 | 3 | 2–4 |
| $\varphi^{-3}/55$ | 143 | 0:1, 4:3, 6:45, 7:69, 8:22, 9:3 | 118 | 6:39, 7:58, 8:18, 9:3 | 5 | 3 | 2–4 |
| $\varepsilon^3/10$ | 34 | 0:1, 4:3, 6:10, 7:4, 8:11, $\ge7$:5 | 25 | 6:8, 7:3, 8:9, $\ge7$:5 | 5 | 3 | 3–4 |

Total: 878 distinct orbits. The 30 orbits first found with $\ge$ at $\varepsilon^2/10$ and $\varphi^{-3}/55$ were rerun with 50 times the BFS budget, and all became exact (23 with diameter 7, 7 with diameter 8); the table shows the exact values. The 5 orbits marked $\ge7$ at $\varepsilon^3/10$ (about $5\cdot10^6$ states each) were not rerun. No diameter above 9 occurs, and the only 9s are at the $1/55$ radii. The orbits with diameter 8 and fewer than 1 000 states are small orbits with few or no large components, where the depth reaches 4 or 5. "Tube distance" is over orbits that meet $\mathcal T_1$.

### 4.4 The tube

For $c\in\{\tfrac12,1,2,4\}$ and the tubes about $\mathbb RE$, $\mathbb R\bar E$ or both (exact key test), a 0-1 breadth-first search (tokens cost 0, connectors cost 1) from the tube states. On the first nine orbits computed (levels 0–3 of the orbit of $0$, the $1/55$ witness, rows 6, 7, 10 and the $1/30$ witness) the maximum over states is 2–3 for the two-line tube at every $c\in\{\tfrac12,1,2,4\}$, and at most 4 for a single line at $c=\tfrac12$. On the other orbits of Table 4.1 (only $c=1$, two lines) it is 3. On the random orbits of Table 4.3 it is at most 3 at the three larger radii and at most 4 at the three smaller ones. The tube states lie in 5 to 11 large components, pairwise at most 4 apart, and in many single-point components. The mechanism suggested by the data: every component is within 3 of a large component (Computation 4.2(4)), and the large components with long passages meet the tube (Lemma 2). This is not a proof: Lemma 2 needs a long passage in the component, which is not shown for every large component.

### 4.5 The type graph across levels

For each large component: size, rescaled extent $\delta\cdot\mathrm{ext}$, rescaled $V$-centre, sheet. Edge weights: the least number of connectors from one large component to another through small components only. On the orbit of $0$:
- **Hubs:** extent $11.85,\,15.64^{\times2},\,15.61^{\times2}$ (level 1), $11.97,\,15.73^{\times2},\,15.73^{\times2}$ (level 2), $12.00,\,15.76^{\times2},\,15.75^{\times2}$ (level 3), all centred at $V=0$, with the 5-cycle of 4.2(3).
- **Satellites:** a pair of extent $6.37,\,6.48,\,6.50$ at $V=\pm3.86,\ \pm4.01,\ \pm4.02$ (rescaled), at weight 1 from two hubs, 2 from two others, and not reachable through small components from the fifth. A quadruple of extent $2.81,\,2.89,\,2.91$ at $V=(\pm2.9,\pm3.4)$, at weight 1 from the hub of sheet 0 and from one other, 2 from two, and not reachable from the fifth.
- The weight matrix restricted to these 11 components is **the same** at levels 1, 2 and 3, row by row up to relabelling.
- The other large components are marginal: twelve of extent $1.07$–$1.10$ at level 1, none at level 2, and four of extent $1.53$ at level 3. Under $\varepsilon$ the level-1 marginals map into the hubs (Computation 4.6(4)).

Along the $1/55$ sequence (witness, row 6, row 8) $\kappa$ maps all 15, resp. 14, large components onto large components. The births are 2 marginal components (extent $1.1$–$1.2$) at the first step and 8 at the second. Along the $1/30$ sequence the five hubs have extents $32.2$ ($1/30$) and $33.5$ (row 10). At the step $1/30\to\varphi^{-3}/30$, 14 large components are born: twelve of 824 states (extent $2.0$–$2.1$) and two of $9\,377$ states (extent $8.87$). All births lie within 1 connector of an image. (Bounding-box extents depend on the frame of the seed's sheet, up to a factor $\sqrt2$, so extents are compared only within one orbit or between frames that $\varepsilon$ preserves.)

### 4.6 Transport by $\varepsilon$

Pairs (parent at $\delta$, child at $u\delta$ containing $u\cdot$seed). Orbit of $0$: levels $0\to1$, $1\to2$, $2\to3$ ($\varepsilon$) and $0\to2$, $1\to3$ ($\varepsilon^2$). Orbit of $E$: $1\to2$, $2\to3$. Class of $-\zeta^2$: $1\to2$, $2\to3$, $1\to3$. The $1/55$ chain: witness $\to$ row 6 $\to$ row 8. The $1/30$ chain: witness $\to\varepsilon\cdot$witness, row 10 $\to\varepsilon\cdot$row 10 ($9\,896\,640$ states). Random parents with physical position $|y|<0.9$: 36 at $1/55\to\varphi^{-3}/55$, 26 at $\varepsilon/10\to\varepsilon^2/10$, 26 at $1/30\to\varphi^{-3}/30$, 14 at $1/20\to\varphi^{-3}/20$.

1. *Image fraction.* $0.6783$–$0.6797$ of the parent's states have $\varepsilon y$ in the child on every named parent and on every random parent with at least $10^4$ states; $0.7739$–$0.7756$ for $\varepsilon^2$. (Small random parents: between $0.6$ and $1$.)
2. *Token edges.* On every pair for the units $\varepsilon,-\varepsilon,\varepsilon^2$, a token edge of the parent whose two endpoints both have images in the child maps into **one** child component: the counts satisfy "same component" + "one end missing" = "all" exactly (for example $324\,892+40\,256=365\,148$ at $2\to3$).
3. *Connector edges between large components.* With both images present, they map to child components at distance exactly 1 on every $\varepsilon$-type pair but one, where $9\,680$ edges map to distance 0 (a merge). None maps to distance 2 or more. For example $200\,980$ of $200\,980$ at $2\to3$, and $734\,680$ of $734\,680$ on row 6 $\to$ row 8.
4. *The plurality map* $\kappa$ on large components: on every pair, every large component of the parent maps to a large child component. No ordered pair has $d(\kappa K_1,\kappa K_2)>d(K_1,K_2)$ (0 violations in 118 pairs, the $\Psi$ pair included). Merges occur: distance $2\to0$, $3\to1$, $4\to0$. At $1\to2$ on the orbit of $0$, $\kappa$ maps each hub to the hub of the same sheet, and the sheet index is preserved on every transported state.
5. *Births and coverage.* Large child components that are not $\kappa$-images are at distance at most 1 from $\kappa(\mathcal D)$ (at most 2 on one random pair). They number 0–14, mostly marginal; at $1/30\to\varphi^{-3}/30$ they include two components of extent $8.87$. Every child component lies within 3 of a component containing an image (within 4 on three pairs). Of 100 distinct random orbits at $1/55$ and $\varepsilon/10$, every one with more than 40 states has a point within $0.236$ of $0$, and therefore an $\varepsilon$-parent candidate in $|y|<1$. The 8 without such a point have 1 to 40 states.
6. *Other units.* $-\varepsilon$ about $0$ gives the same as $\varepsilon$ (up to the symmetry $z\mapsto-z$). $\Psi(z)=E-\varepsilon(z-E)$ at $1\to2$: image fraction $0.648$; $4\,470$ token edges with both images present split between two child components; $1\,356$ connector edges between large components map to distance 3. $\kappa$ is still non-expanding on that pair. So for the global component graph the unit is $\varepsilon$ about $0$, with period one: the sign $\sigma(\varepsilon)<0$ reverses rescaled internal coordinates ($V\mapsto-V$), which the graph does not see.

### 4.7 Where transport fails

For $1\to2$ and $2\to3$ (orbit of $0$), the fraction of parent states with $\varepsilon y$ in the child, by physical radius $|y|$ in bins of $0.1$, is $1.000$ on $[0,1.0)$, and $1.000$, resp. $0.994$, on $[1.0,1.1)$. It is then $0.84,\ 0.63,\ 0.44,\ 0.30,\ 0.52,\ 0.45,\ 0.36,\ 0.35,\ 0.34,\ 0.51,\ 0.40,\ 0.44,\ 0.47,\ 0.70,\ 0.79,\ 0.88$ on $[1.1,2.7)$, and $1.000$ on $[2.7,3.15]$. The two levels agree to $0.02$ in every bin. Binned in square cells of side $h$, the cells containing both successes and failures hold $164,\ 28,\ 0$ of $30\,165$ states ($h=0.05,0.02,0.01$, level 1) and $3\,368,\ 836,\ 236,\ 52$ of $400\,519$ ($h=0.05,0.02,0.01,0.005$, level 2). So success is a function of the physical position, up to a boundary layer that thins with $h$, on a $\delta$-independent region $G$ containing the disk $|y|<1$. The failures lie in components of every size, $32\%$ of all states, **not** only dust. They do not break (R1) because a token or connector edge with a failing endpoint simply has no image.

### 4.8 Transport words for tokens

For each token edge $X\to g\cdot w_i(X)$ of the parent with both images present, the shortest token path between the images in the child has length 3 ($2\,763$ of $3\,336$ sampled edges at $1\to2$), 5 ($568$), or 11 and more ($5$). The image of a $w_1$-step is the word $(\nu w_3)(\nu w_2)(\nu w_3)=w_3^{-1}w_1^{-1}w_3^{-1}$, with translation $4\varphi^{-2}-2\varphi^{-1}=2\varphi^{-4}=\varepsilon\tau_1$, in all 340 sampled cases. The image of a $w_3$-step is the 5-token word $w_3^{-1}w_2^{-1}w_3^{-1}w_1^{-1}w_3^{-1}$, with translation $16-10\varphi=\varepsilon\tau_3$. The index changes by $n(\varepsilon\tau)=-\varphi^3+\tau=-3$, resp. $-5$, which is the identity $n(\varepsilon\xi)=-\varphi^3n(\xi)+\xi$ of the chaining note's Proposition 2: a forward step becomes a short backward path. Tested on every parent state where the token acts (exact letter tests at the child radius):
- for $w_3$ and its eleven symmetric images the transport word acts at $\varepsilon X$ at **every** state ($1\,035/1\,035$ at $1\to2$, $13\,897/13\,897$ at $2\to3$);
- for $w_1,w_2$ it acts on $54.0\%$; it never acts at a point whose image lies outside the child orbit, and it fails at $381$ (resp. $5\,164$) points whose image is in the child.

---

## 5. Direction of the inclusions, and what is dead

- **(K) as a uniform bound** is supported: diameters $\le9$ on about 900 orbits, stable along all renormalization sequences computed. It is not proved.
- **The window/return-map route** for (K) stays dead (chaining note §5): connectors join large components everywhere.
- **Renormalization of orbit relations** (RI, critical-renormalization note) needs the reverse inclusion, and it fails pointwise. For the component graph the forward direction is the useful one. A non-expanding transport bounds distances above, and the data show non-expansion without exception for $\varepsilon$ about $0$. The reverse-type requirement shrinks to (R2), coverage up to bounded graph distance, which holds with $b\le4$. This is where the upper-bound direction stands: forward non-expansion, observed without exception; bounded coverage, observed. Neither is proved.
- **The zoom $\Psi$ about $E$** (unit $-\varepsilon$, local) does not transport the global component graph: edges stretch. The right global unit is $\varepsilon$ about $0$.
- **Failures of transport** are not confined to dust. They are a $\delta$-independent physical region (about $32\%$ of every orbit), and they are harmless for (R1).

**Assessment.** *Repairable, not closed.* The reduction is now to a single structural statement, (R), which is a renormalization statement about the component graph rather than about points. It holds in all 117 tested $\varepsilon$-type parent–child pairs, and with Theorem 3 it gives (B) without any uniformity in $\delta$. What a proof needs, in order of difficulty:
1. (R1) for token edges: show that for $X$ in the success region $G$ the transport word of §4.8 acts at $\varepsilon X$. For $w_3$ the data say it always acts, so this is a containment of an intersection of disks of radius $\varepsilon r$ in one of radius $r'$. It is a finite computation of the kind of the chaining note's Computation 1.2, plus a lune analysis at the tight points.
2. (R1) for connector edges, and a description of $G$ by finitely many circles.
3. (R2): the components born at $\varepsilon\delta$ near the image. This needs the dynamics at $\varepsilon\delta$ on the whole disk union, not only near $0$. It carries the difficulty of (B).

## 6. Reproduction

Throwaway C programs in the session scratch folder, not committed; exact arithmetic as in line 4 §6 (integer 4-vectors, $\zeta^{\pm1}$ shifts, disk tests as the sign of an element of $\mathbb Z[\varphi]$ with 128-bit integers). Radii as in the chaining note §6; additionally $\varphi^{-3}/20$ is $r^2=(63+18\varphi)/20$ and $1/20$ is $(59+20\varphi)/20$.

- `kg` (one orbit). Lifted BFS; letter table; token table (a token acts when each letter's table entry exists); union-find components; deduplicated component graph; BFS from the seed's and the largest component; eccentricity of every large component; multi-source BFS from the large set (depth); iFUB from the largest component, with a BFS budget; a 0-1 BFS over components (cost 1 for entering a large component) for "hops"; the large-component weight matrix (BFS through small components only); hub data (physical box, sheet histogram); the tube as a 0-1 BFS over states from the exactly tested tube states.
- `kmap` (parent and child). Both orbits; $\Phi(y)=c+u(y-c)$ by exact multiplication; image lookup in the child's hash (any lift); per-large-component image statistics and sheet shift; token-edge and connector-edge transport counts; the plurality map $\kappa$ and the pairwise distance comparison (BFS from each $\kappa K$); births and coverage (multi-source BFS from image components); optional dumps of physical position against success (Computation 4.7), shortest child token paths between images (4.8), and an exact letter-by-letter test of the transport words.
- `gen` (random seeds) as in the chaining note §6, with the stated $R$ and seeds 11–15, 21–26, 31–34, 41–42. Duplicate removal by (size, $V$-width).
- Unit vectors: $\varepsilon=(-3,0,-2,-2)$, $-\varepsilon=(3,0,2,2)$, $\varepsilon^2=(13,0,8,8)$, $E=(0,1,-1,0)$.

Peak memory $3.8$ GB (row 6 $\to$ row 8).
