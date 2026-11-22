# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: an atlas of $\pm\varepsilon$ charts, what it localizes, and the gluing step it cannot reach

Authors: Eric Vergo, Claude

**Review.** Independently refereed: [`referee-report-sharp-bound-n5-atlas.md`](referee-report-sharp-bound-n5-atlas.md). Verdict: Propositions 1–4, Lemma 5 and Proposition 7 correct (Proposition 3 and the reading of Proposition 7 after wording fixes: Proposition 7 is a statement about one parent word and one child word, not about the whole relation); Proposition 6 correct after a wording fix (the kind of a test with margin exactly $0$ and no tangency is not covered; it does not occur in Computation 4.2); Theorem 8 correct after minor fixes (image states are those of points of $G_\chi$; the case $L=1$; Conjecture 9 must hold on $0<\delta<\varphi^3/55$ to give (B) with the base $1/55$, and its spread constant is $s=4$, since (A4) is pairwise). One computed claim was wrong and is corrected: transitions are free (cost $0$) for $10\,009$ of the $30\,165$ parent states; "never $0$" in the original came from sampling only states with two or more image components. The referee reproduced, with an independent exact program, the pointwise census (§4.1), the coherence census (§4.3), all transitions (§4.4), the spread (§4.4; pairwise spread reaches $4$) and the gluing table (§4.6) at levels $0\to1$, $1\to2$, $2\to3$ and on 13 random children. The conclusion that the atlas does not reduce (K) is an assessment supported by Proposition 7 and the data, not a theorem. The note continues [`sharp-bound-n5-graph-renormalization.md`](sharp-bound-n5-graph-renormalization.md) ("the transport note"; refereed, correct after minor fixes: [`referee-report-sharp-bound-n5-graph-renormalization.md`](referee-report-sharp-bound-n5-graph-renormalization.md)), whose §6.4 and §7 proposed the atlas, and [`sharp-bound-n5-component-graph.md`](sharp-bound-n5-component-graph.md) ("the component-graph note"; refereed, with its report). From refereed notes it uses: the (T) note's Theorem 4 and Corollary 5(2) ([`sharp-bound-n5-token-components.md`](sharp-bound-n5-token-components.md)); the definitions of [`sharp-bound-n5-chaining.md`](sharp-bound-n5-chaining.md) §1; the ambient group and its 20 classes, `sharp-bound-n5-invariant.md` Proposition 2, and the symmetries of its Proposition 3; the transport note's Lemma 2 (tangent disks), Theorems 3–4 and Lemma 6 (letter exchange); the component-graph note's §1 conventions (lifted states, sheets, sheet-preserving lift) and the proof pattern of its Theorem 3; orbit and group monotonicity (`boundary-contact.md` Theorems 3.1, 3.4, refereed and Lean-checked); `sharp-lower-bound-n5.md` Theorem 4.1; and, as the base case, the certified finiteness at $\delta=1/55$ of [`../certificates.md`](../certificates.md).

**What is established and what is not.** Let $r_c=\sqrt{3+\varphi}$, $\delta=r_c^2-r^2$, $\varepsilon=\varphi^{-3}$; the *parent* radius has defect $\delta$, the *child* radius $r'$ has defect $\varepsilon\delta$.

- **Not established: (B).** Finiteness of $GG_5(r)$ for every $r<r_c$ is not proved here, and (K) is not reduced to finitely many local statements.
- **Answer to the question of this round.** A finite atlas of $\pm\varepsilon$ charts turns the *forward* half of the renormalization (parent edges become child paths, chart changes cost a bounded amount) into finitely many local statements, and makes the bookkeeping of chart changes finite (Theorem 8). It does **not** localize the *reverse* half. Three hypotheses of the resulting recursion remain global, and two of them are reverse-type: coverage of the child orbit up to bounded connector distance, and gluing of the images of different parent orbits. Proposition 7 proves the word-level form of the reason: no chart carries a parent word domain onto a child word domain, because a child word domain that contains a chart image of a parent word domain always contains it strictly, by lunes of positive area at every boundary arc. That the child relation as a whole is strictly richer than every chart image of the parent relation is the lattice picture of this (§4.7, computed for chart $0$), not a theorem; the extra relations are where the child's own structure enters. My assessment: the chord-token programme needs a new idea for this gluing step (§6).
- **Proved.**
  1. *The charts and their algebra* (Propositions 1–4, Lemma 5). The centred charts $c\pm\varepsilon(z-c)$, $c\in\Lambda$, are exactly the maps $z\mapsto\pm\varepsilon z+t$ with $t\in2\Lambda$. Every chart normalizes the ambient group and carries the token module to itself (generalizing Lemma 6 of the transport note to every chart). A chart maps the $\Gamma$-class with label $(a,b)\in\mathbb F_5\times(\mathbb F_{16}/\langle\zeta\rangle)$ to $(\bar u(a-1)+1+\bar t,\ b)$; so for a given orbit only one coset $t_0+\Lambda_T$ of translations (per sign) can map it into a given class, and charts of different cosets never meet in one child orbit. Minus-charts are plus-charts of the mirror orbit, and within one coset $\chi_{u,t+us}(x)=\chi_{u,t}(x+s)$. A change of chart that stays in one sheet costs $0$, $2$, $4$ or at least $5$ connectors, never $1$ or $3$.
  2. *Per-chart transport is a finite cell problem* (Proposition 6). For every chart $\chi_t$ the transport word $W(k)$ acts at $\chi_t(X)$ iff $\varepsilon X$ lies in the disks $D(c'-t,r')$; the test is a finite computation of the kind of the transport note's Theorems 3–4. Among 13 charts tested (Computation 4.2) only $t=0$ has the full tangency structure; for the others the chart-$0$ words are cut by 3 to 10 circles.
  3. *No chart is a word-by-word local conjugacy* (Proposition 7, the lune lemma).
  4. *The atlas recursion* (Theorem 8). Local hypotheses (A1)–(A3) (edge transport per chart, cover of the parent region, bounded transitions) together with global hypotheses (A4) (bounded spread of a chart image of one parent component), (A5) (every child component within $b$ of a chart image) and (A6) (the images of the parents of one child orbit are glued at bounded distance), all with constants independent of $\delta$, give $D(\varepsilon\delta)\le\max(N_0,\ L\,D(\delta)+C)$ and hence (B). The recursion is multiplicative, $D=O(\delta^{-\log L/\log\varphi^3})$, which suffices for (B) by Corollary 5(2) of the (T) note. The finiteness of the atlas is what bounds the cost of chart changes inside one parent component (the chart nerve argument of §3.6); without it the number of chart patches along a path could be unbounded.
- **Computed** (exact orbit arithmetic in $\mathbb Z[\zeta]$; geometry in 50-digit arithmetic; §4).
  1. *Pointwise coverage is cheap and says nothing.* $1\,318$ of the $8\,142$ charts with $|t|\le3.4$, $|\sigma t|\le40$ map more than $5\%$ of the orbit of $0$ at level 1 into the orbit of $0$ at level 2; all of them lie in the coset predicted by Proposition 3, and all preserve the sheet. Together they cover $93.2\%$ of the child pointwise.
  2. *Structural coverage.* Only the chart $t=0$ is exactly coherent (token edges with both images to one child component, connector edges to adjacent ones). $53$ of $801$ plus-charts are coherent to at least $0.9$. Every parent state is a good state of one of them, so the parent side is covered; but their good images cover only $40\%$ of the child, and almost none of the outer annulus $|y'|\ge2.7$.
  3. *Transitions cost 0, 2 or 4.* Every parent state is a good state of at least 3 good charts. For $10\,009$ of the $30\,165$ parent states all these images lie in one child component (a free transition). For the other $20\,156$ they lie in 2 to 8 components, with largest mutual distance exactly $2$ ($19\,952$) or $4$ ($204$); Lemma 5 forbids 1 and 3.
  4. *Spread (A4).* The chart-$0$ images of a parent component with at least 5 states lie in child components at distance $0$ or exactly $2$ from the plurality component, never more: $89$ of $89$ components split at level $1\to2$, $1\,015$ of $1\,131$ at $2\to3$; plurality share at least $0.80$. Pairwise, as (A4) is stated, the pieces are at distance at most $4$ ($4$ for $15$ of the $89$ components, resp. $11$ of the $1\,131$).
  5. *Child-first local coverage (A5).* For every state $y'$ of a child orbit and every chart, the parent point $\chi^{-1}(y')$ is tested locally (all its parent edges must map coherently). On the orbit of $0$ at level 2, $44.0\%$ of the states pass for some chart; on $72$ random child orbits at four radii, $16\%$–$57\%$. Every child component lies within $1$–$3$ connectors of a passing state, and every component with no passing state has at most $7$ states. But passing is **not** a function of physical position ($8.3\%$ of states in mixed cells of side $0.01$, against $0.06\%$ for the success of chart $0$ alone), and the letter distance from a child state to the nearest good chart image reaches beyond 39 letters (§4.3). So (A5) holds in the data, but not in a form that a positional atlas could prove.
  6. *Gluing (A6), child first.* Near $0$ ($|y'|<0.2$, chart $0$), the child orbit of $0$ at levels $1,2,3$ collects its states from $9$, $105$ and $1\,561$ distinct parent orbits, a number that grows with the orbit (by a factor $12$–$15$ per level). All of them, except four 17-point orbits at level 3, have images in a child token component that also contains images of the orbit of $0$. On $81$ of $83$ random child orbits at four radii (155 to $1.17\cdot10^6$ states, up to $315$ parent orbits each; the other two, of 155 states, have no state with $|y'|<0.2$): the same, with gluing distance at most $1$, the diameter of the near-$0$ set at most $4$, and every component within $3$ connectors of it.
  7. *The mechanism of gluing.* In the chart-$0$ picture near $0$, the child joins $\varepsilon x$ to $\varepsilon(x+\tau_k)$ inside one token component in $22\,364$ cases where the parent token $k$ does not act at $x$, against $15\,572$ transported edges (level $1\to2$; $326\,308$ against $221\,412$ at $2\to3$); in $4\,912$ (resp. $78\,376$) of them $x$ and $x+\tau_k$ lie in different parent orbits. These are the lunes of Proposition 7 at work.
- **Conjectured.** (A4)–(A6) with $s=4$, $b=3$, gluing distance $1$, for $0<\delta<\varphi^3/55$ (Conjecture 9). With (A1)–(A3), which are finite computations not carried out here in full, Conjecture 9 implies (B) by Theorem 8.

**The remaining gap.** The reverse half: (A5) and (A6), and the coherence (A4). Each is a uniform bound on the child component graph relative to the chart images; (A5) and (A6) are reverse inclusions in their irreducible form. The data say they hold with small constants. Nothing local found here proves them: by Proposition 7 the child always has relations that a given chart image of a parent word does not see, and §4.5 shows that whether a chart is valid at a child state is not determined by its position.

Labels: **proved** (argument written here, finite computations stated), **computed** (exact unless stated; method and reproduction in §4.8), **conjecture**.

---

## 1. Setting

As in the transport note §1 and the component-graph note §1: $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$, $\varphi=(1+\sqrt5)/2$, $\sigma\colon\zeta\mapsto\zeta^2$, $E=(0,1,-1,0)$, $\varepsilon=(-3,0,-2,-2)$, $\varepsilon^{-1}=\varphi^3=(1,0,-2,-2)$. Letters $a,b$ rotate by $\zeta^{-1}$ about $\mp1$ on the closed disks $D_1,D_2$ of radius $r$; $\Gamma=\langle A,B\rangle$ is the ambient group of global rotations; $K=\Lambda_T=2(1-\zeta)\Lambda$ is its translation subgroup and the token translation module (the (T) note §1, the invariant note Proposition 2). Tokens $t_0,\dots,t_{11}$ and transport words $W(w_1)=w_3^{-1}w_1^{-1}w_3^{-1}$, $W(w_2)=w_3^{-1}w_2^{-1}w_3^{-1}$, $W(w_3)=w_3^{-1}w_2^{-1}w_3^{-1}w_1^{-1}w_3^{-1}$ as in the transport note. Lifted states $(y,j)$, sheets, token components, the component graph $\mathcal C(O)$ with distance $d_O$, and $D(\delta)=\sup_O\operatorname{diam}\mathcal C(O)$ over lattice orbits, as in the component-graph note §1.

- **Charts.** For $u\in\{\varepsilon,-\varepsilon\}$ and $t\in\mathbb C$, $\chi_{u,t}(z)=uz+t$. The *image state* of a parent state $(x,j)$ under $\chi$ is $(\chi(x),j)$ (the sheet-preserving lift of the component-graph report).
- **Images, coherence, good states.** For a parent orbit $O$ and a child orbit $O'$, a parent state $s$ *has a $\chi$-image* if its image state lies in $O'$. A chart is *coherent at $s$* if every token edge at $s$ whose other end has a $\chi$-image maps into the child component of the image of $s$, and every connector edge at $s$ whose other end has a $\chi$-image maps to an equal or adjacent child component. A *good state* of $\chi$ is a state with a $\chi$-image at which $\chi$ is coherent.
- **Local validity, child first.** For a child state $y'$ and a chart $\chi$, $\chi$ is *locally valid at $y'$* if $x=\chi^{-1}(y')$ has at least one edge at the parent radius, and every parent edge at $x$ (computed directly at the parent radius, without reference to an orbit) has its image in the child orbit of $y'$: in the token component of $y'$ for a token edge, in an equal or adjacent component for a connector edge. This is the child-first form of "good state".

## 2. Statements

### 2.1 The charts

**Proposition 1 (the chart set).** For $c\in\Lambda$, $c+u(z-c)=uz+(1-u)c$, and $1-\varepsilon=2\varphi^{-2}$, $1+\varepsilon=2\varphi^{-1}$. Hence the centred charts $z\mapsto c\pm\varepsilon(z-c)$, $c\in\Lambda$, are exactly the maps $\chi_{\pm\varepsilon,t}$ with $t\in2\Lambda$, and each $t\in2\Lambda$ comes from exactly one centre for each sign. **[proved]**

**Proposition 2 (conjugation).** Let $\chi=\chi_{u,t}$ with $t\in2\Lambda$.
1. For letters $L,L'$ with the same rotation $\omega=\zeta^{\mp1}$, about $p,p'\in\{\pm1\}$: $\chi L\chi^{-1}=T_v\circ L'$ with $v=(up+t-p')(1-\omega)\in\Lambda_T$.
2. For a translation $T_\tau$: $\chi T_\tau\chi^{-1}=T_{u\tau}$, and $u\Lambda_T=\Lambda_T$.
3. Consequently $\chi\Gamma\chi^{-1}=\Gamma$, and the image of a token path of translation $\tau$ has translation $u\tau$, the translation of the transport word. **[proved]**

For $t=0$, $u=\varepsilon$ this is Lemma 6 of the transport note.

**Proposition 3 (classes and cosets).** Write $\Lambda/K\cong\Lambda/2\Lambda\times\Lambda/(1-\zeta)\Lambda=\mathbb F_{16}\times\mathbb F_5$, and give a lattice point $y$ the label $(a(y),b(y))$, where $a(y)\in\mathbb F_5$ is the residue of $y+1$ modulo $(1-\zeta)$ (the coefficient sum of $y$, plus $1$, modulo 5) and $b(y)$ is the $\langle\zeta\rangle$-orbit of $y+1$ modulo $2$.
1. The label is a complete invariant of the 20 $\Gamma$-classes.
2. $\chi_{u,t}$, $t\in2\Lambda$, maps the class $(a,b)$ onto the class $(\bar u(a-1)+1+\bar t,\ b)$, with $\bar\varepsilon=3$, $\overline{-\varepsilon}=2$ and $\bar t$ the residue of $t$.
3. For fixed $u$ and classes $C,C'$ with the same $b$, the $t\in2\Lambda$ with $\chi_{u,t}(C)=C'$ form one coset of $\Lambda_T$; for different $b$ there is none. In particular a chart maps the orbit of $0$ into the class of $0$ iff $t\in\Lambda_T$, and two charts of the same sign whose images of one parent orbit meet one child orbit differ by an element of $\Lambda_T$. **[proved]**

**Proposition 4 (reductions).**
1. $\chi_{-\varepsilon,t}(x)=\chi_{\varepsilon,t}(-x)$, and $-O$ is a lattice orbit whenever $O$ is (the invariant note Proposition 3). So minus-charts of $O$ are plus-charts of $-O$; on orbits with $O=-O$ (the orbit of $0$, for example) the two signs give the same image sets.
2. For $s\in\Lambda_T$: $\chi_{u,t+us}(x)=\chi_{u,t}(x+s)$. So the charts of one coset are a single chart composed with the token-module translations of the parent plane; comparing two of them at $x$ is comparing one chart at $x$ and at the (in general virtual) point $x+s$. **[proved]**

**Lemma 5 (parity of transitions).** Two token components in the same sheet are at component-graph distance $0$, $2$, $4$ or at least $5$. In particular, if $\chi(x)$ and $\psi(x)$ are image states in one sheet and in different token components, a transition between them costs at least 2 connectors. **[proved]**

### 2.2 Local transport per chart

**Proposition 6 (transport criterion for any chart).** Let $\chi=\chi_{\varepsilon,t}$, $t\in\Lambda_T$, let $k$ be a token and $W$ a token word with translation $\varepsilon\tau(k)$, with pull-back centres $c'_j$. For $X\in\operatorname{dom}_r(k)$, $W$ acts at $\chi(X)$ at radius $r'$ and ends at $\chi(k(X))$ iff $|\varepsilon X-(c'_j-t)|\le r'$ for all $j$. Each test is of one of the following three kinds, unless its margin is exactly $0$ without the tangency identity of item 1 (a case that does not occur in Computation 4.2); the kind is decided by the margin $m_j=r_c^2-\max_{\operatorname{dom}_{r_c}(k)}|\varepsilon z-(c'_j-t)|^2$:
1. *tangent*: $|c'_j-t-\varepsilon c|=(1-\varepsilon)r_c$ for a test centre $c$ of $k$; then the test holds on $\operatorname{dom}_r(k)$ for every $\delta\ge0$ (transport note, Lemma 2);
2. *margin* $m_j>0$: it holds for $\varepsilon\delta\le m_j$;
3. *cutting* $m_j<0$: it restricts $\operatorname{dom}_r(k)$ to its intersection with the disk $\{X:|X-\varphi^3(c'_j-t)|\le\varphi^3r'\}$, which does not contain $\operatorname{dom}_{r_c}(k)$.

So the set where a fixed word transports $k$ under a fixed chart is $\operatorname{dom}_r(k)$ cut by finitely many circles of radius $\varphi^3r'$, uniformly for $\delta\le\min m_j/\varepsilon$ over the margin tests. **[proved; the classification of the tests for 13 charts is Computation 4.2]**

### 2.3 No chart is a word-by-word conjugacy

**Proposition 7 (the lune lemma).** Let $0\le\delta<r_c^2$, let $\chi$ be a chart, $w$ a word whose domain $U=\operatorname{dom}_r(w)$ at the parent radius has non-empty interior, and $W$ a word whose domain $V=\operatorname{dom}_{r'}(W)$ at the child radius satisfies $\chi(U)\subseteq V$. Then:
1. $\chi^{-1}(V)\setminus U$ has non-empty interior. More precisely, let $\gamma$ be a boundary arc of $U$ (an arc of a circle of radius $r$); then all but at most $2N_W$ points of $\gamma$ ($N_W$ the number of letters of $W$) are interior points of $\chi^{-1}(V)$, so $\chi^{-1}(V)\setminus U$ contains an open set along all of $\gamma$.
2. Hence no chart maps the relation "$W$ acts" at radius $r'$ onto the relation "$w$ acts" at radius $r$ on any open set meeting $\partial U$: on the chart image of a neighbourhood of every boundary arc of every parent word domain, the child has edges that the parent word does not have.
3. If $\gamma$ is not a single point at $\delta=0$, the area of $\chi^{-1}(V)\setminus U$ is bounded below by a positive constant for all small $\delta$.

**[proved]**

This is the word-level mechanism behind the one-sidedness of every renormalization of the orbit relation by a similarity tried so far (Conjecture RI of the critical-renormalization note, the reverse inclusion failing there at every defect tested), and the reason why the transport note's tangencies (Lemma 2) are inclusions. The circles of the child, pulled back by a chart, have radius $r'/\varepsilon\approx9.1$; the parent's have radius $r\approx2.15$. They can touch, but not coincide.

### 2.4 The atlas recursion

Let $\mathcal A$ be a finite set of charts, each with a closed region $G_\chi\subseteq\mathbb C$ of the parent plane. Consider, for $0<\delta\le\delta_0$, the following hypotheses, with constants $a,\tau,s,b,g,m,N_0$ independent of $\delta$.

- (A1) *Edge transport* (local). If an edge of the lifted state graph at radius $r$ has both endpoints in $G_\chi$, its two image states are joined at radius $r'$ by a path with at most $a$ connectors (token edge) or at most $1+a$ connectors (connector edge).
- (A2) *Cover of the parent region* (local). Every edge of the lifted state graph at radius $r$ has both endpoints in $G_\chi$ for some $\chi\in\mathcal A$.
- (A3) *Transitions* (local). If $x\in G_\chi\cap G_\psi$, the image states $\chi(x),\psi(x)$ are joined at radius $r'$ by a path with at most $\tau$ connectors.
- (A4) *Spread* (global). For every parent token component $P$ and every $\chi$, the child components containing image states of $P\cap G_\chi$ are pairwise within distance $s$.
- (A5) *Coverage* (global, reverse-type). Every component of every child orbit $O'$ with more than $N_0$ states lies within distance $b$ of a component that contains an image state $\chi(x)$, $x\in G_\chi$, of some parent orbit.
- (A6) *Gluing* (global, reverse-type). For such $O'$, let $\mathcal P(O')$ be the set of parent orbits having image states in $O'$, joined by an edge when they have image states in components of $O'$ at distance at most $g$. This graph has diameter at most $m$.

In (A4)–(A6) and in Theorem 8 an *image state* of a parent orbit always means $\chi(x)$ with $x\in G_\chi$ and $\chi\in\mathcal A$. (A1)–(A3) imply that all image states of one parent orbit lie in one child orbit, so $\mathcal P(O')$ is well defined.

**Theorem 8 (the atlas recursion).** Let $\delta_\ast>0$ be a defect at which $GG_5$ is finite, and suppose (A1)–(A6) hold at every $\delta\in(0,\delta_\ast/\varepsilon)$. Put $\Sigma=|\mathcal A|\,s+(|\mathcal A|-1)\tau$, $L=(m+1)(\Sigma+1+a)$ and $C=(m+1)\Sigma+mg+2b$.
1. For every parent orbit $O$ and its child orbit $O'$, any two image states of $O$ are within distance $(D(\delta)+1)\Sigma+D(\delta)(1+a)$ in $\mathcal C(O')$.
2. $D(\varepsilon\delta)\le\max\bigl(N_0,\ L\,D(\delta)+C\bigr)$.
3. Hence $D(\delta)<\infty$ for every $\delta>0$, $D(\delta)=O(\delta^{-\log L/\log\varphi^3})$, and $GG_5(r)$ is finite for every $r<r_c$.

**[proved, given (A1)–(A6), the (T) note's Theorem 4 and Corollary 5(2), and the base]**

Item 3 needs no uniformity beyond that of the constants: a multiplicative recursion gives a polynomial bound, and any finite bound at each $\delta$ suffices for (B). What a finite atlas buys is item 1: chart changes inside one parent component cost at most $\Sigma$ in total, however long the token paths are, because the charts met by one component form a connected nerve on at most $|\mathcal A|$ vertices.

**Which hypotheses are local.** (A1)–(A3) are statements about words acting on regions bounded by circles, decided by finite computations uniform in $\delta$ (Proposition 6 and the transport note's method). (A4)–(A6) are statements about child components and parent orbits. Of these, (A5) and (A6) are the reverse-type steps: they say that the child orbit has nothing that is far from the chart images, and that the child joins the images of different parents closely. Proposition 7 indicates that neither can follow from the charts alone, since the child's extra relations are exactly what a chart image of a parent word does not see; this is an assessment, not a theorem.

**Conjecture 9 (uniform atlas constants).** For $0<\delta<\varphi^3/55$, with $\mathcal A$ the coherent class-$0$ charts of §4.3 (and their analogues in the other classes), (A4) holds with $s=4$, (A5) with $b=3$, $N_0=40$, and (A6) with $g=1$, $m\le2$. **[conjecture]** Evidence: §4.4–§4.6. The range is the one Theorem 8 needs with the base $\delta_\ast=1/55$. The regions $G_\chi$ are not specified; $s=4$ is what the pairwise spread of §4.4 needs with $G_\chi=\mathbb C$ (distance $2$ from the plurality component, $4$ between two minority pieces).

---

## 3. Proofs

### 3.1 Proposition 1

$1-\varepsilon=4-2\varphi=2(2-\varphi)=2\varphi^{-2}$ and $1+\varepsilon=2\varphi-2=2\varphi^{-1}$, by $\varphi^2=\varphi+1$. Since $\varphi$ is a unit of $\Lambda$, $(1\mp\varepsilon)\Lambda=2\Lambda$, and $c=t/(1\mp\varepsilon)$ is the unique centre. $\square$

### 3.2 Proposition 2

$\chi^{-1}(z)=(z-t)/u$, and $L(w)=p+\omega(w-p)$. The computation is the same for $\chi^{-1}=\chi_{u^{-1},-t/u}$, with $u^{-1}=\pm\varphi^3$ and $-t/u\in2\Lambda$, since $\varphi^3-1=2\varphi$ and $\varphi^3+1=2\varphi+2$ also lie in $2\mathbb Z[\varphi]$. Then $\chi L\chi^{-1}(z)=up+\omega(z-t-up)+t=\omega z+(up+t)(1-\omega)$, while $L'(z)=\omega z+p'(1-\omega)$. The difference is $v=(up+t-p')(1-\omega)$. Here $up-p'\in\{\pm(\varepsilon-1),\pm(\varepsilon+1)\}=\{\pm2\varphi^{-2},\pm2\varphi^{-1}\}\subset2\Lambda$ and $t\in2\Lambda$; $1-\omega$ is an associate of $1-\zeta$. So $v\in2(1-\zeta)\Lambda=\Lambda_T$. Item 2: $\chi T_\tau\chi^{-1}(z)=u((z-t)/u+\tau)+t=z+u\tau$, and $u$ is a unit. Item 3: $\Gamma$ is generated by $A,B$, and its translations are $\Lambda_T$ (the invariant note, Proposition 2); items 1–2 show $\chi A\chi^{-1},\chi B\chi^{-1}\in\Gamma$, and the same for $\chi^{-1}$. $\square$

### 3.3 Proposition 3

*Item 1.* $2$ and $1-\zeta$ generate coprime ideals ($N(1-\zeta)=5$ is odd), so $\Lambda/K\cong\Lambda/2\Lambda\times\Lambda/(1-\zeta)\Lambda$ by the Chinese remainder theorem, with $\Lambda/2\Lambda\cong\mathbb F_{16}$ ($2$ is inert in $\mathbb Z[\zeta]$, since $2$ has order 4 modulo 5) and $\Lambda/(1-\zeta)\cong\mathbb F_5$ via $\zeta\mapsto1$. By the invariant note's Proposition 2, $y,y'$ are in one $\Gamma$-class iff $y'+1\equiv\zeta^m(y+1)\pmod K$ for some $m$. Since $\zeta\equiv1\pmod{1-\zeta}$, the $\mathbb F_5$-part of $y+1$ is unchanged by $\zeta^m$, and on $\mathbb F_{16}$ multiplication by $\zeta$ has order 5 and fixes only $0$, so its orbits are $\{0\}$ and three orbits of size 5. That gives $5\times4=20$ classes, each determined by $(a,b)$.

*Item 2.* $\chi(y)+1=u(y+1)+(t+1-u)$. Modulo $(1-\zeta)$: $\varepsilon=(-3,0,-2,-2)\mapsto-7\equiv3$, so $\bar u=3$ for $\varepsilon$ and $2$ for $-\varepsilon$, and $a(\chi(y))=\bar u\,a(y)+\bar t+1-\bar u=\bar u(a(y)-1)+1+\bar t$. Modulo $2$: $\pm\varepsilon\equiv(1,0,0,0)$ and $t\equiv0$, so $\chi(y)+1\equiv y+1$, and $b$ is unchanged.

*Item 3.* For $t=2\lambda$, $\bar t=2\bar\lambda$, and $2$ is invertible in $\mathbb F_5$; so prescribing $\bar t$ prescribes $\lambda$ modulo $(1-\zeta)$, i.e. $t$ modulo $2(1-\zeta)\Lambda=\Lambda_T$. For the orbit of $0$, $a=1$, and $\bar u\cdot0+1+\bar t=1$ iff $\bar t=0$. An orbit of $GG_5(r)$ lies in one $\Gamma$-class (the invariant note, Proposition 2(3)), so images of one parent orbit in one child orbit come from charts with the same $\bar t$. $\square$

### 3.4 Proposition 4 and Lemma 5

Proposition 4: $-\varepsilon x+t=\varepsilon(-x)+t$; $z\mapsto-z$ conjugates $a$ to $b$ and maps $D_1$ to $D_2$, so it maps orbits to orbits. And $u(x+s)+t=ux+(t+us)$. Lemma 5: token moves keep the sheet $j\in\mathbb Z/5$ and each connector changes it by $\pm1$ (the component-graph note §1). A path between two components of one sheet with $k$ connectors has signs $e_i=\pm1$ with $\sum e_i\equiv0\pmod5$; for $k\le4$ this forces $\sum e_i=0$, hence $k$ even. $\square$

### 3.5 Propositions 6 and 7

*Proposition 6.* If the first letters of $W$ have acted at $Z=\chi(X)$, letter $j$ acts iff $|Z-c'_j|\le r'$ (pull-back centres, the transport note §1); $|\varepsilon X+t-c'_j|=|\varepsilon X-(c'_j-t)|$. $W$ has rotation $0$ and translation $\varepsilon\tau(k)$, so it ends at $\varepsilon X+t+\varepsilon\tau(k)=\chi(k(X))$. The three kinds are the argument of the transport note §3.3 with $c'$ replaced by $c'-t$; the region removed by a cutting test is the complement of the pulled-back disk $\chi^{-1}(D(c'_j,r'))=D(\varphi^3(c'_j-t),\varphi^3r')$.

*Proposition 7.* $\chi^{-1}(V)=\bigcap_jD\bigl(\chi^{-1}(c'_j),R\bigr)$ with $R=r'/\varepsilon$, since $\chi$ is a similarity of ratio $\varepsilon$. As $r'\ge r$ and $\varepsilon<1$, $R>r$. Let $\gamma\subseteq\partial U$ be an arc of a circle $S$ of radius $r$. Each boundary circle of $\chi^{-1}(V)$ has radius $R\ne r$, so it meets $S$ in at most two points; there are at most $N_W$ such circles. Every other point $p\in\gamma$ lies in $\chi^{-1}(V)$ (because $U\subseteq\chi^{-1}(V)$) and on none of its boundary circles, hence in its interior. But $p\in\partial U$, so every neighbourhood of $p$ contains points outside $U$; a small one lies inside $\chi^{-1}(V)$. This proves item 1, and item 2 restates it ($W$ acts at $\chi(X)$ for $X\in\chi^{-1}(V)$, $w$ does not act at $X\notin U$). Item 3: at $\delta=0$ the configuration (centres fixed, radii $r_c$ and $r_c/\varepsilon$) gives, by item 1 there (the inclusion $\chi(U)\subseteq V$ at $\delta=0$ follows from the inclusions at small $\delta>0$ by closedness), an open set $\Omega_0\subseteq\chi^{-1}(V)\setminus U$; the disks depend continuously on $\delta$ and $U$ only shrinks as $\delta$ grows, so a compact disk inside $\Omega_0$ at positive distance from all boundary circles stays inside $\chi^{-1}(V)\setminus U$ for small $\delta$. $\square$

### 3.6 Theorem 8

*(A1)–(A3) put all images of a parent orbit in one child orbit.* Two states of a parent orbit are joined by a path; each edge lies in some $G_\chi$ (A2) and its image states are joined (A1); at a common vertex of consecutive edges in charts $\chi,\psi$ the two image states are joined (A3).

*Item 1.* Let $P$ be a parent token component and $\mathcal A_P$ the charts with $P\cap G_\chi\ne\varnothing$. Join $\chi,\psi\in\mathcal A_P$ when $P\cap G_\chi\cap G_\psi\ne\varnothing$. This nerve is connected: along a token path in $P$, consecutive edges lie in $G_{\chi_i}$, $G_{\chi_{i+1}}$ (A2) and share a vertex in both. So two charts of $\mathcal A_P$ are joined by a chain $\chi_0,\dots,\chi_n$, $n\le|\mathcal A|-1$, with states $z_i\in P\cap G_{\chi_{i-1}}\cap G_{\chi_i}$. For image states $\chi_0(x)$ and $\chi_n(y)$, $x,y\in P$:
$$d(\chi_0(x),\chi_n(y))\le d(\chi_0(x),\chi_0(z_1))+\sum_{i=1}^{n}\bigl[d(\chi_{i-1}(z_i),\chi_i(z_i))+d(\chi_i(z_i),\chi_i(z_{i+1}))\bigr],$$
with $z_{n+1}=y$. The terms comparing two image states under one chart are at most $s$ (A4), and the transition terms $d(\chi_{i-1}(z_i),\chi_i(z_i))$ at most $\tau$ (A3); there are $n+1\le|\mathcal A|$ of the first kind and $n$ of the second. So all image states of $P$ are within $\Sigma$ of each other. Now let $s_1,s_2$ be states of $O$, in components $P_0,P_k$ with $d_O(P_0,P_k)=k\le D(\delta)$, along a shortest chain $P_0,\dots,P_k$ joined by connector edges $e_i$. By (A2) and (A1) each $e_i$ has image states joined by at most $1+a$ connectors, with one end among the image states of $P_{i-1}$ and the other among those of $P_i$. Summing: $d\le(k+1)\Sigma+k(1+a)$.

*Item 2.* Let $O'$ have more than $N_0$ states and let $X',Y'$ be components of $O'$. By (A5) they are within $b$ of components containing image states of parent orbits $O_1,O_2$. By (A6) there is a chain $O_1=Q_0,\dots,Q_\ell=O_2$, $\ell\le m$, with image states of $Q_{i-1}$ and $Q_i$ in components at distance at most $g$. Within each $Q_i$, item 1 bounds the distance between any two of its image states by $(D+1)\Sigma+D(1+a)$, $D=D(\delta)$. So
$$d(X',Y')\le2b+(m+1)\bigl[(D+1)\Sigma+D(1+a)\bigr]+mg=L\,D+C .$$
Orbits with at most $N_0$ states have diameter less than $N_0$.

*Item 3.* Write $\delta=\varepsilon^k\delta'$ with $\delta'\in[\delta_\ast,\delta_\ast/\varepsilon)$. As in the proof of the component-graph note's Theorem 3 (refereed, with its fixed bound), $D(\delta')\le X:=\max(N_0,5|GG_5(r_\ast)|)$ by orbit monotonicity, and item 2 gives by induction $D(\varepsilon^k\delta')\le L^kX+C(L^k-1)/(L-1)$ (read $kC$ for the last term if $L=1$; the maximum with $N_0$ never binds, since $L\ge1$ and the bound is at least $X\ge N_0$ at every step); since $k\le\log(\delta_\ast/\delta)/\log\varphi^3$, this is $O(\delta^{-\log L/\log\varphi^3})$. Finiteness of $D(\delta)$ at every $\delta<\delta_\ast$ gives finiteness of $GG_5(r)$ at non-norm radii by Corollary 5(2) of the (T) note with the lattice reduction of `sharp-lower-bound-n5.md` Theorem 4.1, at norm radii and at $\delta\ge\delta_\ast$ by group monotonicity (`boundary-contact.md` Theorem 3.4), exactly as in the component-graph note's Theorem 3. $\square$

---

## 4. Computations

Exact arithmetic as in the component-graph note §6: integer 4-vectors, disk tests as signs in $\mathbb Z[\varphi]$ with 128-bit integers, lifted orbits by breadth-first search, union-find token components, the deduplicated component graph. Physical positions printed as decimals are double-precision evaluations of exact points, used only to select and to bin. Radii: levels $(29,10,10)$, $(33,8,10)$, $(17,18,10)$, $(85,-24,10)$ for $r^2=(P+Q\varphi)/D$; for a parent defect $p/D$ the parent is $(3D-p,D,D)$ and the child $(3D+3p,D-2p,D)$. "Charts" are $\chi_{u,t}$ with $t=2\lambda$, $\lambda\in\Lambda$, $|t|\le3.4$ and $|\sigma t|\le T_\sigma$ as stated; the internal shift $|\sigma t|$ has to reach about 40 to find the coherent charts (the chart centred at $-F$ has $t=-2\varepsilon E$, $|\sigma t|=16.1$); with $|\sigma t|\le3$ only $t=0$ succeeds.

### 4.1 Pointwise census (orbit of $0$, level $1\to2$)

$8\,142$ charts (both signs, all cosets, $T_\sigma=40$). $1\,318$ map more than $5\%$ of the $30\,165$ parent states into the child orbit ($400\,519$ states); every one has $t\in\Lambda_T$ (Proposition 3) and keeps the sheet of every image. The two signs give identical counts (Proposition 4(1)). The union of all images covers $93.2\%$ of the child states, uniformly in $|y'|$ (about $7\%$ uncovered in every radial bin). The best charts: $t=\pm2\sqrt5\,\varepsilon=\pm(14,0,8,8)$ ($|t|=1.056$, success $0.693$), a family with $|t|=0.898$ ($0.680$), $t=0$ ($0.679$); the chart centred at $-F$, $t=-2\varepsilon E=(-4,6,-6,4)$ ($|t|=0.555$), has success $0.546$. Pointwise success is cheap: both orbits are cut-and-project-like sets with compatible windows, and almost every child point is a chart image of a parent point for some of the many charts. **[computed, exact memberships]**

### 4.2 Transport margins for nonzero charts (rigorous)

For the transport words of $w_1,w_2,w_3$ and 13 charts, the margins $m_j$ of Proposition 6 over $\operatorname{dom}_{r_c}(k)$, by the enumeration of extreme points of the transport note §4 in 50-digit arithmetic (candidates kept to $10^{-40}$; every reported margin is far from $0$ except the exact tangencies of $t=0$):

| chart $t$ | $\lvert t\rvert$ | $w_1$: tangent / cutting (worst) | $w_2$ | $w_3$ |
|---|---|---|---|---|
| $0$ | $0$ | 4 / 2 ($-1.056$) | 4 / 2 ($-1.056$) | 4 / 0 |
| $(-20,-4,-10,-16)$ | $0.343$ | 0 / 3 ($-2.13$) | 0 / 6 ($-1.42$) | 0 / 6 ($-1.34$) |
| $(-10,-6,-2,-12)$ | $0.555$ | 0 / 4 ($-2.42$) | 0 / 4 ($-3.23$) | 0 / 6 ($-2.42$) |
| $(-4,6,-6,4)=-2\varepsilon E$ (centre $-F$) | $0.555$ | 2 / 5 ($-2.67$) | 0 / 5 ($-2.67$) | 2 / 6 ($-2.67$) |
| $(-6,-4,-2,-8)$ | $0.898$ | 0 / 5 ($-4.88$) | 0 / 6 ($-4.22$) | 0 / 8 ($-4.22$) |
| $(-14,0,-8,-8)$ | $1.056$ | 0 / 7 ($-5.59$) | 0 / 7 ($-5.23$) | 0 / 10 ($-5.59$) |
| $(2,4,0,4)$ | $1.453$ | 0 / 7 ($-8.30$) | 2 / 8 ($-9.75$) | 0 / 10 ($-8.27$) |

(The images of these rows under $z\mapsto-z$ and $z\mapsto\bar z$ give the same counts with $w_1,w_2$ exchanged as appropriate.) So the chart-$0$ transport words, which have the full tangency structure at $t=0$, are cut by 3 to 10 circles for every nonzero chart tested. A nonzero chart transports tokens on a region that is a proper part of the token domain, and needs its own list of words near the cut circles. **[computed, rigorous for the classification]**

### 4.3 Structural census (orbit of $0$, level $1\to2$)

$801$ plus-charts in the coset $\Lambda_T$ ($T_\sigma=40$). For each: pointwise success, token coherence (token edges with both images present that map into one child component) and connector coherence (connector edges between distinct parent components with both images present that map to adjacent child components).

- Only $t=0$ has both coherences equal to $1$ ($24\,300$ token edges, $29\,128$ connector edges). The next best are $0.986$ ($|t|=0.343$) and $0.971$ (the four charts with $|t|=0.555$, among them the chart centred at $-F$). $53$ charts have both coherences at least $0.9$ ("good charts"). Some charts with high pointwise success have token coherence $0$ (for example $t=(2,4,0,4)$, success $0.677$): they map points into the orbit but edges into different components.
- *Parent side:* every parent state is a good state of some good chart ($100\%$).
- *Child side:* the good-chart images cover $41.9\%$ of the child states, the good states' images $40.4\%$. Uncovered fraction by $|y'|$ in bins of $0.3$: $0.07,\,0.09,\,0.10,\,0.18,\,0.48,\,0.63,\,0.64,\,0.64,\,0.66,\,0.97,\,1.00$. Every child component lies within $3$ connectors of a component containing a good image ($19\,053$ / $73\,802$ / $33\,270$ / $40$ components at distance $0/1/2/3$), as for chart $0$ alone ($989$ / $90\,222$ / $34\,570$ / $384$). The components with no good image hold $160\,972$ states and have at most $50$ states each. The letter distance (every letter costs 1) from a child state to the nearest good image has maximum at least $39$ ($8\,428$ states at $\ge39$).

**[computed, exact]**

### 4.4 Transitions and spread

*Transitions.* For each parent state, the distinct child components among its images under the good charts at which it is a good state: $10\,009$ states have one, $9\,608$ two, $5\,180$ three, up to seven or more for $786$. Every parent state is a good state of at least 3 good charts (21 at the median), so the $10\,009$ are states where all good charts agree up to token moves: there the transition is free. On all $20\,156$ states with at least two, the largest mutual distance of these components is $2$ for $19\,952$ and $4$ for $204$ (Lemma 5 forbids 1 and 3; on a sample of every 13th such state: $1\,542$ and $15$). So transitions cost $0$, $2$ or $4$: either the good charts agree, or they put the same parent state into different child components of one sheet, at least 2 connectors apart.

*Spread (A4).* For chart $0$ and each parent component with at least 5 states and an image: the child components containing images, and their distance from the plurality component.
- Level $1\to2$: all $89$ such components split, each at distance exactly $2$; plurality share at least $0.800$ (at least $0.953$ for the 11 components of at least 100 states).
- Level $2\to3$: $1\,131$ components; $116$ unsplit, $1\,015$ at distance exactly $2$; plurality at least $0.800$.
- Chart $(-10,-6,-2,-12)$ at $1\to2$: $78$ unsplit, $9$ at distance $2$, $2$ at $4$. Chart $(-6,-4,-2,-8)$: $32$ unsplit, $57$ at $2$, plurality at least $0.60$.

Pairwise, as in (A4), two minority pieces can be $4$ apart: chart $0$ at $1\to2$, $74$ components with largest pairwise distance $2$ and $15$ with $4$; at $2\to3$, $1\,004$ and $11$; chart $(-10,-6,-2,-12)$, $4$ and $7$.

The split pieces are the parts of a parent component on either side of the failure caps, which the child images separate by two connectors. **[computed, exact]**

### 4.5 Child-first local coverage (A5)

`lcov`: for each child state $y'$ and each chart, $x=\chi^{-1}(y')$ is tested at the parent radius (its 12 tokens and 4 letters computed directly), as in §1. No parent orbit is needed.

- *Orbit of $0$ at level 2*, $1\,602$ charts of the coset ($T_\sigma=40$): $44.0\%$ of the states have a locally valid chart ($25.4\%$ if $x$ is required to carry a token edge). Uncovered fraction by $|y'|$ (bins of $0.3$): $0.39,\,0.04,\,0.15,\,0.18,\,0.45,\,0.52,\,0.50,\,0.66,\,0.66,\,0.98,\,1.00$. Every component lies within $2$ connectors of a covered one; the largest component with no covered state has 15 states.
- *Random child orbits*, child seeds as in the transport note §6.1 (physical point uniform in $D_1\cup D_2$, internal point uniform of modulus at most $25/(\varepsilon\delta)$), $2\,022$ charts of all five cosets ($T_\sigma=20$), children with more than 40 and at most $3\cdot10^6$ states, parent defects $1/16$, $1/30$, $2/45$, $1/55$ (generator seeds 401–404): 72 children with more than 40 states (155 to $1\,463\,939$ states). The covered fraction is $0.16$–$0.57$, and at least $0.55$ on every child with at least $8\,000$ states. Every component lies within $3$ connectors of a covered one (maximum $1$ on 2 children, $2$ on 58, $3$ on 12), and every component with no covered state has at most $7$ states.
- *Is validity positional?* Binning the level-2 child states in square cells of side $h$, the states in cells that contain both covered and uncovered states are $40.4\%$, $18.6\%$, $8.3\%$, $2.4\%$ for $h=0.05,0.02,0.01,0.005$. For the success of chart $0$ alone the component-graph note (Computation 4.7) found $0.84\%$, $0.21\%$, $0.06\%$, $0.01\%$. At $h=0.01$ the cells hold about $1.6$ states on average, so local validity of the atlas is not a function of physical position at the resolution where chart-$0$ success already is.

**[computed, exact]**

### 4.6 Gluing (A6), child first

`merge`: for a child orbit, its states $y'$ with $|y'|<0.2$; the parent orbit of $\varepsilon^{-1}y'$ at the parent radius (exact breadth-first search, shared hash); the parent orbits as groups; the child component-graph distance from the components containing images of the main group (the parent orbit with most such states) to each other group's.

| child orbit | states $\lvert y'\rvert<0.2$ / comps | parent orbits | largest parents | groups at distance $0$ / $1$ | diameter of the near-$0$ set | max distance to it |
|---|---|---|---|---|---|---|
| $0$, level 1 | 245 / 11 | 9 | 1 433, 543, 543 | 9 / 0 | 3 | 2 |
| $0$, level 2 | 3 221 / 67 | 105 | 30 165, 590 (×4) | 105 / 0 | 4 | 2 |
| $0$, level 3 | 45 557 / 787 | 1 561 | 400 519, 8 166 (×4) | 1 557 / 4 (17-point orbits) | 4 | 2 |
| $E$, level 2 | 2 073 / 22 | 64 | 20 424, 549 | 64 / 0 | 4 | 2 |

Random child orbits (child seeds as in §4.5, generator seeds 301–304, parent defects $1/16$, $1/30$, $1/40$, $1/55$, 40 seeds each): 83 children with more than 40 states (155 to $1\,167\,561$ states). Two of them (155 states each) have no state with $|y'|<0.2$. On the other 81: up to $315$ parent orbits per child; every group at distance $0$ from the main group except one group at distance $1$ on each of two children ($855\,972$ and $1\,167\,561$ states); the diameter of the near-$0$ set at most $4$; every component within $3$ connectors of it.

So the number of parent orbits that one child orbit glues together grows with the orbit (by a factor $12$–$15$ per level for the orbit of $0$), while the gluing distance stays at $0$ or $1$. A recursion that charged a cost per glued parent would fail; Theorem 8 charges per step of the gluing graph. In the part of it measured here (chart $0$, states with $|y'|<0.2$) every group is within distance $1$ of the main one, so with $g=1$ that part has diameter at most $2$; the full graph $\mathcal P(O')$ of (A6), over all charts and all of $O'$, was not computed. **[computed, exact; the selection $|y'|<0.2$ is double precision]**

### 4.7 The mechanism: new connections in the lunes

`lune`: for child states $y'$ with $|y'|<0.24$ and each token $k$, with $x=\varepsilon^{-1}y'$ and $z=x+\tau_k$: is $\varepsilon z$ in the token component of $y'$, and does the parent token $k$ act at $x$?

| pair | child states | $k$ acts, $\varepsilon z$ in the component | $k$ does not act, $\varepsilon z$ in the component | of these, $x,z$ in different parent orbits |
|---|---|---|---|---|
| level $1\to2$ | 4 457 | 15 572 | 22 364 | 4 912 |
| level $2\to3$ | 63 117 | 221 412 | 326 308 | 78 376 |

In every case both $x$ and $z$ lie in $D_1\cup D_2$. The child joins, inside one token component, more pairs that the parent token does not join than pairs it does, and about a fifth of those join different parent orbits. This is Proposition 7 seen on the lattice: the gluing of (A6) happens through the lunes. **[computed, exact]**

### 4.8 Reproduction

Throwaway C and Python programs in the session scratch folder, not committed; described so that they can be re-implemented. All use the exact lattice library of the component-graph note §6 (`orb.h`, `z5.h`).
- `atlas` (§4.1): both orbits; enumeration of $t=2\lambda$ over a coefficient box ($|\lambda_i|\le20$) filtered by $|t|$ and $|\sigma t|$; image lookup with the sheet-preserving lift first; per-chart success, sheet shift, token coherence; union coverage.
- `atlas2`–`atlas4` (§4.3, §4.4): as `atlas`, restricted to the coset $\Lambda_T$; connector coherence by binary search in the sorted adjacency lists; good charts at threshold $0.9$; good states; coverage of both sides; distances by multi-source breadth-first search on the component graph; letter distance by breadth-first search on states; transitions from the list of image components of each parent state, distances by breadth-first search (every 13th state).
- `sc` (§4.4, spread): images of each parent component under one chart; plurality; breadth-first search from it.
- `chartrig.py` (§4.2): the transport note's `qz.py`/`rig.py` (exact $\mathbb Q(\zeta)$ pull-back centres, `mpmath` at 50 digits), with the target centres shifted by $-t$.
- `lcov`, `lcov2`–`lcov4` (§4.5): child orbit only; parent tests through the exact letter function at the parent radius; `ladv.sh` drives random children (`gen` and `near0` of the transport note).
- `merge`, `madv.sh`, `msum.py` (§4.6); `lune` (§4.7), token translations from the global letters applied to $0$, exact parent-orbit search for the endpoints.

Peak memory about 2 GB (level $2\to3$; 1.85 GB measured for `lune`); every run on at most 4 cores.

---

## 5. What the computations say, in plain terms

A chart is a little copy of the whole parent picture, shrunk by $\varepsilon$ and placed somewhere in the child picture. The hope was that finitely many such copies, each a faithful image of the parent dynamics on its patch, would tile the child, so that every child statement would be a parent statement plus a bounded cost for passing from one copy to the next.

The copies exist, and the parent side is fully tiled: every parent state sits in some copy that carries all its edges into the child. But the copies are not faithful in the other direction. Each copy has more connections than the parent piece it comes from: the child's circles, seen through a chart, are four times flatter than the parent's, so wherever a parent token stops at a circle, the corresponding child token goes a little further (Proposition 7). Through these extra connections the child glues together pieces of many different parent orbits (105 of them near $0$ at level 2, 1 561 at level 3), and its states outside the copies (about $60\%$) are reached only through child components that no chart describes. The glue is tight in the data: everything is within one or two connectors. But to prove that it is tight one has to know the child's own components, and that is the original problem one level down.

## 6. Assessment

- **Atlas formulation: settled.** Charts are $z\mapsto\pm\varepsilon z+t$, $t\in2\Lambda$; the relevant ones for an orbit form one coset of $\Lambda_T$ (Propositions 1–4). Theorem 8 is the correct multi-chart recursion: finiteness of the atlas bounds the cost of chart changes per parent component, and any uniform constants give (B).
- **The local part: reducible to finite computations, not carried out in full.** (A1)–(A3) are cell problems of the transport note's kind (Proposition 6; Computation 4.2 shows the cutting circles for nonzero charts). Transitions cost $0$, $2$ or $4$ in the data ($0$ for a third of the parent states; Lemma 5 forbids 1 and 3); Theorem 8 absorbs this.
- **The global part: not reduced.** (A4) spread, (A5) coverage and (A6) gluing are uniform bounds on the child component graph relative to the chart images. Proposition 7 shows that wherever a child word domain contains the chart image of a parent word domain, it contains it strictly, by lunes of positive rescaled area, and §4.5–§4.7 show the consequences on the lattice: validity of charts is not positional, and the gluing joins a growing number of parent orbits. A reverse-type statement is needed at exactly two places, (A5) and (A6), and no chart supplies it directly. This agrees with the referee of the transport note, who predicted that an atlas would reduce (R2) only if the covering could be proved from physical position alone; it cannot (§4.5).
- **Overall: the atlas route is dead as a reduction of (K) to local statements.** This is a judgement from Proposition 7 and the data, not a theorem: nothing here excludes a local, child-side proof of (A5) and (A6). The data remain uniform ($s\le4$, $b\le3$, gluing distance $\le1$, near-$0$ diameter $\le4$ at all radii tested), so the structure is there; what is missing is a mechanism for the gluing. **I believe the chord-token programme needs a new idea for it.** The candidates I see are recorded in `notes/ideas.md`: a forward-type completeness statement for child token components near $0$ (every lattice point of the right class in a window lies in a hub component, as the one-line model set of Proposition 13 of the orbit-of-zero note does on the chord), which would make gluing automatic; and a renormalization of the radius rather than of the plane (the parent-radius orbits of the child's own points form a partition of the child orbit by orbit monotonicity, joined only through the rim $r<|y\mp1|\le r'$, so the question becomes how often a shortest path must cross the rim).
