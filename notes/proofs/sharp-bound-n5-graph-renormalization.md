# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: transport of tokens and connectors by $\varepsilon$, and what the renormalization statement (R) still needs

Authors: Eric Vergo, Claude

**Review.** Independently refereed: [`referee-report-sharp-bound-n5-graph-renormalization.md`](referee-report-sharp-bound-n5-graph-renormalization.md). Verdict: correct after minor fixes. Theorem 1 needed the corrected form of the bound in item 3 and the lattice reduction at non-norm radii; the proof of Theorem 3 as first written covered $\delta\le0.16169$ only, and with the tangency identity used for every centre that satisfies it, it gives every $\delta\ge0$; Lemma 2, Theorem 4, Corollary 5 and Lemma 6 are correct; two numbers of §4.2 were corrected. All margins were re-derived by an independent exact branch-and-bound, and §6.2 and the transport statements were reproduced exactly. The note continues [`sharp-bound-n5-component-graph.md`](sharp-bound-n5-component-graph.md) (not refereed; "the component-graph note"), whose Theorem 3 reduces finiteness to its hypothesis (R), and its referee report [`referee-report-sharp-bound-n5-component-graph.md`](referee-report-sharp-bound-n5-component-graph.md), and uses [`sharp-bound-n5-token-components.md`](sharp-bound-n5-token-components.md) (refereed: [`referee-report-sharp-bound-n5-token-components.md`](referee-report-sharp-bound-n5-token-components.md); "the (T) note"): its Theorem 4 (internal diameter of every token component $<72.07/\delta+41.82$) and its Corollary 5(2) (at fixed $r$, $GG_5(r)$ is finite iff $D(r)<\infty$). From refereed notes it uses: the definitions of [`sharp-bound-n5-chaining.md`](sharp-bound-n5-chaining.md) §1 and the enumeration method of its Computation 1.2; the test centres of Table 1.1 of the (T) note, which are those of `sharp-bound-n5-critical-orbits.md` Table 2.1 (refereed); the conjugation symmetry of `sharp-bound-n5-invariant.md` Proposition 3; orbit and group monotonicity, `boundary-contact.md` Theorems 3.1 and 3.4 (refereed, Lean-checked); and, as the base case, the certified finiteness at $\delta=1/55$ of [`../certificates.md`](../certificates.md).

**What is established and what is not.** Let $r_c=\sqrt{3+\varphi}$, $\delta=r_c^2-r^2$, $\varepsilon=\varphi^{-3}$, and $r'$ the radius with $r_c^2-r'^2=\varepsilon\delta$.

- **Not established: (B), and not (R).** Finiteness of $GG_5(r)$ for every $r<r_c$ is not proved. Hypothesis (R) of the component-graph note (with fixed $N_0,b$) is not proved. **Conjecture 5.1 of the component-graph note is false as originally stated** (its referee report §4: child orbits of 155–1 757 states whose parents have no large component, so (R2) fails with $\mathcal D$ = large components, while (R1) fails with $\mathcal D$ = all components). The formulation used here is (R$^\flat$) of §2.1, with the repaired $\mathcal D$ of that report (components of at least 5 states) in Conjecture 7.1. The local part of (R1) is proved for tokens; its global part and (R2) are open, and neither is reduced to a finite computation.
- **Proved.**
  1. *What suffices, and what that means* (Theorem 1). A recursion $\operatorname{diam}\mathcal C(O')\le F_\delta(\operatorname{diam}\mathcal C(O))$ from a parent at $\delta$ to every child at $\varepsilon\delta$ with more than $N_0(\delta)$ states, with any finite monotone $F_\delta$, gives (B). In particular (R1) may carry a factor and an additive constant. But, as the referee of the component-graph note observed, with $\delta$-dependent constants this hypothesis is *equivalent* to (B) (take $F_\delta\equiv D(\varepsilon\delta)$); a renormalization statement has content only if its constants are uniform, or are derived from local structure. Theorem 1(3) records the uniform version: $F_\delta(D)\le D+C$ gives $D=O(\log1/\delta)$, which suffices.
  2. *Transport of the $w_3$-type tokens, everywhere* (Theorem 3). For every $\delta\ge0$ and each of the four tokens $w_3^{\pm1}$, $(\iota w_3)^{\pm1}$: wherever the token acts at $X$ at radius $r$, its five-token transport word acts at $\varepsilon X$ at radius $r'$ and ends at $\varepsilon$ times the token image. No condition on $X$. The proof is a finite list of disk containments: 12 tangencies that hold for all $\delta\ge0$ by concavity of the square root (Lemma 2), 4 of them touching, and 14 containments with margins at least $0.50301$, valid for $\delta\le2.1307$; for $\delta>3\varphi-4\approx0.8541$ the domain of $w_3$ is empty.
  3. *Transport of the $w_1,w_2$-type tokens: the exact domain* (Theorem 4). For $0\le\delta\le2.79$ and $X$ in the domain $U_1(r)$ of $w_1$, the transport word $w_3^{-1}w_1^{-1}w_3^{-1}$ acts at $\varepsilon X$ **if and only if** $\varepsilon X$ lies in two explicit disks of radius $r'$. All other 14 disk tests of the word hold on all of $\varepsilon U_1(r)$. The same for the other seven tokens of this type by symmetry. Consequently (Corollary 5), for $0<\delta\le\tfrac1{10}$, every token edge whose two endpoints lie in the disk $|z|\le0.99$ maps under $\varepsilon$ to a token path at $\varepsilon\delta$ of 3 or 5 tokens.
  4. *Connectors change letter freely* (Lemma 6). $\varepsilon\,L\,\varepsilon^{-1}=T_v\circ L'$ for each pair of letters $L,L'$ of the same rotation sense, with $v$ in the token translation module. So the $\varepsilon$-image of a connector edge is a path with exactly one connector whenever suitable tokens act; which letter it uses depends on the position.
- **Computed** (exact orbit arithmetic; geometry in 50-digit or double precision as stated; §6).
  1. Where the $w_1$ transport word fails, no token word of at most 5 tokens joins the images, and at generic such points none of at most 9. On the orbit of $0$ ($1\to2$) the failure set meets the edges with both images present only near two corners, where 11- and 13-token detours join them (6 edges per token type).
  2. **The claim "token edges with both images present map into one child component" is false.** At $\delta=1/16$ a parent orbit of 40 states has a token edge whose two $\varepsilon$-images lie in the child orbit (665 states) but in different token components (§6.2). (R1) for large components is not affected on that pair.
  3. Connector edges: 99.8% of connector edges with both images present ($1\to2$, orbit of $0$) are realized by two tokens and one letter; the rest need 6 symbols or more than 8. In the disk $|X|\le1$ with $|L(X)|\le1$, the transport words with at most 3 tokens cover everything except a lune inside the pentagonal gap above the centre, which contains no orbit point.
  4. The success region $G$ (where $\varepsilon y$ lies in the child orbit) consists of whole clusters of the orbit: the failures are the clusters in two caps at the top and bottom of $D_1\cup D_2$.
  5. Births: 46–47% of the states of a child orbit lie in components that contain no image (98% of these components have at most 10 states; the largest has $10\,799$ at level $2\to3$). All lie within 3 connectors of an image component. Every child component outside $|y|<0.75$ is born, since all images lie in that disk: (R2) is a statement about the whole child orbit.
  6. Adversarial test from the child side: 248 random child orbits with more than 40 states at 8 parent radii ($\delta=1/16$ to $3/80$, most outside the earlier families). Every one has a point within $0.2217<\varepsilon$ of $0$, hence a parent through $|y|<0.94$. With $\kappa$ on large components: no violation of (R1), connector edges map to distance $\le1$, births within 1, every child component within 3 of an image. With $\kappa$ on all components (172 pairs): (R1) fails on $0.05$–$0.09\%$ of ordered pairs, always by exactly $+2$ ($1\to3$, $2\to4$).
  7. A multi-chart structure: the child orbit of $0$ at level 2 is covered to $80\%$ by the images of the level-1 orbit under 30 maps $z\mapsto c+u(z-c)$, $u=\pm\varepsilon$, $c$ small lattice points, of which 9 have the same success rate $0.68$ as the chart at $0$.
- **Conjectured.** (R$^\flat$) with uniform constants and $\mathcal D$ the components of at least 5 states, together with a separate radius bound for children whose parents are dust (Conjecture 7.1); the region form of (R1) (Conjecture 7.2).

**The remaining gap.** (a) The global part of (R1): the local transport of edges (Theorems 3, 4, Lemma 6, Computation 3) shows that $\varepsilon$ is a graph morphism on edges inside a region, but (i) the region on which *all* edges transport is not described by circles: it is the cluster set $G$, and (ii) the images of one large parent component spread over one large child component and many small ones, so the plurality map is not forced by local lemmas. (b) (R2): a bound on the distance of every child component from the image components. It concerns child components everywhere in $D_1\cup D_2$, it has the same nature as (K), and the $\varepsilon$-chart at $0$ alone cannot give it (§5.4, §7). The data suggest an atlas of $\pm\varepsilon$-charts (§6.4); that is a direction, not a reduction.

Labels: **proved**, **computed** (with method), **conjecture**. "Rigorous" for a computation means that every decision has a stated margin far above the working precision.

---

## 1. Setting

As in the component-graph note §1 and the (T) note §1. Briefly: $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$; $E=\zeta-\zeta^2=(0,1,-1,0)$; $F=\varphi^{-1}E$; $\varepsilon=\varphi^{-3}=\sqrt5-2=(-3,0,-2,-2)$ and $\varepsilon^{-1}=\varphi^3=(1,0,-2,-2)$; letters $a,b$ rotate by $\zeta^{-1}$ about $-1,+1$ on the closed disks $D_1,D_2$ of radius $r$; $A,B$ are their inverses.

- **Tokens** $t_0,\dots,t_{11}$, in the order of the scratch programs: $w_1=AABAB$, $w_2=ababb$, $w_3=abaBAB$, $w_2^{-1}$, $w_1^{-1}$, $w_3^{-1}$, then their images under complex conjugation $\iota$ ($a\leftrightarrow a^{-1}$, $b\leftrightarrow b^{-1}$). Token $t$ acts at $X$ iff $X\in\operatorname{dom}_r(t)$, an intersection of disks of radius $r$ about its pull-back centres (Table 1.1 of the (T) note), and moves $X$ by its translation $\tau(t)$: $\tau(w_1)=\tau(w_2)=2\varphi^{-1}E$, $\tau(w_3)=-2\varphi^{-2}E$.
- **Pull-back centres of a word.** If the first $j-1$ letters have acted, letter $j$ acts iff $|X-c_j|\le r$ with $c_j=h_j^{-1}(p_j)$, $h_j$ the composite rotation and $p_j=\pm1$ the letter's centre. For words with lattice letters these are lattice points; they are computed exactly.
- **Transport words** (component-graph note, Computation 4.8, here verified exactly on every edge used): $W(w_1)=w_3^{-1}w_1^{-1}w_3^{-1}$, $W(w_2)=w_3^{-1}w_2^{-1}w_3^{-1}$, $W(w_3)=w_3^{-1}w_2^{-1}w_3^{-1}w_1^{-1}w_3^{-1}$, $W(t^{-1})=W(t)^{-1}$, $W(\iota t)=\iota W(t)$. Each $W(t)$ is a token path with translation $\varepsilon\,\tau(t)$ (exact check: $W(w_1)$ translates by $(-6,10,-10,6)=\varepsilon\cdot(2,-2,2,-2)$).
- **Parent, child, image, transport.** For a lattice orbit $O$ at $\delta$ the child is the orbit at $\varepsilon\delta$ of $\varepsilon\cdot$(seed). A parent state $y$ *has an image* if $\varepsilon y$ lies in the child. An edge $X\to m(X)$ of the lifted state graph ($m$ a token or a connector letter) *transports* if $\varepsilon X$ and $\varepsilon m(X)$ are joined at $\varepsilon\delta$ by a path with the same number of connectors as $m$ (0 or 1).
- **Graphs.** $\mathcal C(O)$ is the component graph (vertices: token components of lifted states; edges: connectors), $d_O$ its distance, $\operatorname{diam}$ its diameter, $D(\delta)$ the supremum of $\operatorname{diam}\mathcal C(O)$ over lattice orbits at $\delta$. *Large* components have $\delta\cdot$(internal extent)$\,>1$ (component-graph note §1).

## 2. Statements

### 2.1 What suffices

**Hypothesis (R$^0$) at $\delta$.** There are $N_0<\infty$ and a non-decreasing function $F:\mathbb N\to\mathbb N$ (both may depend on $\delta$) such that every lattice orbit $O'$ at $\varepsilon\delta$ with more than $N_0$ states has a lattice orbit $O$ at $\delta$ with $\operatorname{diam}\mathcal C(O')\le F(\operatorname{diam}\mathcal C(O))$.

**Hypothesis (R$^\flat$) at $\delta$.** There are $N_0,b,L,c<\infty$ (may depend on $\delta$) such that every lattice orbit $O'$ at $\varepsilon\delta$ with more than $N_0$ states has a lattice orbit $O$ at $\delta$, a set $\mathcal D$ of components of $O$ and a map $\kappa:\mathcal D\to\mathcal C(O')$ with
- (R1$^\flat$) $d_{O'}(\kappa K_1,\kappa K_2)\le L\,d_O(K_1,K_2)+c$ for $K_1,K_2\in\mathcal D$;
- (R2) every component of $O'$ is within $d_{O'}$-distance $b$ of $\kappa(\mathcal D)$.

(R) of the component-graph note is (R$^\flat$) with $L=1$, $c=0$ and constants independent of $\delta$.

**Theorem 1 (the weakest renormalization hypothesis).** Let $\delta_\ast>0$ be a defect at which $GG_5$ is finite.
1. (R) $\Rightarrow$ (R$^\flat$) $\Rightarrow$ (R$^0$), with $F(D)=LD+c+2b$.
2. If (R$^0$) holds at every $\delta\in(0,\delta_\ast/\varepsilon)$, then $D(\delta)<\infty$ for every $\delta>0$, and $GG_5(r)$ is finite for every $r<r_c$.
3. If moreover $F_\delta(D)\le D+C$ with $C$ and $N_0$ independent of $\delta$, then $D(\varepsilon^k\delta')\le\max(N_0,\ 5|GG_5(r_\ast)|)+kC$ for $\delta'\in[\delta_\ast,\delta_\ast/\varepsilon)$, $r_\ast^2=r_c^2-\delta_\ast$.

With $\delta_\ast=1/55$ the base case is the certified finiteness of `certificates.md`. **[proved, given the (T) note's Theorem 4 and Corollary 5(2), and `sharp-lower-bound-n5.md` Theorem 4.1]**

Item 2 says that no uniformity in $\delta$ is needed for the implication, because the chain $\delta'\to\varepsilon\delta'\to\dots\to\delta$ from a certified radius is finite. The converse is also immediate: if $D(\varepsilon\delta)<\infty$ then (R$^0$) holds at $\delta$ with $F\equiv D(\varepsilon\delta)$, and (R$^\flat$) with $\mathcal D$ one component and $b=D(\varepsilon\delta)$ (referee report of the component-graph note, main finding). So, given the base, (R$^0$) at all $\delta$ is equivalent to (B), and all content of a renormalization hypothesis lies in the uniformity of its constants (item 3) or in a proof of them from local structure. This note proves local structure (§2.2–2.3); it does not prove any uniform constant.

### 2.2 Tokens

**Lemma 2 (tangent disks).** Let $c,c'\in\mathbb C$ with $|c'-\varepsilon c|=(1-\varepsilon)r_c$. Then $\varepsilon D(c,r)\subseteq D(c',r')$ for every $\delta\in[0,r_c^2]$. **[proved]**

**Theorem 3 ($w_3$-type tokens).** Let $\delta\ge0$ (for $\delta>3\varphi-4\approx0.8541$ the domain $U_3(r)$ is empty, because its test disks about $(-1,2,-4,2)$ and $(-1,2,0,0)$, at squared distance $28-8\varphi$, are disjoint once $r^2<7-2\varphi$), and let $t$ be one of $w_3,w_3^{-1},\iota w_3,(\iota w_3)^{-1}$. For every $X\in\mathbb C$ at which $t$ acts at radius $r$, the word $W(t)$ acts at $\varepsilon X$ at radius $r'$, and $W(t)(\varepsilon X)=\varepsilon\,t(X)$. Equivalently, $\varepsilon\operatorname{dom}_r(t)\subseteq\operatorname{dom}_{r'}(W(t))$. **[proved, using Computation 4.1]**

For $w_3$ the 28 letter tests of $W(w_3)$ have 26 distinct pull-back centres $c'$. Twelve satisfy the tangency identity of Lemma 2 with a test centre $c$ of $w_3$; four of these touch $\varepsilon U_3(r_c)$, at the two corners $E$ and $-\varepsilon E$ of $U_3(r_c)$, and the other eight contain it with positive margin. The remaining 14 contain $\varepsilon U_3(r_c)$ with margin $r_c^2-\max|\varepsilon z-c'|^2\ge0.503017$ (Table 4.1).

**Theorem 4 ($w_1,w_2$-type tokens: the exact domain).** Let $0\le\delta\le2.79$ and $X\in U_1(r)$. Then $W(w_1)=w_3^{-1}w_1^{-1}w_3^{-1}$ acts at $\varepsilon X$ at radius $r'$ if and only if
$$|\varepsilon X-c_a|\le r'\quad\text{and}\quad|\varepsilon X-c_b|\le r',\qquad c_a=(1,-2,4,-2),\ c_b=(5,-8,10,-6),$$
equivalently $|X-\varphi^3c_a|\le\varphi^3r'$ and $|X-\varphi^3c_b|\le\varphi^3r'$, with $\varphi^3c_a=(1,6,6,4)\approx-5.2361+6.8819i$ and $\varphi^3c_b=(1,8,4,4)\approx-3+7.6085i$ (radius $\varphi^3r'\approx9.10$). For $w_2$ and $X\in U_2(r)$ the same holds for $W(w_2)$ with $c_a=(1,-2,0,0)$, $c_b=(5,-8,6,-4)$. For the other six tokens of this type the statement follows by $t\mapsto t^{-1}$ and $\iota$. **[proved, using Computation 4.1]**

Of the 16 distinct centres of $W(w_1)$, 4 are tangent (Lemma 2) at the corners $-F$ and $-\sqrt5E$ of $U_1(r_c)$, 10 contain $\varepsilon U_1(r_c)$ with margin at least $0.66034$, and $c_a,c_b$ are the two that cut: on $U_1(r_c)$ they are violated by up to $1.0557$ and $0.9605$, at the lowest corner $\approx-0.691-2.127i$ of $U_1(r_c)$.

**Corollary 5 (token edges near $0$).** Let $0<\delta\le\tfrac1{10}$. Every token edge $\{X,t(X)\}$ of $\mathcal T(r)$ with $|X|\le0.99$ and $|t(X)|\le0.99$ transports: $W(t)$ acts at $\varepsilon X$ and ends at $\varepsilon t(X)$. More precisely, for a $w_1$-type edge it suffices that the start point of the forward $w_1$, resp. backward $\iota$-image, lies in $|z|\le0.99$; for a $w_2$-type edge, the end point; for a $w_3$-type edge nothing. **[proved, using Computation 4.2]**

### 2.3 Connectors

**Lemma 6 (letter exchange).** Let $L,L'$ be letters with the same rotation $\zeta^{\mp1}$, about $p,p'\in\{\pm1\}$. Then $\varepsilon L\varepsilon^{-1}(z)=L'(z)+v$ for all $z$, with
$$v=(\varepsilon p-p')(1-\zeta^{\mp1})\in2(1-\zeta)\Lambda=\Lambda_T ,$$
the translation module of token paths (the (T) note §1). So the image of a connector edge is a path with one connector exactly when a token path with translation $v_1$, the letter $L'$ and a token path with translation $v_2$, $\zeta^{\mp1}v_1+v_2=v$, act in turn at $\varepsilon X$. **[proved]**

The lattice data say which: §5.1.

## 3. Proofs

### 3.1 Theorem 1

*Item 1.* (R)$\Rightarrow$(R$^\flat$) is trivial. Given (R$^\flat$), let $X',Y'$ be components of $O'$; choose $K_1,K_2\in\mathcal D$ with $d(X',\kappa K_1)\le b$, $d(Y',\kappa K_2)\le b$. Then $d(X',Y')\le2b+L\,d_O(K_1,K_2)+c\le2b+L\operatorname{diam}\mathcal C(O)+c$.

*Item 2.* Fix $\delta\in(0,\delta_\ast)$ and write $\delta=\varepsilon^k\delta'$ with $k\ge1$ and $\delta'\in[\delta_\ast,\delta_\ast/\varepsilon)$. Base: the radius at $\delta'$ is at most $r_\ast$, so by orbit monotonicity every lattice orbit at $\delta'$ lies in one at $\delta_\ast$, which has at most $|GG_5(r_\ast)|$ points and $5|GG_5(r_\ast)|$ lifted states; a graph has diameter less than its number of vertices, so $D(\delta')\le5|GG_5(r_\ast)|$. Step: if $D(\varepsilon^j\delta')<\infty$, then by (R$^0$) at $\varepsilon^j\delta'<\delta_\ast/\varepsilon$, every child orbit with more than $N_0$ states has diameter at most $F(D(\varepsilon^j\delta'))$ ($F$ non-decreasing), and the others less than $N_0$; so $D(\varepsilon^{j+1}\delta')\le\max(N_0,F(D(\varepsilon^j\delta')))<\infty$. After $k$ steps $D(\delta)<\infty$. For $\delta\ge\delta_\ast$, $D(\delta)\le5|GG_5(r_\ast)|$ by monotonicity. $D$ here is the supremum over lattice orbits, while Corollary 5(2) of the (T) note takes it over the orbits of all points of $\mathbb C$; at a non-norm radius every word map is realised at a lattice point (`sharp-lower-bound-n5.md` Theorem 4.1), so the argument of that corollary (with the (T) note's Theorem 4) runs with the lattice supremum and gives finiteness of $GG_5(r)$ at every non-norm radius, as in Proposition 1(3) of the component-graph note. Non-norm radii are dense, and group monotonicity (`boundary-contact.md` Theorem 3.4) gives every radius.

*Item 3.* The same induction with $F(D)\le D+C$: with $X=\max(N_0,5|GG_5(r_\ast)|)$, $D(\varepsilon^{j}\delta')\le X+jC$ gives $D(\varepsilon^{j+1}\delta')\le\max(N_0,X+(j+1)C)=X+(j+1)C$. (The form $\max(N_0,5|GG_5(r_\ast)|+kC)$ would fail if $N_0>5|GG_5(r_\ast)|$, because a parent may itself be a small orbit.) $\square$

### 3.2 Lemma 2

For $z\in D(c,r)$: $|\varepsilon z-c'|\le\varepsilon|z-c|+|\varepsilon c-c'|\le\varepsilon r+(1-\varepsilon)r_c$. The square root is concave, so
$$r'=\sqrt{(1-\varepsilon)r_c^2+\varepsilon r^2}\ \ge\ (1-\varepsilon)r_c+\varepsilon r ,$$
since $(1-\varepsilon)r_c^2+\varepsilon(r_c^2-\delta)=r_c^2-\varepsilon\delta=r'^2$. $\square$

At $\delta=0$ the two circles are internally tangent; at $\delta>0$ the inclusion is strict. This is the exact form of the first-order self-similarity at a tight corner $z_0$: the target test of $W(t)$ at $\varepsilon z_0$ and a test of $t$ at $z_0$ have Lagrange multipliers $(\varepsilon,0)$, so the defect $\delta$ at $z_0$ becomes exactly the defect $\varepsilon\delta$ at $\varepsilon z_0$.

### 3.3 Theorems 3 and 4

*Reduction by symmetry.* $\varepsilon$ is real, so it commutes with $\nu(z)=-z$ and with $\iota(z)=\bar z$. If $t$ acts at $X$ then $t^{-1}$ acts at $t(X)$, and $W(t)^{-1}$ acts at $W(t)(\varepsilon X)=\varepsilon t(X)$ iff $W(t)$ acts at $\varepsilon X$ (each disk is invariant under its letter's rotation). $\iota$ maps the system to itself with $a\leftrightarrow a^{-1}$, $b\leftrightarrow b^{-1}$ (invariant note, Proposition 3), so $\iota t$ acts at $\bar X$ iff $t$ acts at $X$, and likewise for $\iota W(t)$. So the twelve tokens reduce to $w_1,w_2,w_3$; Computation 4.1 treats all three directly.

*The containment.* $W(t)$ acts at $\varepsilon X$ iff $|\varepsilon X-c'|\le r'$ for each pull-back centre $c'$ of $W(t)$. Fix $c'$.
- If $c'$ is tangent to $\varepsilon D(c,r)$ for a test centre $c$ of $t$ (exact identity $|c'-\varepsilon c|^2=(1-\varepsilon)^2(3+\varphi)$ in $\mathbb Q(\sqrt5)$, Computation 4.1), then $\varepsilon\operatorname{dom}_r(t)\subseteq\varepsilon D(c,r)\subseteq D(c',r')$ by Lemma 2, for all $\delta\ge0$.
- Otherwise let $m=r_c^2-\max_{z\in\operatorname{dom}_{r_c}(t)}|\varepsilon z-c'|^2$. Since $\operatorname{dom}_r(t)\subseteq\operatorname{dom}_{r_c}(t)$, every $z\in\operatorname{dom}_r(t)$ has $|\varepsilon z-c'|^2\le r_c^2-m\le r'^2$ as soon as $\varepsilon\delta\le m$.

For Theorem 3 all centres are of the two first kinds. Twelve satisfy the tangency identity, including the two with the smallest margin $0.0381717$ (centres $(3,-4,6,-4)\leftarrow(-1,2,0,0)$ and $(7,-12,10,-6)\leftarrow(-1,2,-4,2)$); the other 14 have $\min m=0.503017$, so the containment holds for $\varepsilon\delta\le0.503017$, i.e. $\delta\le2.1308$, which includes every $\delta\le3\varphi-4$; beyond that $U_3(r)=\varnothing$. For Theorem 4 the centres other than $c_a,c_b$ are of the two first kinds with $\min m=0.66034$, valid for $\delta\le2.7972$; so $W(w_1)$ acts at $\varepsilon X$, $X\in U_1(r)$, iff the two remaining tests pass. The tests of $c_a,c_b$ are among those of the word, which gives "only if". $\square$

### 3.4 Corollary 5

For $w_1$: the region $U_1(r)\cap\{|z|\le0.99\}$ lies in $U_1(r_c)\cap\{|z|\le0.99\}$, on which $r_c^2-\max|\varepsilon z-c_a|^2=0.024973$ and $r_c^2-\max|\varepsilon z-c_b|^2=0.27229$ (Computation 4.2). For $\delta\le\tfrac1{10}$, $\varepsilon\delta\le0.023607<0.024973$, so both tests of Theorem 4 pass. For $w_2$: $\nu$ maps the $w_1$-edge $X\to X+\tau E$ to the $w_2$-edge $Y=-X-\tau E\to-X$, and $\nu\bigl(W(w_1)^{-1}\bigr)=(\nu w_3)(\nu w_1)(\nu w_3)=w_3^{-1}w_2^{-1}w_3^{-1}=W(w_2)$ as words ($\nu w_1=w_2^{-1}$, $\nu w_3=w_3^{-1}$, chaining note §1). So $W(w_2)$ acts at $\varepsilon Y$ when $|Y+\tau E|=|X|\le0.99$. Backward tokens and $\iota$-images as in §3.3; $w_3$-type edges by Theorem 3, which has no condition on $\delta$. $\square$

### 3.5 Lemma 6

$\varepsilon L\varepsilon^{-1}(z)=\varepsilon p+u(z-\varepsilon p)$ and $L'(z)=p'+u(z-p')$ with $u=\zeta^{\mp1}$, so the difference is $(\varepsilon p-p')(1-u)$. For $p,p'\in\{\pm1\}$, $\varepsilon p-p'\in\{\pm(\varepsilon-1),\pm(\varepsilon+1)\}=\{\pm2\varphi^{-2},\pm2\varphi^{-1}\}\subset2\mathbb Z[\varphi]\subset2\Lambda$, and $1-\zeta^{\mp1}$ is an associate of $1-\zeta$. So $v\in2(1-\zeta)\Lambda$, which is $\Lambda_T$ by the (T) note §1. Composition: $L'(z+v_1)+v_2=L'(z)+\zeta^{\mp1}v_1+v_2$. $\square$

---

## 4. Rigorous computations for §2.2

Method (as Computation 1.2 of the chaining note, refereed): the maximum of the convex function $|\varepsilon z-c'|^2$ over a compact intersection of disks is attained at an extreme point, hence on a boundary arc, hence at an arc end (a pairwise intersection of boundary circles lying in all disks) or at the point of a boundary circle farthest from $c'/\varepsilon$, if it lies in all disks. All candidates are enumerated in 50-digit arithmetic; a candidate is kept if it satisfies every disk inequality to within $10^{-40}$ (keeping slightly infeasible candidates can only enlarge the maximum). Every margin used in a proof exceeds the value it is compared with by at least $1.9\cdot10^{-4}$ (Theorem 3: $0.503017$ against $2.13\varepsilon=0.50282$; Corollary 5: $0.024973$ against $0.023607$), far above the precision. The referee re-derived every margin used in a proof by an independent branch-and-bound in exact rational interval arithmetic (referee report §3.1). Tangencies and corner memberships are exact identities in $\mathbb Q(\sqrt5)$ (exact arithmetic in $\mathbb Q(\zeta)$, §6).

### 4.1 The tests of the transport words over $\operatorname{dom}_{r_c}(t)$

**Table 4.1.** For each $t\in\{w_1,w_2,w_3\}$: the pull-back centres $c'$ of $W(t)$ (lattice coordinates), with the margin $m=r_c^2-\max_{\operatorname{dom}_{r_c}(t)}|\varepsilon z-c'|^2$, "tangent" (to $\varepsilon D(c,r)$, centre $c$ of $t$ given), or "cuts" (negative $m$).

| $t$ | tangent $c'$ ($\leftarrow c$) | cuts | margins of the others |
|---|---|---|---|
| $w_1$ | $(3,-6,4,-2)\leftarrow(-1,0,-2,2)$; $(3,-6,6,-2)\leftarrow(-1,0,0,2)$ [corner $-F$]; $(5,-6,6,-4)\leftarrow(-1,2,-2,2)$; $(5,-8,6,-4)\leftarrow(-1,0,-2,2)$ [corner $-\sqrt5E$] | $(1,-2,4,-2)$: $-1.0557$; $(5,-8,10,-6)$: $-0.9605$ | $2.0526, 0.66034, 3.0132, 3.0942, 1.5787, 4.0689^{\times3}, 1.5787, 3.0904$ |
| $w_2$ | $(1,-2,4,-2)\leftarrow(-1,2,0,0)$; $(1,-4,4,-2)\leftarrow(-1,0,0,0)$ [corner $E$]; $(3,-4,4,-4)\leftarrow(-1,2,-2,0)$; $(3,-4,6,-4)\leftarrow(-1,2,0,0)$ [corner $-F$] | $(1,-2,0,0)$: $-0.9605$; $(5,-8,6,-4)$: $-1.0557$ | $3.0904, 1.5787, 4.0689^{\times3}, 1.5787, 3.0942, 3.0132, 0.66034, 2.0526$ |
| $w_3$ | $(1,-2,4,-2)\leftarrow(-1,2,0,0)$; $(1,-4,4,-2)\leftarrow(-1,0,0,0)$ [corner $E$]; $(9,-12,12,-8)\leftarrow(-1,4,-4,2)$; $(9,-14,12,-8)\leftarrow(-1,2,-4,2)$ [corner $-\varepsilon E$] | none | 22 values, smallest $0.038172$ (twice), then $0.39885$; all listed in §6.5. Eight of the 22 also satisfy the tangency identity: $(3,-4,6,-4)$, $(7,-12,10,-6)$ ($0.038172$), $(3,-4,4,-4)$, $(7,-12,12,-6)$ ($0.39885$), $(1,-2,2,0)$, $(9,-14,14,-10)$ ($1.6702$), $(5,-6,6,-4)$, $(5,-10,10,-6)$ ($2.0526$); the smallest margin of the other 14 is $0.50302$ |

The tangent pairs satisfy $|c'-\varepsilon c|^2=(1-\varepsilon)^2(3+\varphi)$ exactly. At each tight corner $z_0$ the exact Karush–Kuhn–Tucker multipliers of the two tight tests of $t$ for the target $c'$ are $(\varepsilon,0)$ or $(0,\varepsilon)$, in $\mathbb Q(\sqrt5)$; their sum $\varepsilon$ is what makes the defect scale by exactly $\varepsilon$. **[computed, rigorous]**

### 4.2 The disk $|z|\le0.99$

Adding the constraint $|z|\le0.99$ to $U_1(r_c)$: margins $0.024973$ ($c_a$) and $0.27229$ ($c_b$). For comparison, with $|z|\le1$ they are $0.013174$ and $0.25993$, and with the half-plane $\operatorname{Im}z\ge-0.85$ instead, $0.033240$ and $0.28094$ (so Corollary 5 also holds with that half-plane, for $\delta\le0.1408$). The region of $U_1(r)$ where $W(w_1)$ fails starts at $|X|=1.0113$ ($\delta\to0$) to $1.0135$ ($\delta=0.1$), at $X\approx-0.49-0.88i$ on the circle about $\varphi^3c_a$ (nearest point, 50-digit arithmetic, not a rigorous bound). **[computed, rigorous for the three margins]**

## 5. Computations: connectors, the success region, births

### 5.1 Connector words (exact, orbit of $0$, levels $1\to2$)

For every connector edge $X\to L(X)$ between token components with both images present ($29\,128$ edges), a breadth-first search at level 2 over (state, connector used) found the shortest word "tokens, one letter, tokens" from $\varepsilon X$ to $\varepsilon L(X)$: length 3 (two tokens and one letter) for $29\,080$, length 6 for $24$, none of length $\le8$ for $24$. $22\,408$ connector edges have one image missing. The letter used is often not $L$ (Lemma 6): for example $A$ is realized by $w_2\,B\,w_3$ ($6\,542$ times, "$t_1Bt_2$"), and $a$ by $w_1^{-1}a\,\iota w_1$ ($6\,278$), $\iota w_2\,b\,\iota w_3$ ($493$) and others. Per letter 4–8 distinct words occur.

Geometry (double precision, grid step $0.003$): for $L=a$ there are 97 words with at most 3 tokens and the right map, of 13 distinct domains with at most 2 tokens; each domain is $\operatorname{dom}(a)$ cut by 2–5 circles of radius $\varphi^3r'$. On $\{|X|\le1,\ |a(X)|\le1\}$ their union covers $91.8\%$; the uncovered part is a lune with corners near $0.11+0.36i$, $0.31+0.95i$, $-0.33+0.95i$, inside the pentagonal gap above the centre of the orbit picture, and contains no point of the orbit of $0$ at level 1. On all of $\operatorname{dom}(a)$ the union covers $44\%$; the rest is where $a(X)$ leaves the success region. **[computed]**

### 5.2 Token edges (exact)

Orbit of $0$, $1\to2$, per token of type $w_1,w_2$: $2\,514$ edges where $W(t)$ acts at $\varepsilon X$ (both images then present, as they must be); $2\,142$ where it fails and an image is missing; $6$ where it fails with both images present. Those 6 are at the two corners of the failure region of Theorem 4 ($X\approx-0.63-0.97i$ and $X\approx-2.11-1.45i$), and the images are joined at level 2 by the token words $t_2t_0t_{10}t_{11}t_5t_3t_5t_5t_3t_7t_8$ (11 tokens) and $t_5t_{10}t_{11}t_5t_3t_5t_5t_3t_7t_8t_2t_0t_2$ (13 tokens). Per token of type $w_3$: $1\,035$ edges, $W(t)$ acts on all (Theorem 3). In double precision, the union of the domains of all 886 token words of length $\le5$ with translation $\varepsilon\tau(w_1)$ equals the domain of $W(w_1)$ on a grid of step $0.006$ in $U_1(r)$ ($\delta=\varepsilon/10$), and at 170 random points of $U_1(r)$ outside that domain no token path of length $\le9$ joins the images. **[computed]**

### 5.3 The success region

At $1\to2$ and $2\to3$ (orbit of $0$) the states without image form whole clusters of the orbit (the pentagonal rosettes of the orbit picture): those in two caps, the part of $D_1\cup D_2$ above roughly $\operatorname{Im}y=1$ near $\operatorname{Re}y=0$ widening to the circles at $|\operatorname{Re}y|\approx1.8$, and its mirror image. The boundary between success and failure runs through gaps between clusters, which is why the mixed cells of Computation 4.7 of the component-graph note thin out with the cell size. The failure region of Theorem 4 (two big circles cutting the bottom of $U_1$) covers the lower-left failure clusters and touches success clusters only at its two corners (5.2). The images $\varepsilon\cdot$(cap) lie in the pentagonal gaps of the child picture at $\pm0.55i$. **[computed; the description by "clusters" is read off plots and is not a definition]**

### 5.4 Births and the reverse direction

| pair | image components | born components | states in born components | largest born | born at distance 1 / 2 / 3 |
|---|---|---|---|---|---|
| orbit of $0$, $1\to2$ | 989 | 125 176 | 46.0% | 57 | 90 222 / 34 570 / 384 |
| orbit of $0$, $2\to3$ | 12 903 | 1 775 026 | 47.2% | 10 799 | 1 268 702 / 500 232 / 6 092 |

All components at distance 3 are single states; at $2\to3$, 32 born components with more than 100 states, all at distance 1. Child points near $0$ are not all images: of the level-2 points with $|y'|<0.7$, between $44\%$ and $96\%$ per annulus of width $0.02$ are $\varepsilon$-images of level-1 points (the pointwise reverse inclusion fails near $0$ too). **[computed]**

## 6. Computations: adversarial tests and charts

### 6.1 Random child orbits

For parent defects $\delta=p/D\in\{1/16,1/20,1/25,1/30,1/40,1/50,2/45,3/80\}$ (child $r'^2=(3D+3p+(D-2p)\varphi)/D$, parent $r^2=(3D-p+D\varphi)/D$): random *child* seeds (physical point uniform in $D_1\cup D_2$, internal point uniform in radius $25/(\varepsilon\delta)$), the child orbit, its point $y'$ of least modulus, the parent orbit of $\varepsilon^{-1}y'$ at $\delta$, and the transport statistics of the component-graph note's `kmap`. 410 child seeds; 248 child orbits with more than 40 states (155 to $1\,165\,681$ states); the 162 others have at most 40.

- Every child orbit with more than 40 states has $|y'|\le0.2217<\varepsilon=0.2361$, so $|\varepsilon^{-1}y'|<0.94$.
- Caveat: only the parent through the point nearest $0$ was used, and image lookup accepts any lift of $\varepsilon y$ (not the sheet-preserving lift $(y,j)\mapsto(\varepsilon y,j)$ of the referee report). Pairs whose parent has no large component count as "no violation" vacuously; the referee's counterexamples to Conjecture 5.1 are of this kind, and this test does not see them.
- $\kappa$ = plurality on large components: 0 violations of (R1) on all 248 pairs; connector edges between large components with both images map to distance $\le1$; large births within 1 of $\kappa(\mathcal D)$; every child component within 3 of a component containing an image.
- Token edges with both images present: in one same child component on 247 pairs; the exception is 6.2.

### 6.2 A token edge that splits

$\delta=1/16$ (parent $r^2=(47+16\varphi)/16$, child $r'^2=(51+14\varphi)/16$). Child seed $(-711,387,-680,-51)$, child orbit 665 states; parent seed $(250,102,91,257)$, parent orbit 40 states. The token $\iota w_2=ABABB$ maps $X=(167,-93,160,11)\approx-0.0805-0.8683i$ to $Y=(171,-91,160,15)\approx1.3015-1.3173i$. Both $\varepsilon X$ and $\varepsilon Y$ lie in the child orbit, in token components of 46 and 3 states, and no token path of any length joins them (search to depth 200). Here $|Y|=1.85$, so Corollary 5 does not apply: the relevant endpoint for $\iota w_2$ is $Y$. With $\kappa$ on all 20 parent components, (R1) holds on this pair. **[computed, exact]**

### 6.3 $\kappa$ on all components

Rerunning the 172 pairs with child orbits of at most $3\cdot10^5$ states, with $\mathcal D$ = all parent components that have an image and $\kappa$ the plurality map: (R1) fails on $34\,764$ of $3.7\cdot10^7$ ordered pairs at $\delta=1/16$, and on $0.048\%$–$0.072\%$ at the other radii; every failure has $d_{O'}(\kappa K_1,\kappa K_2)=d_O(K_1,K_2)+2$ with $d_O\in\{1,2\}$. So (R1$^\flat$) holds on all pairs with $L=1$, $c=2$; (R1) with $c=0$ needs the restriction to large components. **[computed, exact]**

### 6.4 Charts other than $0$

Orbit of $0$, level 1 to level 2: for each of 670 maps $z\mapsto c+u(z-c)$, $u=\pm\varepsilon$, $c$ a lattice point with coefficients in $[-2,2]$ and $|c|<2.6$, the fraction of level-1 points mapped into the level-2 orbit, and a greedy cover of the level-2 states. Nine charts have success $0.677$–$0.680$ (among them $c=-F$, $\pm\bar E$-type points and $c=\pm1.176i$, mostly with $u=-\varepsilon$); 30 charts cover $80.0\%$ of the level-2 states, the chart at $0$ adding only $1.6\%$ after the first 16. **[computed, exact memberships]**

### 6.5 Reproduction

Throwaway programs in the session scratch folder, not committed; described so that they can be re-implemented.
- *Exact arithmetic* as in the component-graph note §6 (integer 4-vectors, disk tests as signs in $\mathbb Z[\varphi]$, lifted orbits, union-find token components). `tw` (token edges: exact letter-by-letter test of $W(t)$ at $\varepsilon X$ at the child radius, endpoint check, breadth-first token paths between images), `cw` (connector edges: breadth-first search over (state, connector used)), `kmapb` (the component-graph note's `kmap` with born-component statistics), `kmapall` (`kmap` with every component counted as large), `near0`, `adv.sh`, `allk.sh` (6.1–6.3, generator seeds 101–103, 201–206), `charts` (6.4), `rev` (5.4).
- *Geometry*: `qz.py` (exact $\mathbb Q(\zeta)$ and $\mathbb Q(\sqrt5)$; pull-back centres; tangency identities; Karush–Kuhn–Tucker multipliers by $2\times2$ solves with exact verification), `rig.py`, `rig2.py`, `tang.py` (Table 4.1 and §4.2, `mpmath` at 50 digits), `wenum.py`, `cover.py`, `cover2.py`, `alt1.py` (word enumeration and coverage in double precision). The 22 non-tangent margins for $w_3$: $3.4891, 0.50302, 1.6702, 4.1714, 4.4458, 0.39885, 0.038172, 4.0689, 2.0526, 0.66034, 3.2288, 3.2288, 0.66034, 2.0526, 4.0689, 0.038172, 0.39885, 4.4458, 4.1714, 1.6702, 0.50302, 3.4891$.

## 7. Conjectures, and why the gap is not finite as it stands

**Conjecture 7.1 (repaired form, after the referee of the component-graph note).** For every $\delta\in(0,1/(55\varepsilon))$ and every lattice orbit $O'$ at $\varepsilon\delta$ with more than $N_0=40$ states: either some parent orbit $O$ at $\delta$ (orbit of $\varepsilon^{-1}x$, $x\in O'$) has a component of at least 5 states, and then (R$^\flat$) holds with $\mathcal D$ its components of at least 5 states, $\kappa$ the plurality map, $L=1$, $c=0$, $b=4$; or all parents are dust, and then $\mathcal C(O')$ has radius at most 4. **[conjecture]** The version with $\mathcal D$ = large components (Conjecture 5.1 of the component-graph note) is false (its referee report §4). With $\mathcal D$ all components with an image, (R1) fails but (R1$^\flat$) with $c=2$ held on the 172 pairs of §6.3. Evidence for the repaired form: the referee's six pairs; the pairs of §6.1 were not run with the threshold 5. The second alternative is a uniform radius bound, the old difficulty (K) restricted to orbits with dust parents.

**Conjecture 7.2 (region form of (R1)).** There is a closed set $G\subset D_1\cup D_2$, a finite union of regions bounded by circular arcs and independent of $\delta$, with $|y|\le1$ in $G$, such that for $0<\delta\le\delta_0$ every edge of the lifted state graph with both endpoints in $G$ transports, by one of finitely many explicit words. **[conjecture]** Corollary 5 is the token part on $|y|\le0.99$; the data (5.1–5.3) suggest that $G$ is a union of clusters whose boundary runs through the gaps of the orbit, with finitely many corner exceptions needing longer words (5.2).

*Why (R1) does not follow from local lemmas.* Even with Conjecture 7.2, (R1) needs that the parent's shortest paths between large components can be chosen with edges in $G$, and that the image of a large component is concentrated in one child component. Neither is local: the images of each large component of the orbit of $0$ at level 1 lie $96\%$ in one large child component and the rest in child components of 1 to 46 states (component-graph note's `kmap`, per-component output), and the 6.2 example shows that edges near the boundary of $G$ can split.

*Why (R2) is not a finite problem in this form* (the referee of the component-graph note reaches the same conclusion, adding that a 40-state parent can have a child of 252 725 states). All $\varepsilon$-images lie in $|y|<0.75$ (they are $\varepsilon$ times points of $D_1\cup D_2$), so every child component outside that disk is born, and (R2) asserts that each of them is within $b$ connectors of a component reaching into the disk. That is a bound on the depth of the child's component graph relative to a set defined near $0$, of the same kind as (K) itself. A proof would need control of the child dynamics everywhere. Computation 6.4 suggests the natural object: an atlas of $\pm\varepsilon$-charts at finitely many centres whose images cover the child orbit up to dust, each with its own local transport lemmas, plus bounded connector distances between overlapping charts. That would make (R2) a finite list of local statements of the kind proved in §2.2. It is not attempted here. The alternative of bypassing parents, a direct bound "every state is within $b$ connectors of a hub", is the uniform radius form of (K): the tube statement (every state within 4 connectors of the tube $|d|\le\delta$, component-graph note Computation 4.4) would reduce it to "every tube state is within bounded distance of a hub", but no fence-type argument for connectors is known (the (T) note §2.4 explains why the fence does not transfer). So that route is the old difficulty, not a new reduction.

## 8. Assessment

- **Formulation: settled, with a caveat** (Theorem 1). Any recursion $D(\varepsilon\delta)\le F_\delta(D(\delta))$ suffices for (B), but with $\delta$-dependent constants it is equivalent to (B); the target is a uniform additive recursion ($D=O(\log1/\delta)$ suffices) or a radius bound. Conjecture 5.1 of the component-graph note is false as stated; Conjecture 7.1 is the repaired form.
- **(R1) for token edges, local: closed** for $w_3$-type tokens everywhere (Theorem 3) and for $w_1,w_2$-type tokens with an exact two-circle description of where the transport word acts (Theorem 4), with an explicit sufficient region (Corollary 5). The method (tangent disks at tight corners plus margins) is uniform in $\delta$ and needs no lune analysis.
- **(R1) for connector edges: computed, not proved.** The words are known (2 tokens and one letter, letter exchange allowed by Lemma 6), and their union covers the relevant region except inside an orbit-free gap; a covering proof needs a cell decomposition of each letter's domain.
- **(R1) global and (R2): open, and not reduced.** The claim that token edges with both images present never split is false (6.2), though harmless for (R1) on large components. (R2) concerns the whole child orbit and needs more than the chart at $0$.
- **Overall: repairable, not closed.** The renormalization of the component graph by $\varepsilon$ at $0$ is confirmed in all 365 tested pairs, and its local mechanism is now proved for tokens. What remains is global, and the most promising route I see is a multi-chart renormalization (§6.4), which would replace the single global map $\kappa$ by finitely many local ones.
