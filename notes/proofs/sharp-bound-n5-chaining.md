# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: the free-token cut-off, the one-line window map, and two-dimensional token components

Authors: Eric Vergo, Claude

**Review.** Independently refereed: [`referee-report-sharp-bound-n5-chaining.md`](referee-report-sharp-bound-n5-chaining.md). Verdict: Lemma 1.1, Theorem 1, Proposition 2 and Proposition 6 correct (Lemma 1.1 and Theorem 1 after minor fixes: a margin overstated, the case $|h|>0.15$ of Theorem 1(1) made explicit); Computation 1.2 re-derived independently in 80-digit arithmetic, every table entry confirmed; Computations 3(2), 4 (all eleven rows) and 5 reproduced with an independent exact program. Computation 3(1) was corrected: words that minimize the number of connectors do *not* need dozens of alternations (one with 2 connectors and 2 runs reaches the level-2 extreme state). The evidence for (K) is the diameter of the component graph (exactly 6 to 9 where computed), not the eccentricity $e$. It continues [`sharp-bound-n5-invariant.md`](sharp-bound-n5-invariant.md) ("line 4", refereed), whose Theorem 7, Lemma 5, Conjecture B$^\ast$ and Corollary 11 are cited with that numbering, and uses [`sharp-bound-n5-orbit-of-zero.md`](sharp-bound-n5-orbit-of-zero.md) (refereed) only for comparison.

**What is established and what is not.** Let $r_c=\sqrt{3+\varphi}$ and $\delta=r_c^2-r^2$. **(B), finiteness of $GG_5(r)$ for every $r<r_c$, is not proved here; it remains open.** The aim of this round was to bound the chaining of chord runs (Conjecture B$^\ast$ of line 4) through a first-return map to the breakpoint windows. What the note establishes:

1. **Proved: the free-token cut-off on every chord-parallel line** (Theorem 1). On a line at offset $h$ from $\mathbb RE$, let the three chord tokens act wherever their disk tests pass, at any position (also outside $[-1,1)$ and where the token domains overlap), forwards or backwards. Every connected piece of this walk visits fewer than $\varphi^3/\delta_h+1/\sqrt5$ positions modulo the golden rotation, with $\delta_h=\min(\delta+h^2,\tfrac15)$, and changes the internal coordinate by less than $36.035/\delta_h+8.58$. On lines with $|h|\ge0.15$ a piece visits at most 8 positions. The same holds on lines parallel to $\mathbb R\bar E$. This removes the "token assigned by $T$" hypothesis of line 4's Theorem 7 (suggestion S1 of its referee). The input is a finite computation of the extents of the three token domains (Computation 1.2).
2. **Proved: the one-line window map is exactly self-similar** (Proposition 2). In the coordinate $u=(s-b^\ast)/\delta$, the first return of the golden rotation to a window $b^\ast+\delta W$ satisfies $R_{\varepsilon\delta}=R_\delta^{-1}$ and $R_{\varepsilon^2\delta}=R_\delta$ exactly ($\varepsilon=\varphi^{-3}$), and the rescaled internal displacement changes sign under $\delta\mapsto\varepsilon\delta$. This is the one-line form of the sign flip $\sigma(\varepsilon)<0$: period one for the return relation, period two for the return map.
3. **Computed (exact orbits): the window first-return map is not the dynamics.** The chord tokens of the two lines $\mathbb RE$ and $\mathbb R\bar E$ act together on two-dimensional regions. Token components mix the two line classes, and switching lines without a connector saves connectors. (Words that minimize the number of connectors need not alternate many times, though: among them, the fewest single-line runs needed is at most 11 at level 2, over all states.) The non-token letters that join large token pieces occur at about as many places as the orbit has points, all over the disks, not in $O(\delta)$-windows at finitely many points (Computation 3). So the first-return map $F_\delta$ to finitely many breakpoint windows that suggestion S2 asks for does not describe the orbit. The finite object is instead the **token-component graph** (§2.3).
4. **Computed (exact orbits, 11 orbits at 10 radii, plus random token components at 11 radii): the token-component structure is self-similar.** Every orbit computed consists of between 11 and 23 large token components and a mass of components with one or two points. The largest component has $\delta\cdot(\text{internal extent})$ equal to $15.64,\ 15.73,\ 15.75$ (orbit of $0$, levels 1–3), $23.13,\ 23.63,\ 23.65$ ($\delta=1/55,\ \varphi^{-3}/55,\ \varphi^{-6}/55$) and $32.25,\ 33.49,\ 33.51$ ($1/30$ and its two renormalizations). Every state of an orbit is reached from the seed with at most 3 to 7 non-token letters, and the diameter of the component graph is 6 to 9 (exact on six orbits, lower bounds 8 or 9 on the other five; Computation 4). Over 134 000 random lattice seeds at 11 radii, no token component has $\delta\cdot(\text{internal extent})$ above $34.3$.
5. **Computed (S4): the renormalized chain at $\delta=\varphi^{-6}/55$.** Multiplying a point of the $\delta=1/55$ witness orbit by the unit $\varepsilon$, twice, gives orbits at $\varphi^{-3}/55$ and $\varphi^{-6}/55$ with $1\,448\,901$ and $20\,057\,921$ points and $\delta M\ge22.26$ and $22.27$, against $22.24$ at $1/55$. The extreme word at $\varphi^{-6}/55$ has 6 runs. Its run lengths are those of the $1/55$ word in reverse order, multiplied by $\varphi^6$ (Computation 5).
6. **Conjectured: Conjecture B$^\sharp$**, which replaces B$^\ast$. (T) every token component has internal diameter at most $C_T/\delta$, and (K) every word map is realized by a word with at most $K_0$ non-token letters. B$^\sharp$ implies Conjecture A for small $\delta$ and hence (B) (Proposition 6). Theorem 1 is (T) for components confined to one line. The data support (T) and (K). They do not support the literal form of B$^\ast$ for *every* word map: the least number of single-line runs plus connectors needed to reach every state grows, from 6 to 9, 11 and 12 over levels 0–3 for the orbit of $0$ (Computation 4(5)).

**The remaining gap.** Two statements, uniform in $\delta$:
- (T), a two-dimensional cut-off for walks that mix the tokens of $\mathbb RE$ and $\mathbb R\bar E$. Theorem 1 handles one line. Mixed walks can go around the blocked window, because the window moves with the offset and the other line's tokens change the offset.
- (K), bounded chaining of token components by connector letters.

Neither is proved. The breakpoint-window formulation of the chaining (S2(b)–(c)) is the wrong object, because the walks between windows are two-dimensional; §5 says what replaces it.

Labels: **proved** (argument written here, with finite computations stated and reproducible), **computed** (exact orbit arithmetic in $\mathbb Z[\zeta]$ unless "double precision" is said; method in §6), **conjecture**.

---

## 1. Setting and definitions

As in line 4 §1. In brief: $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$, $\varphi=(1+\sqrt5)/2$, $\sigma\colon\zeta\mapsto\zeta^2$, $\varepsilon=\varphi^{-3}=2\varphi-3$ with $\sigma(\varepsilon)=-\varphi^3$, $H(x)=\sigma(x)-x$ on $\mathbb Q(\varphi)$. $D_1,D_2$ are the closed disks of radius $r$ about $\mp1$, $a,b$ the piecewise rotations; $A,B$ inside words mean $a^{-1},b^{-1}$. $E=\zeta-\zeta^2$, $|E|^2=3-\varphi$, $|\sigma E|=1.902113$, $N=iE/|E|$, $F=\varphi^{-1}E$, $b^\ast=-\varphi^{-1}$. Every $X\in\mathbb C$ is $X=sE+hN$ with $s,h$ real ($h$ is the offset from $\mathbb RE$).

- **Tokens.** $w_1=AABAB$, $w_2=ababb$, $w_3=abaBAB$ translate by $\tau_iE$, $\tau_1=\tau_2=2\varphi^{-1}$, $\tau_3=-2\varphi^{-2}=2\varphi^{-1}-2$, wherever every letter acts as its global rotation. A token *acts* at $X$ when this happens. The *domain* $U_i(r)$ is the set where $w_i$ acts. It is the intersection of the closed disks of radius $r$ about the test centres $P_{i1},\dots$ of line 4 §1, so $U_i(r)\subseteq U_i(r_c)$. The twelve chord tokens are $g\cdot w_i$, $g\in\{\mathrm{id},\nu,\iota,\iota\nu\}$. As words, $\nu\cdot w_1=w_2^{-1}$, $\nu\cdot w_2=w_1^{-1}$ and $\nu\cdot w_3=w_3^{-1}$. A word $w^{-1}$ acts at $X$ exactly when $w$ acts at $w^{-1}(X)$, letter by letter, because each disk is invariant under its rotation. So the class-$\nu$ tokens on $\mathbb RE$ are the backward steps of the class-$\mathrm{id}$ tokens, and the classes $\iota,\iota\nu$ do the same on lines parallel to $\mathbb R\bar E$.
- **Window functional.** $u=(0,1,1,-1)$, $P=(-1,0,-2,2)$ and $P'=(-1,2,0,0)$ (line 4, Lemma 5). Put $\ell(X)=2\operatorname{Re}\bigl(\bar u(X+F)\bigr)$. In strip coordinates $\ell=\sqrt5(s-b^\ast)+\gamma h$ with $\gamma=3\varphi-1$, and with $\Delta=X+F$,
$$|X-P|^2=r_c^2+\ell+|\Delta|^2,\qquad |X-P'|^2=r_c^2-\ell+|\Delta|^2,\qquad |\Delta|^2=(3-\varphi)(s-b^\ast)^2+h^2\tag{1.1}$$
  (line 4, Lemma 5 and its proof, refereed).
- **Line graph.** For $h\in\mathbb R$ let $\Gamma_h(r)$ be the graph on the points of the line $L_h=\{sE+hN\}$ with an edge $X\sim X+\tau_iE$ whenever $w_i$ acts at $X$ at radius $r$ ($i=1,2,3$). A path in $\Gamma_h(r)$ is a *free-token walk*: tokens of the classes $\mathrm{id}$ and $\nu$, in any order, wherever they act. Fix $X_0=s_0E+hN$. Every vertex $X$ of its component has $s-s_0\in2\mathbb Z[\varphi]$, and $s-s_0=2k\varphi^{-1}-2m$ for unique integers $k,m$. The integer $k=k(X)$ is the *index*. Every edge changes it by $\pm1$, and $s\equiv s_0+2k\varphi^{-1}\pmod2$.
- **Token graph and token components.** $\mathcal T(r)$ is the graph on $\mathbb C$ with an edge $X\sim g\cdot w_i(X)$ for each of the twelve tokens acting at $X$. Its components are the *token components*. Along a token path the word map is a translation. The *internal diameter* of a component $K$ is $\sup|\sigma t|$ over the translations $t$ of token paths inside $K$. For lattice points it is the diameter of $\{\sigma y:y\in K\}$, taken in the lifted state space of line 4, Computation 9.
- **Connector letters, component graph.** A *connector* is a single letter $a^{\pm1},b^{\pm1}$ that moves its point. The *component graph* of an orbit has the token components inside the orbit as vertices and an edge for each connector between two of them.

## 2. Statements

### 2.1 The free-token cut-off

**Lemma 1.1 (blocked arcs at every offset).** Let $r\le r_c$, $h\in\mathbb R$, and $\delta_h=\min(\delta+h^2,\tfrac15)$. Let $\mathcal B_h(r)\subseteq\mathbb R/2\mathbb Z$ be the set of $x$ such that no $w_i$ acts at $sE+hN$ for any $s\equiv x\pmod 2$. Then:
1. if $|h|\le0.15$ and $\delta_h>0$, $\mathcal B_h(r)$ contains the open arc $\{s\bmod2:\ |\sqrt5(s-b^\ast)+\gamma h|<\delta_h\}$, of length $2\delta_h/\sqrt5$;
2. if $h\ge0.15$, $\mathcal B_h(r)$ contains the arc $(1.04189,\ 1.36296)\bmod2$; if $h\le-0.15$, it contains $(-0.59903,\ -0.27796)\bmod2$. Both have length $0.32107>2\cdot\tfrac15/\sqrt5$;
3. if $|h|>1.81$, $\mathcal B_h(r)$ is the whole circle.

**[proved, using Computation 1.2]**

**Computation 1.2 (extents of the token domains at $r_c$).** The test centres are exact lattice points (line 4 §1), and $U_i(r_c)$ is an intersection of five or six disks of radius $r_c$. The extremes over $U_i(r_c)\cap\{h_{\rm lo}\le h\le h_{\rm hi}\}$ of the linear functions $\ell$, $s$ and $h$ were found by enumerating the candidate extreme points: the extreme point of each disk in the given direction, the pairwise intersections of the boundary circles, and the intersections of the circles with the lines $h=h_{\rm lo},h_{\rm hi}$. Each candidate was tested for membership in all disks and in the band, in 60-digit arithmetic. Values (rounded outward in the last digit):

| domain | $h$-range | $s$-range | $\ell$ on $\lvert h\rvert\le0.15$ | $s$ on $h\ge0.15$ | $s$ on $h\le-0.15$ |
|---|---|---|---|---|---|
| $U_1(r_c)$ | $[-1.80902,\ 0.22192]$ | $[-2.25507,\ -0.59903]$ | $[-4.22743,\ 0]$ | $[-1.89599,\ -0.95811]$ | $[-2.25507,\ -0.59903]$ |
| $U_2(r_c)$ | $[-0.22192,\ 1.80902]$ | $[-0.63704,\ 1.01900]$ | $[0,\ 4.22743]$ | $[-0.63704,\ 1.01900]$ | $[-0.27796,\ 0.65992]$ |
| $U_3(r_c)$ | $[-0.22192,\ 0.22192]$ | $[-0.25057,\ 1.01450]$ | $[0.24471,\ 4.22743]$ | $[0.10401,\ 1.01450]$ | $[-0.25057,\ 0.65992]$ |

Over all of $U_1\cup U_2\cup U_3$, $|\ell|\le8.47214$. The bounds $\ell\le0$ on $U_1(r_c)$ and $\ell\ge0$ on $U_2(r_c)$ are exact: by (1.1), $U_1(r_c)\subseteq D(P,r_c)=\{\ell+|\Delta|^2\le0\}$, and $U_2(r_c)\subseteq\{-\ell+|\Delta|^2\le0\}$. The decisions in the proof of Lemma 1.1 have margins of at least $0.044$ (the two smallest are $0.24471-\tfrac15$ and $(2\sqrt5-\tfrac15)-4.22743$, both $0.0447$), so 60-digit arithmetic settles them. **[computed; rigorous enumeration, §6]**

**Theorem 1 (free-token cut-off).** Let $r\le r_c$ and $h\in\mathbb R$ with $\delta_h=\min(\delta+h^2,\tfrac15)>0$. Let $j$ be the least integer with $\varphi^{-(j-2)}<\delta_h/\sqrt5$. Then for every component $K$ of $\Gamma_h(r)$:
1. the index takes at most $F_j$ values on $K$, and $F_j<\varphi^3/\delta_h+1/\sqrt5=4.2361/\delta_h+0.4473$;
2. if $|h|\ge0.15$, the index takes at most $F_6=8$ values on $K$;
3. every word map along a path in $K$ is a translation $tE$ with $|\sigma(tE)|<36.035/\delta_h+8.58$;
4. the same holds on every line parallel to $\mathbb R\bar E$, for the tokens of the classes $\iota,\iota\nu$.

In particular, for $0<\delta\le\tfrac15$ every free-token walk on one line has fewer than $\varphi^3/\delta+0.45$ index values and internal translation below $36.035/\delta+8.58$, at every offset. At $r=r_c$, every free-token walk on a line at offset $h\neq0$ visits fewer than $4.2361/\min(h^2,\tfrac15)+0.45$ index values. **[proved]**

Compared with line 4: Theorem 7 there needs the tokens assigned by $T$ and positions in $[-1,1)$, and gives $5.86/\delta$ steps. The constant $\varphi^3$ is that of Theorem 11 of `sharp-bound-n5-orbit-of-zero.md`, also proved there only for $T$-assigned passages. Theorem 1 needs no assignment and no range of positions.

**Remark (computed, double precision).** At offset $h$ the true gap between the domains of $w_1$ and $w_2$ near $b^\ast$ has width $2\delta/\sqrt5+O(\delta^2)$ at $h=0$, and for $\delta\lesssim|h|\ll1$ it fits $\tfrac85|h|+(\tfrac15+\tfrac1{\sqrt5})\delta$ to first order (for example $0.0169$ computed against $0.0167$ at $\delta=10^{-3}$, $h=0.01$). The reason is that the third letters of $w_1$ and $w_2$ are also tight at $-F$ (`sharp-bound-n5-critical-orbits.md` Table 2.1), so the two domains are wedges with their corner at $-F$. So the $h^2$ in $\delta_h$ is not sharp. With a proof of the linear gap, runs at offset $h$ would have length $O(1/\max(\delta,|h|))$, the scale behaviour that Conjecture K2 of that note predicts.

### 2.2 The one-line window map

Fix a bounded open interval $W\subseteq\mathbb R$ (for the part $|\ell|<\delta$ of the window of Lemma 1.1(1), $W=\{v:|\sqrt5v+\gamma\eta|<1\}$ with $\eta=h/\delta$). For $\delta>0$ with $\delta\,|W|<\tfrac12$, consider the arc $J_\delta=b^\ast+\delta W\pmod 2$ and the rotation $\rho(x)=x+2\varphi^{-1}\pmod 2$, which is the action of every forward token step on positions modulo 2. For $v\in W$ the first return of $\rho$ to $J_\delta$ is $\rho^{n}(b^\ast+\delta v)=b^\ast+\delta R_\delta(v)\pmod 2$, with $R_\delta(v)=v+\xi/\delta$, $\xi=\xi_\delta(v)\in2\mathbb Z[\varphi]$, and return time $n=n(\xi)=-H(\xi)/(2\sqrt5)\ge1$. The first backward return is $R_\delta^{-1}$, with displacement $\xi^-_\delta(v)$ and $n(\xi^-)\le-1$. On a line where $J_\delta$ is the blocked window, $\xi E$ is the translation of the free run from one window visit to the next, and $\sigma(\xi)\sigma E$ is its internal translation.

**Proposition 2 (exact self-similarity of the one-line return map).** For every $v\in W$:
1. $R_{\varepsilon\delta}(v)=R_\delta^{-1}(v)$, with $\xi_{\varepsilon\delta}(v)=\varepsilon\,\xi^-_\delta(v)$ and $n(\xi_{\varepsilon\delta}(v))=-\varphi^3n(\xi^-_\delta(v))+\xi^-_\delta(v)$;
2. the rescaled internal displacements satisfy $\varepsilon\delta\,\sigma(\xi_{\varepsilon\delta}(v))=-\delta\,\sigma(\xi^-_\delta(v))$;
3. hence $R_{\varepsilon^2\delta}=R_\delta$, with equal rescaled internal displacements.

So, as an undirected relation with rescaled internal translations up to sign, the one-line return structure is the same at $\delta$ and at $\varepsilon\delta$. As a map it has period two. **[proved]** (Checked numerically for random $v$: return times $144\to610=\varphi^3\cdot144$ under $\varepsilon$ and $89\to1597$ under $\varepsilon^2$.)

What Proposition 2 does not cover:
- the deviation of the true window from $b^\ast+\delta W$. By (1.1) it is of relative size $O(\delta(1+\eta^2))$, and the third-letter tests of the Remark add a further piece of the boundary. These are the one-line lunes: the points whose rotation orbit enters the band between the true and the linear window boundary. They have measure $O(\delta)$ per return but are not excluded;
- everything off one line (§2.3).

### 2.3 Token components (computed)

**Computation 3 (the window picture fails).** Exact lifted orbits; the words are minimal for the stated cost (§6).
1. *Mixed token walks.* At level 2 ($\delta=\varepsilon^2/10$), the orbit of $0$ has a state of largest internal modulus ($1\,165.00$) that is reached with 2 connector letters. One such word, found by breadth-first search, has about 55 token runs alternating between $\mathbb RE$ and $\mathbb R\bar E$ with no connector between consecutive runs. That many alternations are not needed: the least number of single-line runs among words with the least number of connectors is 2 for this state, and at most 11 for every state of the orbit (referee, lexicographic search). The alternations do matter for the connector count: if a switch of line class is allowed only after a connector, the largest number of connectors needed rises from $3,4,5$ to $4,6,8$ (levels 0–2) and from 6 to 10 ($1/55$). Tokens of both line classes act at many points far from both lines (more than half of such points in large components have distance above $0.6$ from $\mathbb RE$ or from $\mathbb R\bar E$), because the domains $U_i$ are two-dimensional regions of height up to $1.8$ (Computation 1.2), not thin strips.
2. *Connectors are everywhere.* At level 1 there are $26\,536$ connector edges between token components with at least 100 points (orbit: $30\,165$ points); at level 2 there are $350\,308$ between components with at least $1\,000$ points (orbit: $400\,519$ points). They are spread over the disks: binned by the letter and a grid cell of side $0.1$, the most populated bin holds 39, resp. 474, of them.

So the dynamics between window visits is a two-dimensional token walk. A first-return map to $O(\delta)$-neighbourhoods of finitely many breakpoint points does not capture it, because the large pieces of the orbit touch each other along their whole extent.

**Computation 4 (the token-component structure across levels).** For each orbit: the number of states, $\delta M$ (the diameter of $V$, line 4 Computation 9, compared exactly), the number of token components with $\delta\cdot(\text{internal extent})>1$, the largest $\delta\cdot(\text{internal extent})$ of a component, the eccentricity $e$ of the seed's component in the component graph (equal to the least number of connectors with which every state is reached), a lower bound $D$ for the diameter of the component graph (from three breadth-first sweeps), and $P$, the least number of pieces (single-line runs plus connectors) with which every state is reached. "Internal extent" is the diagonal of the bounding box of the component's part of $V=\{\zeta^{-2j}\sigma y\}$, which is between the internal diameter and $\sqrt2$ times it (double precision from exact points).

| $\delta$ | seed | states | $\delta M$ | large comps | top $\delta\cdot$extent | $e$ | $D\ge$ | $P$ |
|---|---|---|---|---|---|---|---|---|
| $1/10$ (level 0) | $0$ | 1 433 | — | 19 | 11.39 | 3 | 5 | 6 |
| $\varepsilon/10$ (level 1) | $0$ | 30 165 | — | 23 | 15.64 | 4 | 6 | 9 |
| $\varepsilon^2/10$ (level 2) | $0$ | 400 519 | — | 11 | 15.73 | 5 | 7 | 11 |
| $\varepsilon^3/10$ (level 3) | $0$ | 5 673 561 | — | 15 | 15.75 | 5 | 7 | 12 |
| $1/55$ | $(470,202,166,493)$ | 111 107 | 22.24 | 15 | 23.13 | 6 | 9 | 13 |
| $\varphi^{-3}/55$ | $(2118,110,1241,1419)$ | 1 448 901 | 22.26 | 14 | 23.63 | 5 | 9 | 15 |
| $\varphi^{-3}/55$ | $(3873,830,1882,3226)$ | 1 467 539 | 22.26 | 16 | 23.20 | 7 | 8 | — |
| $\varphi^{-6}/55$ | $(-8972,-466,-5257,-6011)$ | 20 057 921 | 22.27 | 20 | 23.65 | 6 | 9 | — |
| $1/30$ | $(437,-36,293,235)$ | 54 210 | 24.66 | 21 | 32.25 | 4 | 5 | — |
| $\varphi^{-3}/30$ | $(972,705,164,1305)$ | 747 936 | 24.61 | 15 | 33.49 | 5 | 7 | — |
| $\varphi^{-6}/30$ | $(947,-233,731,353)$ | 9 929 377 | 24.63 | 16 | 33.51 | 5 | 8 | — |

($\delta M$ for the orbit of $0$ is not listed; its maximal conjugate from $0$ is in line 1, Table 4.1. The seeds at $\varphi^{-3}/55$ and $\varphi^{-6}/55$ in rows 6 and 8 are $\varepsilon$ times a point of the orbit in the row above; row 7 is the referee's witness of line 4.)

What the table shows:
1. The largest token component has a rescaled internal extent that converges along each sequence $\delta\varepsilon^k$: $15.64,15.73,15.75$; $23.13,23.63,23.65$; $32.25,33.49,33.51$. The increments shrink by about a factor $\varepsilon$, as $O(\delta)$ corrections to an exactly self-similar limit would.
2. The number of large components does not grow (11–23).
3. Every state is reached with at most 3 to 7 connectors ($e$), and $e$ does not grow along the $1/55$ and $1/30$ sequences (6, 5, 6 and 4, 5, 5); for the orbit of $0$ it is $3,4,5,5$.
4. The component sizes grow by a factor $11$–$15$ per step $\delta\mapsto\varepsilon\delta$ (for example $37\,946\to518\,136$ points in the largest component, levels 2 to 3), as the orbits do (growth exponent $\approx1.8$).
5. $P$ grows: $6,9,11,12$ for the orbit of $0$ at levels 0–3, and $13,15,17$ along the $1/55$ sequence (the value 17 at $\varphi^{-6}/55$ is the referee's). The state of largest internal modulus is reached with $P=4,3,4,3$ pieces (levels 0–3) and $5,6$ ($1/55$, $\varphi^{-3}/55$).

**Computation 4′ (random token components).** For random lattice seeds (a uniform physical point of $D_1\cup D_2$ and a uniform internal point of modulus at most $25/\delta$, rounded to $\Lambda$), only the token component of the seed was computed (exact tests). The largest $\delta\cdot(\text{internal extent})$ found:

| $\delta$ | $1/10$ | $1/20$ | $1/30$ | $\varepsilon/10$ | $1/55$ | $1/80$ | $\varphi^{-3}/30$ | $\varepsilon^2/10$ | $\varphi^{-3}/55$ | $\varepsilon^3/10$ | $\varphi^{-6}/30$ |
|---|---|---|---|---|---|---|---|---|---|---|---|
| seeds | 20 000 | 20 000 | 20 000 | 20 000 | 20 000 | 10 000 | 10 000 | 5 000 | 5 000 | 2 000 | 2 000 |
| max | 25.50 | 25.82 | 34.15 | 26.51 | 24.33 | 27.59 | 34.28 | 27.54 | 23.63 | 27.57 | 33.51 |

No sampled token component exceeds $34.3/\delta$, against $36.035/\delta$ per line in Theorem 1. **[computed]**

**Computation 5 (S4: the $1/55$ chain two steps deeper).** The orbit at $\varphi^{-6}/55$ of $\varepsilon^2\cdot(-500,-26,-293,-335)$, a point of the $1/55$ witness orbit, has $20\,057\,921$ points and $M\ge21\,978.915$ (diameter of $V$, exact comparison), so $\delta M\ge22.270$. A shortest word between the extreme states has $17\,447$ letters, of which $17\,435$ lie in 3 104 chord tokens, all assigned by $T$. The tokens form 6 runs, alternating between $\mathbb RE$ and $\mathbb R\bar E$, of $986,189,188,377,189,1175$ tokens, with 12 connector letters of total contribution $22.83$. The $1/55$ word has runs of $66,10,21,11,10,54$ tokens (line 4 Computation 10), and $\varphi^6=17.94$ times these, in reverse order, is $969,179,197,377,179,1184$, within $6\%$ of the run lengths at $\varphi^{-6}/55$. Along this sequence the run count is $6,7,6$, the token count grows by $4.24$ and $4.26$ per step ($172\to729\to3104$), and $\delta M=22.24,22.26,22.27$. **[computed]**

### 2.4 The replacement conjecture

**Conjecture B$^\sharp$.** There are $\delta_0>0$, $C_T$ and $K_0$ such that for $0<\delta\le\delta_0$:
- (T) every token component of $\mathcal T(r)$ has internal diameter at most $C_T/\delta$;
- (K) every word map at every point is the word map there of a word that splits into token paths and at most $K_0$ connector letters.

**[conjecture]** Evidence: Computations 4 and 4′ ((T) with $C_T\approx35$ on the samples; (K) with $K_0$ at least 9 and at most 14 on the orbits computed). Because (K) quantifies over every starting point, the $K_0$ an orbit needs is the diameter of its component graph, not the eccentricity $e$ of the seed. It is exactly $6,6,7,9,9,6$ on the six orbits where it was computed exactly (levels 0–2, $1/55$, row 6, $1/30$), and lies between the sweep bound and $2e$ on the others. Theorem 1 is the case of (T) for components inside one line.

**Proposition 6.** B$^\sharp$ implies $M(r)\le(K_0+1)C_T/\delta+1.903K_0$ for $0<\delta\le\delta_0$, hence Conjecture A of line 1 for these radii, hence (B). **[proved, given the conjecture]**

**Relation to B$^\ast$.** B$^\ast$ bounds the number of single-line runs. B$^\sharp$ bounds only the connectors and lets token walks switch lines freely, which is what the minimal words do (Computation 3(1)). B$^\sharp$ implies B$^\ast$ only if each token component is crossed by boundedly many single-line runs, and Computation 4(5) does not support that for every word map.

---

## 3. Proofs

### 3.1 Lemma 1.1

*Item 1.* Let $|h|\le0.15$, $X=sE+hN$, and $|\ell(X)|<\delta_h$. By (1.1), $|\Delta|^2\ge h^2$.
- The fourth letter of $w_1$ has test centre $P$. If $w_1$ acted at $X$, this test would pass: $r_c^2+\ell+|\Delta|^2\le r_c^2-\delta$, so $\ell\le-\delta-h^2\le-\delta_h$. That is impossible, so $w_1$ does not act at $X$.
- The second letter of $w_2$ has test centre $P'$. Likewise $-\ell\le-\delta-h^2$ is impossible, so $w_2$ does not act at $X$.
- $U_3(r)\subseteq U_3(r_c)$, and on $|h|\le0.15$ the domain $U_3(r_c)$ has $\ell\ge0.24471>\tfrac15\ge\delta_h$ (Computation 1.2). So $w_3$ does not act at $X$.

For a lift $X+2mE$, $m\neq0$, $\ell(X+2mE)=\ell(X)+2\sqrt5m$, because $\ell$ is affine with $\ell(X+E)-\ell(X)=2\operatorname{Re}(\bar uE)=\sqrt5$ (line 4, Lemma 5(2)). For $m=\pm1$ the value lies within $\tfrac15$ of $\pm4.47214$. On the band, $\ell\in[-4.22743,0]$ on $U_1$, $\ell\in[0,4.22743]$ on $U_2$ and $\ell\in[0.24471,4.22743]$ on $U_3$, and all three miss $(-4.67214,-4.27214)\cup(4.27214,4.67214)$. For $|m|\ge2$ the value has modulus above $8.74>8.47214$. So no token acts at any lift, and the arc lies in $\mathcal B_h(r)$.

*Item 2.* Let $h\ge0.15$. By Computation 1.2 the $s$-values of $U_2(r)$, of $U_3(r)$ and of $U_1(r)+2E$ on the line $L_h$ lie in $[-0.63704,1.04189]$, an interval of length $1.67893<2$. Its complement modulo 2, which contains the arc $(1.04189,1.36296)$, meets none of them modulo 2. The case $h\le-0.15$ is the same, with $U_1(r)$, $U_2(r)-2E$ and $U_3(r)-2E$ in $[-2.27796,-0.59903]$.

*Item 3.* All domains lie in $|h|\le1.80902$. $\square$

### 3.2 Theorem 1

In the coordinate $x=(s+1)/2\in\mathbb R/\mathbb Z$, the position of index $k$ is $x_0+k\varphi^{-1}$. Call $k$ *blocked* if $x_0+k\varphi^{-1}$ lies in the arc of Lemma 1.1, of normalized length $\lambda=\delta_h/\sqrt5$ (item 1), or $0.16053$ (item 2). An edge from index $k$ to $k+1$ is a token acting at a vertex of index $k$, whose position is $x_0+k\varphi^{-1}$ modulo 1. So no edge leaves a blocked index upwards. The index set of a component is an interval $I$ (edges change $k$ by $\pm1$), and every element of $I$ except its largest is unblocked.

*Three-distance theorem* (V. T. Sós, 1958; S. Świerczkowski, 1959). For $j\ge3$ and every $x$, the $F_j$ points $x+k\varphi^{-1}$, $0\le k<F_j$, cut $\mathbb R/\mathbb Z$ into arcs of lengths $\varphi^{-(j-1)}$ and $\varphi^{-(j-2)}$. (The denominators of the continued fraction of $\varphi^{-1}$ are the Fibonacci numbers, and $\|F_j\varphi^{-1}\|=\varphi^{-j}$. Line 4, Lemma 6, gives the weaker gap bound $1/F_j+\varphi^{-j}$ with a written proof, which yields the same theorem with $5.86$ in place of $\varphi^3$.)

So an open arc of length $\lambda>\varphi^{-(j-2)}$ contains one of any $F_j$ consecutive positions. Then $I$ cannot contain $F_j$ unblocked indices, so $|I|\le F_j$.

1. For $|h|>0.15$ item 2 below gives at most $8<F_7\le F_j$ values, so let $|h|\le0.15$ and use the arc of Lemma 1.1(1). $\delta_h\le\tfrac15$ gives $\lambda\le0.0895<\varphi^{-4}$, so $j\ge7$, and $j-1$ is not admissible: $\varphi^{-(j-3)}\ge\lambda$, that is $\varphi^j\le\sqrt5\varphi^3/\delta_h$. By Binet, $F_j\le(\varphi^j+\varphi^{-j})/\sqrt5<\varphi^3/\delta_h+1/\sqrt5$.
2. For $|h|\ge0.15$, $\lambda=0.16053>\varphi^{-4}=0.14590$, so $j\le6$ and $|I|\le F_6=8$.
3. Every token is a translation, so a path from $X_a$ to $X_b$ has word map $x\mapsto x+(s_b-s_a)E$. Write $s_b-s_a=2n\varphi^{-1}-2m$ with $n=k_b-k_a$; then $H(s_b-s_a)=-2\sqrt5n$, so $\sigma(s_b-s_a)=(s_b-s_a)-2\sqrt5n$. Every vertex of a component with an edge lies in some $U_i(r)$ or in $U_i(r)+\tau_iE$. By Computation 1.2 these sets have $s\in[-2.25507,2.25507]$ (for example $U_2+2\varphi^{-1}E$ reaches $1.01900+1.23607$), so $|s_b-s_a|\le4.51014$. Hence $|\sigma(tE)|\le|\sigma E|\bigl(4.51014+2\sqrt5(F_j-1)\bigr)<1.902113\,(4.51014+2\sqrt5\varphi^3/\delta_h)$, which is less than $8.579+36.0342/\delta_h$.
4. Complex conjugation $\iota$ conjugates $a,b$ to $a^{-1},b^{-1}$ and fixes the disks (line 4, Proposition 3). It maps lines parallel to $\mathbb RE$ to lines parallel to $\mathbb R\bar E$ and the class-$\mathrm{id},\nu$ tokens to the classes $\iota,\iota\nu$, and it commutes with $\sigma$.

The statement for $\delta\le\tfrac15$ uses $\delta_h\ge\delta$. The statement at $r_c$ is the case $\delta=0$, $h\neq0$: Lemma 1.1 used only $|\Delta|^2\ge h^2$ and strict inequalities. $\square$

### 3.3 Proposition 2

Put $\xi'=\varepsilon\xi$. Multiplication by the unit $\varepsilon$ is a bijection of $2\mathbb Z[\varphi]$. For $\xi\in2\mathbb Z[\varphi]$ write $\xi=2n\varphi^{-1}-2m$, so $n=n(\xi)=-H(\xi)/(2\sqrt5)$. Then
$$n(\varepsilon\xi)=-\frac{\sigma(\varepsilon)\sigma(\xi)-\varepsilon\xi}{2\sqrt5}=\frac{\varphi^3(\xi-2\sqrt5\,n)+\varphi^{-3}\xi}{2\sqrt5}=-\varphi^3n+\xi,$$
using $\sigma\xi=\xi-2\sqrt5n$ and $\varphi^3+\varphi^{-3}=2\sqrt5$.

The first forward return at $\varepsilon\delta$ from $v$ is given by the $\xi'\in2\mathbb Z[\varphi]$ with $v+\xi'/(\varepsilon\delta)\in W$ and $n(\xi')\ge1$ minimal. In terms of $\xi=\xi'/\varepsilon$: $v+\xi/\delta\in W$, so $|\xi|<\delta|W|<\tfrac12$.
- *Sign.* $n(\xi')=-\varphi^3n(\xi)+\xi\ge1$ holds iff $n(\xi)\le-1$. If $n(\xi)\le-1$ the value is at least $\varphi^3-\tfrac12>1$; if $n(\xi)\ge0$ it is at most $\xi<1$.
- *Order.* For two candidates with $n_1\neq n_2$, $|\varphi^3(n_2-n_1)|\ge4.23>|\xi_2-\xi_1|$. So $n(\xi'_1)<n(\xi'_2)$ iff $n_1>n_2$. If $n_1=n_2$, then $\xi_1-\xi_2\in2\mathbb Z$ has modulus below 1, so $\xi_1=\xi_2$.

Hence the minimizer at $\varepsilon\delta$ corresponds to the candidate at $\delta$ with $n\le-1$ largest, which is the first backward return: $\xi_{\varepsilon\delta}(v)=\varepsilon\xi^-_\delta(v)$ and $R_{\varepsilon\delta}(v)=v+\xi^-_\delta(v)/\delta=R_\delta^{-1}(v)$. That is item 1.

Item 2 is $\varepsilon\sigma(\varepsilon)=N(\varepsilon)=-1$. For item 3 apply item 1 twice: the backward return at $\varepsilon\delta$ is the forward return at $\delta$, by the same argument with the signs exchanged. $\square$

### 3.4 Proposition 6

Split a word realizing the word map at $z$ as in (K): at most $K_0+1$ token paths and at most $K_0$ connectors. Under composition of affine maps $\mu_i(x)=\zeta^{j_i}x+t_i$ the translation is $t=\zeta^{j_2}t_1+t_2$, so $|\sigma t|\le|\sigma t_1|+|\sigma t_2|$. A token path inside one component contributes at most $C_T/\delta$ by (T). A connector letter $x\mapsto p+\zeta^{\mp1}(x-p)$ has $t=p(1-\zeta^{\mp1})$, with $|\sigma t|=|1-\zeta^{\mp2}|=1.90211$. So $M(r)\le(K_0+1)C_T/\delta+1.903K_0$. Then $GG_5(r)$ is finite for $0<\delta\le\delta_0$ by `critical-radius-n5.md` Lemma 4.1, and for smaller $r$ by group monotonicity (`boundary-contact.md` Theorem 3.4), as in line 4, Corollary 11. $\square$

---

## 4. What the computations say, in plain terms

The previous picture was this: runs along one chord line, cut off at scale $1/\delta$, stopping in small windows at the breakpoints, where a letter or two passes the orbit to the other chord line. Theorem 1 confirms the first half for every walk confined to one line, with no condition on which token is used.

The second half is wrong. The three chord words act on large two-dimensional regions, and so do their mirror images on $\mathbb R\bar E$. Where both act, an orbit can switch from one family to the other without any other letter. The orbit is therefore assembled from a few large *token components*: connected sets on which every move is a translation by a chord token. Between them sits a dust of components with one or two points, and the pieces are joined by single letters at very many places.

Measured in internal space, the large components have a size proportional to $1/\delta$ with a stable constant ($\approx15.75$, $23.65$ and $33.5$ on three families). Their number stays between 11 and 23. Every state can be reached with at most about 7 single letters. This is the self-similar structure that a proof should capture. Its two parts are a two-dimensional version of Theorem 1, and a bound on the number of single letters.

## 5. The remaining gap, and an assessment

**What S1–S4 delivered.**
- *S1: closed.* Theorem 1, with explicit constants, uniform in the offset, valid at $r_c$ off the chord line.
- *S2: (a) answered negatively, (b) proved for the one-line part, (c) not reached.*
  - (a) The window first-return map with all letters is not a finite object on $O(\delta)$-windows at finitely many points: connectors between large components occur all over the disks (Computation 3).
  - (b) Its one-line part (golden rotation, linear window) is exactly invariant under $\delta\mapsto\varepsilon^2\delta$ and inverted under $\delta\mapsto\varepsilon\delta$ (Proposition 2). The failure of linearization is confined to bands of relative width $O(\delta)$ at the window ends (one-line lunes). In the lattice these are not excluded by any inequality proved here.
  - (c) The return graph that would have to be shown bounded is the token-component graph. Its diameter is 6–9 in the data, and that it is bounded is (K).
- *S3: replaced.* Per offset, Theorem 1 gives a run length at most $\varphi^3/\min(\delta+h^2,\tfrac15)$, and at most 8 positions for $|h|\ge0.15$. A per-scale count of single-line runs is not the right quantity, because the least number of runs needed grows with the level (Computation 4(5)) while the number of connectors does not.
- *S4: done.* The $1/55$ chain persists two renormalization steps deeper, with the same number of runs (6, 7, 6) and the same $\delta M$.

**The precise remaining gap: Conjecture B$^\sharp$.**
- (T): a two-dimensional free-token cut-off. The mechanism of Theorem 1 does not extend directly. A walk can change its offset by tokens of the other class, and that moves the blocked window $|\ell|<\delta_h$, whose position depends on $h$. So "every $F_j$ consecutive indices contain a blocked one" fails for mixed walks. A proof must use the fact that long single-line runs exist only near the two chord lines ($|h|\le0.15$ for $\mathbb RE$, by Theorem 1(2)), so long walks of the two classes meet only near $0$. It must also control the short hops in between, which change the offset by elements of $2\mathbb Z[\varphi]$ of small index ($\pm0.29$, $\pm0.18$ in $t$).
- (K): bounded chaining of token components. Its natural renormalization is the two-dimensional analogue of Proposition 2: a cut-and-project structure in $(s,t)$ with $X=sE+t\bar E$, where both coordinates perform the golden rotation modulo 2.

**Assessment.**
- *Repairable, not closed.* The one-dimensional reduction (runs, windows, connectors at windows) is **dead as stated**: the walks between windows are two-dimensional.
- What replaces it is better supported by the data: a bounded number of large token components, of rescaled size converging along each renormalization sequence, joined by a bounded number of letters. Theorem 1 and Proposition 2 are the one-line cases of the two statements needed.
- I expect (T) to be the next provable step. It is a statement about a piecewise translation of the plane by the vectors $\pm2\varphi^{-1}E,\pm2\varphi^{-2}E$, $\pm2\varphi^{-1}\bar E,\pm2\varphi^{-2}\bar E$ on six explicit convex domains, with no other letters involved.
- (K) carries the remaining difficulty of (B).

## 6. Reproduction

All programs are throwaway scratch code, not part of the repository. They are described so that they can be re-implemented. Lattice arithmetic is as in line 4 §6: integer 4-vectors, multiplication by $\zeta^{\pm1}$, exact disk tests by the sign of $\rho-|y\mp1|^2$ in $\mathbb Z[\varphi]$ with 128-bit integers. Radii: $\delta=1/q$ is $\rho=(3q-1+q\varphi)/q$. The levels are $(29+10\varphi)/10$, $(33+8\varphi)/10$, $(17+18\varphi)/10$, $(85-24\varphi)/10$. $\varphi^{-3}/30$, $\varphi^{-6}/30$, $\varphi^{-3}/55$ and $\varphi^{-6}/55$ are $(93+28\varphi)/30$, $(77+38\varphi)/30$, $(168+53\varphi)/55$ and $(152+63\varphi)/55$. Multiplication by $\varepsilon$ is multiplication by $(-3,0,-2,-2)$.

- **Computation 1.2** (`s1rig.py`, mpmath, 60 digits). The centres in strip coordinates $(|E|s,h)$ come from the exact lattice centres. Candidates: disk extreme points in the direction of the functional; pairwise circle intersections; intersections of each circle with the band lines. A candidate is kept if it satisfies every disk and band inequality to within $10^{-40}$. Keeping slightly infeasible candidates can only enlarge a computed range, which is the safe direction.
- **Lifted orbits and $\delta M$** (`lift`, the referee's program of line 4 §4). Breadth-first search over states $(y,j)$, convex hull of $V=\{\zeta^{-2j}\sigma y\}$, exact comparison of the near-extreme pairs, and a shortest word. The word decomposition is the referee's `decomp.py`.
- **Piece counts $P$ and $e$** (`cost`). After the lifted search, a 0-1 breadth-first search on (state, line class). A token move (one of the twelve tokens acting, all letters global) costs 0 if it continues the current line class and 1 otherwise (mode 1), or always 0 (mode 2). A connector letter costs 1 and resets the class. $P$ is the maximum over states of the mode-1 cost, and $e$ the maximum of the mode-2 cost. Parent pointers give the paths of Computation 3(1).
- **Token components** (`comp`). Union-find over token edges in the lifted orbit. For each component: size and the bounding box of $V$. The component graph is built from connector edges between distinct components. Eccentricity is by breadth-first search from the seed's component, and $D$ is the largest eccentricity in three sweeps (each starting at the farthest component of the last). The same program lists the connector edges between components above a size threshold (Computation 3(2)) and the orbit points near $0$ (Computation 5).
- **Random token components** (`tokcomp`). A physical point uniform in $D_1\cup D_2$ and an internal point uniform in the disk of radius $25/\delta$ are rounded to $\Lambda$ through the inverse of the $4\times4$ Minkowski matrix. Breadth-first search uses token moves only, with random seed 1.
- **Cross-checks.** Orbit sizes agree with line 4 and its referee report (111 107 at $1/55$; 1 467 539, 54 210, 747 936, 9 929 377 for the referee's witnesses; 1 433, 30 165, 400 519, 5 673 561 for the orbit of $0$ at levels 0–3). The two independent counts $e$ (from `cost` mode 2 and from `comp`) agree on all six orbits where both were run. The diameter at $\varphi^{-3}/55$ is $5\,185.891869$ for both seeds, with the same exact squared value $7433192+12027116\varphi$.
- **Proposition 2 check** (`prop2.py`, 50 digits): first returns at $\delta$, $\varepsilon\delta$, $\varepsilon^2\delta$ for random $v$, $\delta=1/55,1/30$, $W=(-0.3,0.6)$.
