# Period-two renormalization at the tight points of $GG_5$: exact tests on large samples, a positivity lemma, and the remaining gap

Authors: Eric Vergo, Claude

**What is and is not established.** Let $r_c=\sqrt{3+\varphi}$. **(B), finiteness of $GG_5(r)$ for every $r<r_c$, is not proved here, and neither is exact period two.** This note tests and analyses the period-two conjecture of [`sharp-lower-bound-limit-system.md`](sharp-lower-bound-limit-system.md) (Conjecture 5.1 there) at the tight points $\pm E,\pm\bar E$.

1. **Refuted (exact): period two in the unrestricted form.** The first-return set at level $k+2$ differs from that at level $k$, in zoomed coordinates, for 293 of the 811 points of the fixed sample $S_E$ at $k=2$, including $E$ itself. The failures are *not* all growths: 62 are growths, 223 shrinkings, 8 incomparable (§6.2). This is a difference from $n=12$, where every observed change from level 1 on was a growth.
2. **Computed (exact), no counterexample: the lune criterion.** Every observed change between levels $k$ and $k+2$ has a lune point in the level-$k$ excursion; every start whose level-$k$ excursion is lune-free keeps its first-return set at level $k+2$. Cases: 349 lune-free starts (295 at $k=2$, 54 at $k=3$) on four internal-radius bands up to $|\sigma\eta|\le400$, with no failure (§6.3). Lune-freeness persisted from level $k$ to $k+2$ in every case tested. The level-5 part of this evidence is biased towards small excursions (§6.3), and level 6 is out of reach in the memory used (the excursion of $E$ itself exceeds $1.8\cdot10^8$ points).
3. **Computed (exact): the statistics do not depend on the internal radius at levels $\le4$.** Agreement rates, lune-free rates and excursion sizes are the same on the bands $|\sigma\eta|\le50$, $50$–$100$, $100$–$200$, $200$–$400$ (§6.4). This is explained (proved, Lemma 3.5) by the fact that the Diophantine lune lemma excludes no lune at levels $\le3$, and at levels 4 and 5 only at zoomed internal radius below $0.08$ and $0.46$, far below the internal spread of an excursion: lunes at these levels are a physical, not an arithmetic, phenomenon. The mean number of lune points per excursion falls by a factor close to $\varepsilon=\varphi^{-3}$ per level (94, 18.3, 6.5, 1.04 at levels 1–4), while the number of excursion points near critical points does not grow.
4. **Proved: the positivity lemma** (Lemma 3.2, Proposition 3.3), the precise form of the referee's parity mechanism. For every level $k\ge1$, every non-critical disk test whose cut meets the zoomed core has a zoomed offset whose Galois conjugate has the sign $(-1)^k$; the constant is explicit and no "large $k$" is needed. Consequently, among the zoom maps $(k,\eta)\mapsto(k+m,\pm\eta)$, only those with $+$ and $m$ even preserve both the tight half-plane tests and the sign class of the near-miss offsets: the minimal one is $\varepsilon^2$, the least *totally positive* power. The map $\varepsilon$ fails the internal condition, and $-\varepsilon$ fails both; the data confirm both failures for general $\eta$. One exception is observed and not explained: at $E$ itself ($\eta=0$) the first-return sets at consecutive levels are exact negatives of each other from level 3 on (§6.5). So matching of return sets does not require matching of cuts, and Proposition 3.3 is a necessary condition only for matchings induced by cuts.
5. **Proved: why the positivity argument does not give a conjugacy.** The zoom $\Psi_E^2$ does not commute with the rotations (Lemma 3.6), and a near-miss cut at level $k$ has an exact counterpart at level $k+2$ only if a norm equation is solvable; so the lune lemma plus total positivity gives a *necessary condition* for matching, not a conjugacy of chains. Period two, where it holds, is a property of the return relation and not of chains or cuts.
6. **Proved: what period two would give** (Theorem 4.3). If the lune criterion holds from some level on, and if excursions from bounded internal radius stay within internal radius $O(\varphi^{3k})$ (observed: at most $48\,\varphi^{3k}$ beyond the start at levels 1–4, §6.4), then the first-return relation is exactly period two on the explicit domains $\mathcal D_k=\{|\eta|\le\tfrac3{10},\ |\sigma\eta|\le M_k\}$ with $M_k\asymp\varphi^{3k}$ (an explicit formula). This is **not** (R-core-t): the zoomed tight core contains lattice points of every internal radius, and the step from $\mathcal D_k$ to all points (the face-inradius problem) and two base levels beyond the certified range remain. §5 lists the exact remaining gap.

So: (R-bulk-t) is untouched here; (R-core-t) is not obtained; the renormalization step is reduced to one precisely stated conjecture (the lune criterion, Conjecture 4.1), which the data support without exception, plus the inputs listed in §5. My assessment: **repairable in principle but not closed**; the route needs a new idea for the lune criterion (a statement about return relations, not chains) and for generic points.

Terms: *level, zoomed coordinate, core, first-return set, excursion, lune point, near miss* (§1–§2).

---

## 1. Statements

All objects are those of `sharp-lower-bound-limit-system.md` §1–§2; they are repeated here so that every claim below is checkable.

**Setting.** $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$, $\varphi=(1+\sqrt5)/2$, $\sigma\colon\zeta\mapsto\zeta^2$ (so $\sigma\varphi=-\varphi^{-1}$). $\varepsilon=\varphi^{-3}=2\varphi-3$; $\sigma\varepsilon=-\varphi^3$, $N(\varepsilon)=-1$. The *level* $k$ radius is $r_k^2=3+\varphi-\varepsilon^k/10$. $D_1,D_2$ are the closed disks of radius $r$ about $\mp1$; $a,b$ rotate by $\zeta^{-1}$ about $\mp1$ on them.

**Critical points, core.** The 38 lattice points of $\partial D_1\cup\partial D_2$ at $r_c$. For a critical $Q\in\partial D_p$, $w=Q-p$ satisfies $|w|^2=3+\varphi$ and $|\sigma w|^2=4-\varphi$. The level-$k$ core is $B_k=\bigcup_Q\overline B(Q,\tfrac3{10}\varepsilon^k)$. A core point $x=Q+\varepsilon^k\eta$ has *zoomed coordinate* $\eta\in\Lambda$ ($|\eta|\le0.3$); its *zoomed internal radius* is $|\sigma\eta|$. The tight points are $E=\zeta-\zeta^2$, $-E$, $\bar E$, $-\bar E$; by the symmetries $z\mapsto-z,\bar z$ it suffices to test at $E$.

**First-return set, excursion.** $R_k(\eta)$ is the set of zoomed core points $(Q',\eta')$ reached from $x=E+\varepsilon^k\eta$ by chains at radius $r_k$ whose intermediate points avoid $B_k$, together with $x$ itself. The *excursion* is the set of all points of these chains.

**Lune point.** For a critical $Q\in\partial D_p$ and $y=Q+\varepsilon^kY\in\Lambda$, $\lambda_Q(Y)=20\operatorname{Re}(Y\bar w)+1\in1+10\mathbb Z[\varphi]$. $y$ is a *lune point* at level $k$ if the disk test $y\in D_p(r_k)$ and the half-plane test $\lambda_Q(Y)<0$ disagree. An excursion is *lune-free* if none of its points within distance $3\varepsilon^k$ of a critical point is a lune point (for every tight disk through that critical point).

**Near miss.** For $u\in\Lambda$ put $D(u)=10(|u|^2-r_c^2)\in10\mathbb Z[\varphi]$. A disk test of $D_p$ at the chain point $h(x)$, $h(z)=\zeta^Jz+t$, has base vector $u=h(E)-p$; it is *critical* if $D(u)=0$ and a *near miss* otherwise. Its *zoomed offset* is $\tilde\delta_k(u)=1+\varepsilon^{-k}D(u)$.

**Claims.**

| # | statement | status |
|---|---|---|
| L3.1 | Exact zoomed form of a disk test along a chain (identity (3.1)) | proved |
| L3.2 | Near-miss positivity: if a near-miss cut meets the zoomed core at level $k\ge1$, then $|\sigma u|>|\sigma w|$ and $\operatorname{sign}\sigma(\tilde\delta_k(u)-1)=(-1)^k$ | proved |
| P3.3 | Among zoom maps $(k,\eta)\mapsto(k+m,s\eta)$, $s=\pm1$, only $s=+1$, $m$ even preserve both the tight tests and the offset sign classes | proved |
| L3.4 | Rescaled inclusion: $\sim_k$ on the inner core, rescaled by $\varepsilon^{-j}$, is contained in $\sim_{k+j}$ | proved |
| L3.5 | Lune-freeness from an internal bound; excludes nothing at $k\le3$, and only zoomed internal radius $<0.46$ at $k\le5$ | proved |
| L3.6 | $\Psi_E^2$ is not a conjugacy of chains | proved |
| C4.1 | Lune criterion: lune-free at $k$ $\Rightarrow$ $R_{k+2}=R_k$ | conjecture (exact evidence §6.3) |
| C4.2 | Bounded internal drift: excursions from $|\sigma\eta|\le M$ stay within internal radius $\varphi^{3k}(M+c_0)$ of $\sigma E$ | conjecture ($c_0\le48$ observed, §6.4) |
| T4.3 | C4.1 + C4.2 $\Rightarrow$ exact period two on $\mathcal D_k$ from an explicit level | proved (conditional) |
| P4.4 | Exact period two of the orbit relation on the whole tight core from $k_0$, plus finiteness at $k_0,k_0+1$, $\Rightarrow$ (R-core-t) | proved (conditional) |
| P4.5 | Monotone coarsening with period two + bounded limit classes $\Rightarrow$ (R-core-t) | proved (conditional) |
| §6 | Tables of agreement, failures, lunes, radii | computed, exact |
| Ref | Unrestricted period two at $2\to4$ | refuted (exact, §6.2) |

---

## 2. The exact program

All data of §6 come from one throwaway C program, `fr5.c`, written for this note and not committed. A referee can re-implement it from this description.

- **Points** are integer 4-vectors in the basis $1,\zeta,\zeta^2,\zeta^3$, with $\zeta^4=-1-\zeta-\zeta^2-\zeta^3$. Multiplication by $\zeta^{-1}$ is $(v_0,v_1,v_2,v_3)\mapsto(v_1-v_0,v_2-v_0,v_3-v_0,-v_0)$, by $\zeta$ is $(w_0,\dots,w_3)\mapsto(-w_3,w_0-w_3,w_1-w_3,w_2-w_3)$.
- **Norms.** $|w|^2=(S_0-S_1)+(S_1-S_2-S_3)\varphi$ with $S_0=\sum w_i^2$, $S_1=w_0w_1+w_1w_2+w_2w_3$, $S_2=w_0w_2+w_1w_3$, $S_3=w_0w_3$.
- **Signs.** The sign of $x+y\varphi$ is the sign of $(2x+y)+y\sqrt5$, decided by comparing $(2x+y)^2$ with $5y^2$ in 128-bit integers.
- **Disk test** at level $k$: $z\in D_p(r_k)$ iff $10|z-p|^2-(30+10\varphi)+\varepsilon^k\le0$, with $\varepsilon^k=a_k+b_k\varphi$ from $\varepsilon(a+b\varphi)=(-3a+2b)+(2a-b)\varphi$. It is exact and never a tie (non-norm radii).
- **Core test**: $100|y-Q|^2\le9\varepsilon^{2k}$, exact. Floating point only preselects the candidate critical points: a point farther than $3.0003\varepsilon^k$ (plus $10^{-9}$) from both boundary circles, in double precision, is not tested (the rounding error is below $10^{-9}$ for the coordinates that occur).
- **Lune test**: for a point within (floating) distance $3\varepsilon^k$ of a critical $Q$, $Y=\varphi^{3k}(y-Q)$ exactly ($\varphi^3=1+2\varphi=(1,0,-2,-2)$), $\lambda=10(|Y+w|^2-|Y|^2-(3+\varphi))+1$, and the exact disk test is compared with the sign of $\lambda$. The preselection radius only affects the definition of "within zoomed distance 3", which is a statistic.
- **First returns.** Breadth-first search over $\Lambda$ under $a^{\pm1},b^{\pm1}$; core points are recorded and not expanded. The non-core points of one search form a connected component of the graph with core points removed; components are cached (hash of points $\to$ component id, with the list of core points adjacent to the component), so $R_k(\eta)=\{x\}\cup\{$core neighbours of $x\}\cup\bigcup\{$core points adjacent to the components of the non-core neighbours of $x\}$. Excursion size = $1+$ component sizes $+$ number of returned points other than $x$.
- **Orbit partitions** (closure mode): the first-return graph is closed over all core points reached; the result is $O_{r_k}(x)\cap B_k$ in zoomed coordinates.
- **Samples** (`gen5.c`, exact): all $\eta\in\Lambda$ with $100|\eta|^2\le9$ and $M_1^2<|\sigma\eta|^2\le M_2^2$, enumerated as $\eta=\varepsilon^j\xi$ with $j$ balancing the two radii and $\xi$ in a box derived from the inverse Minkowski matrix with slack; both inequalities are tested exactly ($\sigma(A+B\varphi)=(A+B)-B\varphi$).

**Validation.**
- $R_k$ for $(E,\eta=(-3,-1,-1,-3))$ at levels 1–4 has $6,36,6,46$ points and excursions of $156$, $60\,861$, $21\,066$, $16\,128\,171$ points, the level-3 excursion lune-free: as in `sharp-lower-bound-limit-system.md` §5.2.
- The full orbit of $E+\varepsilon(-3,-1,-1,-3)$ at level 1 has $71\,817$ points, equal to `tdcsg-orbit orbit -n 5 --r2 re:41/10,4/5 --start pow:13,6,4,13` (the engine's count).
- Closure mode on $S_{21}$ (798 points, 21 per critical point) gives 387 and 414 orbits with at most 1 578 and 1 352 core visits at levels 1 and 2: Table 6.1 of `sharp-lower-bound-combined.md`.
- On $S_E$: consecutive agreement 0, 14, 14 at $1\to2$, $2\to3$, $3\to4$; two levels apart 185 ($1\to3$) and 518 ($2\to4$); 124 of 124 lune-free starts agree at $2\to4$; the unit $-\varepsilon$ gives 34, 64, 80: all as in `sharp-lower-bound-limit-system.md` §5.2 and its referee report.

---

## 3. Proved lemmas

### 3.1 Zoomed tests along a chain

**Lemma 3.1.** Let $x=E+\varepsilon^kY$, $|Y|\le0.3$, and let $h(z)=\zeta^Jz+t$ be the prefix map of a chain at $x$. The disk test of $D_p$ at $h(x)$, with $u=h(E)-p$, is the sign of
$$\varepsilon^{-k}\cdot10\bigl(|h(x)-p|^2-r_k^2\bigr)=\tilde\delta_k(u)+20\operatorname{Re}\bigl(\zeta^JY\bar u\bigr)+10\varepsilon^k|Y|^2 .\tag{3.1}$$

*Proof.* $h(x)-p=u+\zeta^J\varepsilon^kY$; expand $|u+\zeta^J\varepsilon^kY|^2$ and use $10r_k^2=10r_c^2-\varepsilon^k$. $\square$

For a critical test ($u$ a critical vector, $D(u)=0$) this is the tight test of `sharp-lower-bound-limit-system.md` (2.1), with $Y$ replaced by $\zeta^JY$.

### 3.2 Positivity of near-miss offsets

**Lemma 3.2.** Let $k\ge1$ and let $u\in\Lambda$ with $D(u)\neq0$ be the base vector of a test whose zero set (3.1) meets $\{|Y|\le0.3\}$. Then:
1. $|D(u)|\le15.37\,\varepsilon^k\le3.628$;
2. $|\sigma u|>|\sigma w|=\sqrt{4-\varphi}=1.5434$, that is $\sigma D(u)>0$;
3. $\sigma\bigl(\tilde\delta_k(u)-1\bigr)=(-1)^k\varphi^{-3k}\,\sigma D(u)$ has the sign $(-1)^k$.

*Proof.* (2) first, under the assumption $|D(u)|<10/(4-\varphi)=4.1982$. $D(u)=10t$ with $t\in\mathbb Z[\varphi]\setminus\{0\}$, so $|N(D(u))|=100|N(t)|\ge100$, i.e. $|D(u)|\,|\sigma D(u)|\ge100$. Since $\sigma(|u|^2)=|\sigma u|^2\ge0$, $\sigma D(u)=10(|\sigma u|^2-(4-\varphi))\ge-10(4-\varphi)=-23.82$. If $\sigma D(u)<0$, then $|\sigma D(u)|\le23.82$ and $|D(u)|\ge100/23.82=4.1982$, a contradiction; $\sigma D(u)=0$ is excluded by the norm.

(1) If the zero set of (3.1) meets $|Y|\le0.3$, then $|\tilde\delta_k(u)|\le6|u|+0.9\varepsilon^k$, so $|D(u)|\le\varepsilon^k(1+6|u|+0.9)$. With $|u|^2=r_c^2+D(u)/10$ this reads $|D|\le\varepsilon^k(1.9+6\sqrt{4.618+|D|/10})$, whose right side grows like $\sqrt{|D|}$ (for $D<0$ the root is smaller, and the same bound holds). For $k\ge1$ ($\varepsilon^k\le0.2361$) and $|D|\ge4.1982$ the right side is at most $0.2361(1.9+6\cdot2.2449)\cdot\sqrt{|D|/4.1982}<|D|$, so every such test has $|D|<4.1982$, and then $|D|\le15.37\,\varepsilon^k\le3.628$.

(3) $\sigma(\varepsilon^{-k})=\sigma(\varphi^{3k})=(-\varphi^{-1})^{3k}=(-1)^k\varphi^{-3k}$. $\square$

So **for every $k\ge1$, every near miss that cuts the zoomed core is internally larger than the critical vectors, and its zoomed offset lies on the side $(-1)^k$ of $1$ in the internal line.** Write $\mathcal O_k\subset10\mathbb Z[\varphi]$ for the set of values $\beta=\tilde\delta_k(u)-1=\varepsilon^{-k}D(u)$ of the near misses that cut the zoomed core at level $k$. Then $|\beta|\le15.37$ and $(-1)^k\sigma\beta>0$. In particular $\mathcal O_k\cap\mathcal O_{k+1}=\varnothing$ for every $k\ge1$: two consecutive levels never share a near-miss offset, while levels of equal parity lie in the same half-line $\{(-1)^k\sigma\beta>0\}$. This is the referee's identity (`referee-report-sharp-lower-bound-limit-system.md` §3) with the "for large $k$" removed and the constant made explicit.

### 3.3 Which zoom maps are compatible

Call a *zoom map* $T_{m,s}\colon(k,\eta)\mapsto(k+m,s\eta)$, $m\ge1$, $s=\pm1$. It relates the level-$k$ zoomed point $E+\varepsilon^k\eta$ to the level-$(k+m)$ zoomed point $E+\varepsilon^{k+m}s\eta$; physically it is $y\mapsto E+s\varepsilon^m(y-E)$, i.e. the unit $u=s\varepsilon^m$.

**Proposition 3.3.**
1. *(Physical condition.)* The tight test at $E$ of the zoomed point $\eta$ at level $k$ is the sign of $\lambda(\eta)+10\varepsilon^k|\eta|^2$, with $\lambda(\eta)=20\operatorname{Re}(\eta\bar w)+1$ independent of $k$. For $s=+1$ the tests of $\eta$ at levels $k$ and $k+m$ agree unless $\eta$ is a lune point at level $k$. For $s=-1$ they disagree for every $\eta$ with $\lambda(\eta)<-10\varepsilon^k|\eta|^2$ (inside at level $k$) or $\lambda(\eta)>2$ (outside at level $k$), since $\lambda(-\eta)=2-\lambda(\eta)$.
2. *(Internal condition.)* A near-miss cut at level $k$ and one at level $k+m$ have equal zoomed offsets only if $m$ is even (Lemma 3.2(3)); for $m$ even the two offset sets lie in the same half-line $\{(-1)^k\sigma\beta>0\}$.
3. Hence a zoom that preserves the tight tests (for all $\eta$ outside the lunes) and can carry near-miss offsets to equal near-miss offsets has $u=\varepsilon^m$ with $m$ even: $u$ is *totally positive*. The least such zoom is $\varepsilon^2$; $\varepsilon$ fails condition 2, and $-\varepsilon$ (positive in the internal embedding, negative physically) fails both.

*Proof.* (1) For $s=+1$ the two test values are $\lambda+10\varepsilon^k|\eta|^2$ and $\lambda+10\varepsilon^{k+m}|\eta|^2$, which can differ in sign only if $-10\varepsilon^k|\eta|^2<\lambda<-10\varepsilon^{k+m}|\eta|^2$, i.e. only at a lune point of level $k$. For $s=-1$: if $\lambda(\eta)<-10\varepsilon^k|\eta|^2$, then $\eta$ is inside at level $k$ while $\lambda(-\eta)>2$ puts $-\eta$ outside at level $k+m$; if $\lambda(\eta)>2$, then $\eta$ is outside while $\lambda(-\eta)<0$ and, unless $-\eta$ is a lune point at level $k+m$, $-\eta$ is inside. (2) is Lemma 3.2(3). $\square$

What this does and does not show. It is a *necessary-condition* statement for a renormalization that is the identity (or $-1$) on zoomed coordinates and matches cuts with cuts. It does not show that $\varepsilon^2$ is a renormalization, and it does not apply to matchings of return relations that are not induced by matchings of cuts (which is what the data show, Lemma 3.6). It explains why the period cannot be one for $n=5$ in this sense, and is the precise form of "total positivity" in the referee's proposed rule.

### 3.4 The only proved inter-level inclusion

**Lemma 3.4 (rescaled inclusion).** For $k,j\ge0$ and zoomed points with $|\eta|,|\eta'|\le0.3\varepsilon^j$: if $Q+\varepsilon^k\eta$ and $Q'+\varepsilon^k\eta'$ lie in one orbit at $r_k$, then $(Q,\varepsilon^{-j}\eta)$ and $(Q',\varepsilon^{-j}\eta')$ are zoomed core points at level $k+j$ lying in one orbit at $r_{k+j}$.

*Proof.* They are the same physical points, and $O_{r_k}\subseteq O_{r_{k+j}}$ (`boundary-contact.md` Theorem 3.1). $\square$

This compares the level-$k$ relation on the *inner* core of radius $0.3\varepsilon^j$ with the level-$(k+j)$ relation on the full core, for both parities of $j$. It is the inclusion observed in `sharp-lower-bound-n5.md` §7. It gives lower bounds on core orbit sets, never upper bounds, and says nothing about period two.

### 3.5 When the lune lemma bites

**Lemma 3.5.** Let $Q'\in\partial D_p$ be critical and $z=Q'+\varepsilon^kY$ a lattice point with $|Y|\le3$ and $|\sigma Y|\le M$. If $\varphi^{3k}\ge90(30.87M+1)$, then $z$ is not a lune point of $D_p$ at level $k$. The largest $M$ allowed is $(\varphi^{3k}/90-1)/30.87$: none for $k\le3$, then $0.084$, $0.459$, $2.05$, $8.78$, $37.3$, $158$ for $k=4,\dots,9$.

*Proof.* A lune point has $-10\varepsilon^k|Y|^2<\lambda<0$, so $|\lambda|<90\varepsilon^k$. $\lambda\in1+10\mathbb Z[\varphi]$ has $|N(\lambda)|\ge1$ and $|\sigma\lambda|\le20|\sigma w||\sigma Y|+1\le30.87M+1$, so $|\lambda|\ge1/(30.87M+1)$. $\square$

Excursion points near critical points have $|\sigma Y|$ up to about $47$ beyond the start's $|\sigma\eta|$ (§6.4). Consequently, at levels $k\le5$ the lune points of excursions are not excluded by arithmetic at any internal radius of the start, which is why the statistics of §6.4 do not depend on the zoomed internal radius of the start. The lune lemma starts to separate bounded internal radius from large internal radius only from level 6 on, beyond every computed level.

### 3.6 Why total positivity does not give a conjugacy

**Lemma 3.6.** Let $\Psi(z)=E+\varepsilon^2(z-E)$ and $R_p(z)=p+\zeta^{-1}(z-p)$. Then $\Psi R_p(z)-R_p\Psi(z)=(1-\varepsilon^2)(1-\zeta^{-1})(E-p)\neq0$ for every $z$.

*Proof.* Expand both sides. $\square$

Equivalently, $\Psi R_p\Psi^{-1}$ is the rotation by $\zeta^{-1}$ about $\Psi(p)=E+\varepsilon^2(p-E)\ne\pm1$, so $\Psi$ does not carry chains of the level-$k$ system to chains of any level; at the tight tests of $E$ itself the zoomed half-plane tests agree (Proposition 3.3(1)), but every rotation step moves the chain to where the two systems differ by a translation of size $(1-\varepsilon^2)|1-\zeta^{-1}||E-p|$. Moreover a near-miss cut of (3.1) at level $k$, with base vector $u$, is the same zoomed line as a cut at level $k+2$ with base vector $u'$ only if $\zeta^{-J'}u'$ is a positive real multiple of $\zeta^{-J}u$ and $D(u')=\varepsilon^2D(u)$, i.e. only if $r_c^2+\varepsilon^2D(u)/10$ is the norm of a lattice vector in a prescribed direction; this is a norm equation with generically no solution, consistent with the observation (`sharp-lower-bound-limit-system.md` §5.4) that cut lines do not recur. Hence the lune lemma and total positivity of $\varepsilon^2$ yield a necessary condition for period two (Proposition 3.3), not a conjugacy between the level-$k$ and level-$(k+2)$ systems. Period two, where it holds, must be a property of the return *relation*: different chains with different cuts produce the same returns.

---

## 4. Conditional statements

**Conjecture 4.1 (lune criterion with period two).** For every zoomed tight-core lattice point $\eta$ and every level $k\ge2$: if the level-$k$ excursion of $\eta$ is lune-free, then the level-$(k+2)$ excursion is lune-free and $R_{k+2}(\eta)=R_k(\eta)$.

**Conjecture 4.2 (bounded internal drift).** There is $c_0$ such that for every $k\ge1$ and every zoomed tight-core lattice point $\eta$, every point $z$ of the level-$k$ excursion satisfies $|\sigma z-\sigma E|\le\varphi^{3k}(|\sigma\eta|+c_0)$.

**Theorem 4.3 (conditional; proved).** Assume Conjectures 4.1 and 4.2, and for $k\ge2$ put
$$M_k=\frac{\varphi^{3k}/90-1}{30.87}-c_0-1,\qquad \mathcal D_k=\{\eta\in\Lambda:\ |\eta|\le0.3,\ |\sigma\eta|\le M_k\}.$$
Then for every $k\ge2$ and every $\eta\in\mathcal D_k$: $R_{k+2j}(\eta)=R_k(\eta)$ for all $j\ge0$.

*Proof.* A point $z$ of the level-$k$ excursion within distance $3\varepsilon^k$ of a critical $Q'$ has $Y=\varepsilon^{-k}(z-Q')$ with
$$|\sigma Y|=\varphi^{-3k}|\sigma z-\sigma Q'|\le|\sigma\eta|+c_0+\varphi^{-3k}|\sigma E-\sigma Q'|\le M_k+c_0+1,$$
using Conjecture 4.2, $|\sigma Q|\le2.53$ for every critical point (so $|\sigma E-\sigma Q'|\le5.06\le\varphi^{3k}$ for $k\ge2$). By Lemma 3.5 the excursion is lune-free, and Conjecture 4.1 gives $R_{k+2}(\eta)=R_k(\eta)$. Since $M_{k+2}\ge M_k$, $\eta\in\mathcal D_{k+2}$ and the argument repeats. $\square$

So under the two conjectures, period two holds exactly on domains $\mathcal D_k$ whose zoomed internal radius grows like $\varphi^{3k}/2778$. With the observed $c_0\le48$ (§6.4), $\mathcal D_k$ is non-empty from $k=9$ ($M_9\approx109$; $M_8<0$).

**Proposition 4.4 (what exact period two on the whole core would give; proved).** Write $\sim_k$ for "same orbit at $r_k$" on zoomed tight-core lattice points. Suppose that for some $k_0$ and all $k\ge k_0$, $\sim_{k+2}=\sim_k$ on all zoomed tight-core lattice points, and that $GG_5(r_{k_0+1})$ is finite. Then (R-core-t) holds: $\sup_y|O_{r_k}(y)\cap B^{\rm t}_k|\le\max(N_{k_0},N_{k_0+1})$ for $k\ge k_0$, with $N_k$ the supremum at level $k$ over lattice points.

*Proof.* As `sharp-lower-bound-n12.md` Proposition 6.4, with two base levels, one per parity; $GG_5(r_{k_0})$ is finite by monotonicity. $\square$

The base levels needed are beyond the certified range (level $\approx1.18$), and the hypothesis is refuted for $k_0=2$ (§6.2).

**Proposition 4.5 (monotone version; proved).** Suppose (M$_5$) $\sim_k\subseteq\sim_{k+2}$ for all $k\ge k_1$, and (L$_5$) the two eventual relations $\sim_\infty^{\rm ev}$, $\sim_\infty^{\rm odd}$ (same class at all large even, resp. odd, levels) have classes of at most $N$ elements. Then every $\sim_k$-class, $k\ge k_1$, has at most $N$ elements, so (R-core-t) holds on lattice points.

*Proof.* As `sharp-lower-bound-n12.md` Proposition 8.1, separately on each parity. $\square$

(M$_5$) is **not** supported for first-return sets, which also shrink (§6.2); whether it holds for orbit partitions is tested in §6.6.

---

## 5. The remaining gap

Assuming nothing, the following are needed for (B) along this route, and none is proved:

1. **The renormalization step**: Conjecture 4.1, or any statement that the return relation at level $k+2$ equals that at level $k$ on a describable domain. It must be proved at the level of return relations (Lemma 3.6).
2. **Internal drift**: Conjecture 4.2 for bounded internal radius. In full generality (all starts) it would by itself bound all word maps at lattice points, hence give finiteness at each level (`sharp-lower-bound-n5.md` Theorem 4.1), so only the bounded-radius form can be an ingredient.
3. **Generic points**: from the domains $\mathcal D_k$ (zoomed internal radius $\le M_k$) to all zoomed core points. The zoomed core contains lattice points of every internal radius. By the box argument of `sharp-lower-bound-n5.md` Theorem 4.3, $\mathcal D_k$ meets every face of the level-$k$ return arrangement in the zoomed core if every face has inradius at least about $16.9/M_k$; no such lower bound is known (question 10 of `../open-problem-critical-radius.md`).
4. **Bases**: finiteness at two consecutive levels from which the induction starts, beyond the certified level $\approx1.18$ (Theorem 4.3 needs $k\ge9$ with the observed $c_0$).
5. **(R-bulk-t)**: restricted closures at $r_c$ for windows at the tight points of every scale. Not addressed here.

Neither (R-bulk-t) nor (R-core-t) is obtained. How the items would combine: items 1–3 would give period two of the tight first-return relation on all zoomed tight-core points from some level $k^\ast$; since the non-tight cores are rigid from level 4 (`sharp-lower-bound-limit-system.md` Theorem 4.2), the orbit relation on the core would then have period two, and Proposition 4.4 with the bases of item 4 gives (R-core-t); with item 5, Theorem 6.1 of the limit-system note gives (B).

---

## 6. Exact computations

All at the tight point $E$ (index 19 in the lexicographic list of the 38 critical points; the other three tight points are symmetric images). Every disk and core test is exact (§2).

### 6.1 Samples and levels

| sample | definition | size | levels computed |
|---|---|---|---|
| $S_E$ | all $\eta$, $|\eta|\le0.3$, $|\sigma\eta|\le50$ (as in the limit-system note) | 811 | 1–4 (all), 5 (random 150, seed 5), closure 1–3 |
| $A_{100}$ | all $\eta$, $50<|\sigma\eta|\le100$ | 2 380 | 1–3; 4 on every 6th point (397) |
| $A_{200}$ | every 4th $\eta$ with $100<|\sigma\eta|\le200$ (of 9 550) | 2 388 | 1–3; 4 on every 6th (398); 5 on 40 of those (random, seed 7) |
| $A_{400}$ | every 16th $\eta$ with $200<|\sigma\eta|\le400$ (of 38 070) | 2 380 | 1–3; 4 on every 6th (397) |

The subsamples are fixed in advance by position in the enumeration order (or by a fixed random seed), not by excursion size. At level 5 an excursion cap of $1.2\cdot10^8$ points ($9\cdot10^7$ on $A_{200}$) was used; capped starts are excluded from the comparisons and counted separately (§6.3). Largest excursions: $7\,674$, $103\,351$, $1\,341\,289$, $18\,097\,966$ points at levels 1–4 (the same maxima on every band), and above $1.2\cdot10^8$ at level 5.

### 6.2 Agreement of first-return sets

**Table 6.1.** Starts whose first-return sets agree between the two levels, out of the starts computed at both; in brackets the changes split as growth ($R_a\subsetneq R_b$) / shrinking / incomparable.

| band | $1\to2$ | $2\to3$ | $3\to4$ | $1\to3$ | $2\to4$ |
|---|---|---|---|---|---|
| $S_E$ | 0/811 | 14/811 | 14/811 | 185/811 (9/379/238) | **518/811** (62/223/8) |
| $A_{100}$ | 0/2380 | 28/2380 | 8/397 | 558/2380 (68/1050/704) | **282/397** (42/63/10) |
| $A_{200}$ | 0/2388 | 38/2388 | 6/398 | 544/2388 (47/1127/670) | **282/398** (24/86/6) |
| $A_{400}$ | 0/2380 | 30/2380 | 4/397 | 559/2380 (53/1076/692) | **271/397** (37/82/7) |

- Consecutive levels essentially never agree, at every internal radius.
- Two levels apart, agreement is about 23% at $1\to3$ and about 70% at $2\to4$ on every band.
- **Unrestricted period two is refuted at $2\to4$**: 293 changes on $S_E$, among them $E$ itself ($\eta=0$: 12 points at level 2, 10 at level 4, the level-2 set being the level-4 set plus two points). The point $\eta=(-3,-1,-1,-3)$ grows from 36 to 46 points.
- **The changes are not monotone.** At $2\to4$ shrinkings outnumber growths on every band (223 vs 62 on $S_E$); a shrinking typically loses 2 or 4 points (157 and 66 cases on $S_E$), a growth gains a whole block of 10 or 34 points (36 and 10 cases). For $n=12$ every change from level 1 on was a growth; for $n=5$ that observation does not transfer.
- 1 566 of the 1 600 lost or gained points on $S_E$ (98%) are non-linear returns ($\eta'\ne\zeta^j\eta$); 17 of the 293 changes on $S_E$ also involve linear returns.

### 6.3 The lune criterion

**Table 6.2.** Lune-free starts at the first level, and how many of them agree at the second.

| band | lune-free at 2, agree $2\to4$ | lune-free at 2, agree $2\to3$ | lune-free at 3, agree $3\to4$ | lune-free at 3, agree $3\to5$ |
|---|---|---|---|---|
| $S_E$ | **124/124** | 0/124 | 14/244 | **44/44** (random 150, 83 uncapped) |
| $A_{100}$ | **61/61** (sub-sample) | 0/344 | 8/109 | |
| $A_{200}$ | **56/56** | 0/361 | 6/118 | **10/10** (random 40 of the sub-sample, 24 uncapped) |
| $A_{400}$ | **54/54** | 0/325 | 3/108 | |

- **No lune-free start changes two levels later**: 349 cases (295 at $k=2$, 54 at $k=3$), on four bands of internal radius up to 400, no failure. The same starts mostly change one level later (0 of 124, 344, 361, 325 agree at $2\to3$).
- **Every change two levels apart has a lune** in the level-$k$ excursion: 293/293, 115/115, 116/116, 126/126 at $2\to4$.
- The converse fails: of the 107 starts computed uncapped at level 5, 53 had lunes at level 3 and still agree at $3\to5$; at $2\to4$ likewise most starts with lunes agree (394 of 687 on $S_E$).
- **Lune-freeness persisted** from level 2 to level 4 in every case (124/124, 61/61, 56/56, 54/54) and from level 3 to level 5 (44/44, 10/10).
- **Level 5.** Excursions at level 5 reach $1.2\cdot10^8$ points and more, so the level-5 test is limited and **selected by size**. On the random 150 starts of $S_E$ (cap $1.2\cdot10^8$), 83 are uncapped; on 40 random starts of the $A_{200}$ sub-sample (cap $9\cdot10^7$), 24.
  - $3\to5$: **83/83** and **24/24** of the uncapped starts agree, lune-free or not; $4\to5$: 0/83 and 0/24; $1\to5$: 36/83 and 7/24.
  - The selection is not neutral. The capped starts of $S_E$ agreed at $1\to3$ in 0 of 67 cases against 36 of 83 uncapped, and had on average 10.0 lune points at level 3 against 2.6. So "3→5 agrees on all computed points" says that the *small* excursions are period-two stable; the starts with the largest level-5 excursions, which are exactly those with many lunes at level 3, were not tested. Of the starts lune-free at level 3, 7 of 51 ($S_E$) and 1 of 11 ($A_{200}$) were capped.
  - The largest uncapped level-5 excursion has $7.8\cdot10^7$ points; mean lune count at level 5 on the uncapped starts is $0.22$.

### 6.4 Statistics independent of the internal radius; lune decay; internal drift

- Lune-free fractions are $0$, $\approx14\%$, $\approx27$–$30\%$, $\approx67$–$70\%$ at levels 1–4 on every band ($S_E$: 0, 124, 244, 571 of 811; $A_{100}$: 0, 344, 653 of 2 380, 272 of 397 at level 4; $A_{200}$: 0, 361, 618 of 2 388, 265 of 398; $A_{400}$: 0, 325, 647 of 2 380, 266 of 397).
- The mean number of lune points per excursion on $S_E$ is $94.0$, $18.3$, $6.54$, $1.04$ at levels 1–4 (ratios $0.19$, $0.36$, $0.16$; $\varepsilon=0.236$).
- The mean number of excursion points within zoomed distance 3 of a critical point is $2\,900$, $6\,782$, $5\,115$ at levels 1–3 (maximum $13\,584$); for $E$ itself $1\,732$ at level 5. It does not grow, although excursions grow by a factor of about 13.5 per level (medians $2\,254$, $32\,783$, $436\,912$, $5\,761\,134$).
- **Internal drift** (evidence for Conjecture 4.2): the largest value of $\max_z|\sigma z|/\varphi^{3k}-|\sigma\eta|$ over the excursions of $S_E$ is $46.8$, $47.1$, $47.1$, $47.2$ at levels 1–4, and the same ($46.8$–$47.1$) on $A_{100},A_{200},A_{400}$ at levels 1–3. With $|\sigma E|\le2.53$ this gives $c_0\le48$ on all data.
- Agreement rates, lune-free rates and excursion maxima coincide across the bands to within sampling noise. Lemma 3.5 explains this: at these levels the arithmetic does not exclude lunes at any internal radius, and a start with large $|\sigma\eta|$ behaves like a generic point of the zoomed core. The internal radius of a start becomes relevant only from level 6 on.

### 6.5 The point $E$ itself

The first-return sets of $\eta=0$ have 10, 12, 10, 10, 10 points at levels 1–5 (excursions $1\,713$, $21\,091$, $258\,837$, $3\,681\,037$, $49\,301\,326$; lune counts 42, 10, 8, 0, 0; at level 6 the excursion exceeds the cap of $1.8\cdot10^8$ points). Exactly:
- $R_1=R_3=R_5=:A$, a set of 10 zoomed points at $E$ and at $\bar E$ (index 7);
- $R_4=-A$ (every zoomed coordinate negated), and $R_2=-A\cup\{(8,(-10,-4,-4,-10)),(20,(-6,4,-6,0))\}$, two returns to non-tight cores, absent from level 3 on.

So at $E$ itself the returns are renormalized with period **one** by the unit $-\varepsilon$ from level 3 on: the return defects $\tau=\varepsilon^{-k}(g(E)-Q')$ satisfy $\tau_{k+1}=-\tau_k$. This is not predicted by Proposition 3.3, whose internal condition excludes every odd period when cuts are matched with cuts. It is a direct instance of Lemma 3.6: returns can match where no cut matches. For general $\eta$ the unit $-\varepsilon$ fails (34, 64, 80 of 811 at $1\to2$, $2\to3$, $3\to4$, comparing $R_{k+1}(-\eta)$ with $-R_k(\eta)$), as Proposition 3.3(1) predicts for $\eta$ away from the strip $0<\lambda<2$.

### 6.6 Orbit partitions

Closure mode on $S_E$: the core orbit sets (orbits intersected with all 38 cores) form 154, 150, 148 distinct blocks at levels 1, 2, 3, with at most 1 936, 1 406, 1 582 core points. Agreement of the core orbit set of a start: $0/811$ ($1\to2$), $14/811$ ($2\to3$), $124/811$ ($1\to3$; changes 6 growths, 534 shrinkings, 147 incomparable). The partition at level 4 was not computed (a level-4 closure needs the first returns of several hundred tight core points per orbit, each with up to $1.8\cdot10^7$ points). So (M$_5$) of Proposition 4.5 is not supported at $1\to3$; level 1 is pre-asymptotic for first returns as well (no start is lune-free there), and the test that matters, $2\to4$ on partitions, remains to be done.

---

## 7. Reproduction

Programs (scratch, not committed): `fr5.c` (`cc -O2 -o fr5 fr5.c -lm`; `fr5 ret k cap log2slots < starts` first returns, `fr5 clo …` orbit partitions, `fr5 orb …` full orbits; starts are lines `19 e0 e1 e2 e3`; `fr5b.c` is the same program with a counter of excursion points within zoomed distance 3 of a critical point, used for §6.4 and for the levels 5–6 runs at $E$), `gen5.c` (`gen5 19 M1 M2 [every]`: the samples), `cmp.py`, `anal.py`, `blocks.py` (comparisons). The repository engine was used read-only for the orbit-size cross-check of §2.
