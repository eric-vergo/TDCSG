# Towards the sharp lower bound for $GG_{12}$: window reduction, rigidity, and the period-one renormalization tested to level five

Authors: Eric Vergo, Claude

**Status.** Let $r_c=\sqrt{40-22\sqrt3}\approx1.376547$. Infinitude of $GG_{12}(r)$ for $r\ge r_c$ is proved and Lean-checked (`critical-radius-n12.md`, Theorem A). **The converse (B₁₂), finiteness of $GG_{12}(r)$ for every $r<r_c$, is still open, so $r_{\rm crit}(12)=\sqrt{40-22\sqrt3}$ is not proved by this note.** Finiteness is certified for $r^2\le r_c^2-1/180$ (`../certificates.md`), which covers the levels $m=0,1,2$ defined below. The note does the following.

1. **Proved (with exact finite computations that I ran): the set-up for $n=12$.**
   - There are exactly 24 lattice vectors of norm $r_c^2$ and 48 critical points in 12 classes. None lies on both circles, and tangencies occur only at critical points (Lemmas 2.1, 2.2).
   - Exactly **8 critical points are tight**, in two classes, $\{\pm p^\ast,\pm\bar p^\ast\}$ and $\{\pm P_4,\pm\bar P_4\}$ with $P_4=-5+3\zeta+5\zeta^2-5\zeta^3$. The other 40 are **rigid from level 0 on**, for every point and not only for lattice points (Theorem 5.1).
   - At every level $r_m^2=r_c^2-\varepsilon^m/10$, no lattice point lies on a lattice-centred circle of radius $r_m$, and no two such circles are tangent. In the field sense of the non-norm lemma (no triple points), the levels $m=0,4,5$ and all $m\ge6$ are non-norm radii; **$m=1,2,3$ are norms from $\mathbb Q(\zeta_{12})$** (Lemma 3.1).
2. **Certified (engine generator and independent float-free checker, run by me): the bulk is bounded uniformly in $r$.** Restricted closures exist at $r_c$ with windows about all 48 critical points, for window circumradii $0.0915$, $0.0358$ and $0.0197$ (all three VALID). Hence **for every $r<r_c$, $GG_{12}(r)$ is finite if and only if its orbits meet the 48 windows in uniformly boundedly many points** (Corollary 4.2). With the rigidity theorem, (B₁₂) follows from two statements about the 8 tight points (Theorem 5.4).
3. **Proved: the exact zoomed arithmetic** that an inductive step needs.
   - The tight-test identity and the transfer of tight tests between consecutive levels (Lemma 6.1).
   - The lune lemma for $n=12$, with the explicit constant $20|\sigma'w|=176.75$ (Lemma 6.2).
   - The absence of any parity obstruction: $\operatorname{sign}(\sigma'\tilde\delta-1)$ does not depend on the level (Lemma 6.3).
   - The **frozen-point lemma** (Lemma 3.3). For $m\ge2$, the level-$m$ system and the strict system at $r_c$ act identically at every lattice point whose internal coordinate is below $\sqrt{78.1+10\varepsilon^{-m}}$.
4. **Refuted (exact): the literal period-one inductive step from level 2 or 3.**
   - The referee's 265/265 agreement holds on its sample, whose internal radius is at most $100$. I reproduced it and extended it to level 5: 184/184 uncapped points agree $4\to5$.
   - On the sample with internal radius at most $300$ (2 413 points at each tight class), the first-return sets **change** between levels $2\to3$ at 49 points and $3\to4$ at 22 points.
   - The orbit partition of the core changes at 28 points between levels $2\to3$, and at 4 of the 1 489 points covered (partial run) between levels $3\to4$.
   - The smallest internal radius of a disagreeing point is $124.5$. Example: $\eta=-45+11\zeta+71\zeta^2-67\zeta^3$ (§7.4). So the exact period-one statement holds only on lattice points of bounded internal radius, from a level that grows with that radius.
5. **Conjecture with exact evidence: eventual period one, by monotone growth, with a lune criterion** (§8).
   - From level 1 on, every observed change is a growth: the earlier first-return set (or core orbit set) is a proper subset of the later one. That is 557 of 557 first-return changes and 32 of 32 partition changes; 0 shrinkings.
   - Every change is preceded by a lune point in the excursion.
   - A point whose level-$m$ excursion is lune-free never changed again: 6 216 cases, 0 failures.
   - The number of core visits per full orbit is **level-independent** on every orbit computed (maximum 224, resp. 280, at levels 0–4).
6. **The remaining gap** (§8.3) is two statements, both conjectural:
   - **(R-core-lim)**: the limit core classes are uniformly bounded, together with monotone growth;
   - **(R-bulk₁₂)**: restricted closures exist at $r_c$ for windows of every scale. Three are computed, down to the core scale of level 1.

   An exact one-step induction of the form envisaged does not exist, because of item 4. The correct inductive object is the monotone limit of item 5.

Terms: *critical, tight, rigid* (§2, §5), *level, zoomed coordinate, core, first-return set, core orbit set* (§3, §7), *lune point, frozen point* (§3, §6), *window, restricted closure* (§4).

---

## 1. Setting

- $\zeta=e^{2\pi i/12}$, $\zeta^4=\zeta^2-1$, and $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$.
- For $c=\sum c_j\zeta^j$: $|c|^2=A+B\sqrt3$ with $A=\sum c_j^2+c_0c_2+c_1c_3$ and $B=c_0c_1+c_1c_2+c_2c_3$.
- $K=\mathbb Q(\sqrt3)$ is the real subfield, and $\Lambda\cap\mathbb R=\mathbb Z[\sqrt3]$.
- The internal embedding is $\sigma'\colon\zeta\mapsto\zeta^5$. It restricts to $\sqrt3\mapsto-\sqrt3$ on $K$ and commutes with complex conjugation, so $|\sigma'c|^2=A-B\sqrt3$.
- $\varepsilon=2-\sqrt3$ has $\sigma'\varepsilon=2+\sqrt3=\varepsilon^{-1}>0$. It is **totally positive**, with norm $+1$.
- $D_1,D_2$ are the closed disks of radius $r$ about $\mp1$; $a,b$ rotate by $-2\pi/12$ about $\mp1$ on their disks and are the identity elsewhere.
- $r_c^2=40-22\sqrt3$ and $\sigma'(r_c^2)=40+22\sqrt3=78.1051$.
- $p^\ast=-2\zeta+4\zeta^2-3\zeta^3=(2-\sqrt3)(1-2i)\in\partial D_1(r_c)$.
- For a critical point $Q$ put $\Phi_Q(z)=Q+\varepsilon(z-Q)$. Since $\varepsilon$ is a unit, $\Phi_Q$ is a bijection of $\Lambda$, and $\Phi=\Phi_{p^\ast}$.

Refereed facts used:
- orbit and group monotonicity (`boundary-contact.md` Theorems 3.1, 3.4);
- bounded orbits give a finite group (`theorem1-converse.md` Proposition 4.2);
- the relative-certificate theorem and its corollaries (`sharp-lower-bound-combined.md` Theorem 4.2, Corollary 4.3, Proposition 4.4). These were stated for $n=5$, but their proofs are general in $n$ (`../relative-certificates.md` §§2–3 re-reads them for general $n$, with bound $1+20nF$). Windows may sit at any set of critical points (`referee-report-sharp-lower-bound-limit-system.md` §2).

"Exact" below means: every disk test and equality is an integer sign test in $\mathbb Z[\sqrt3]$; floating point only pre-filters, with a safety factor before an exact test, or produces reported margins that are far from the thresholds.

---

## 2. Critical points (proved)

**Lemma 2.1.**
1. The solutions of $|w|^2=r_c^2$, $w\in\Lambda$, are exactly 24 elements: $\zeta^j\pi$ and $\zeta^j\bar\pi$, $j=0,\dots,11$, with $\pi=p^\ast+1$.
2. The lattice points of $\partial D_1(r_c)\cup\partial D_2(r_c)$ are the 48 points $\pm1+w$. None lies on both circles.
3. Under $\{\pm z,\pm\bar z\}$ they form 12 classes of 4 points. The minimal distance between two of them is $\sqrt{52-30\sqrt3}=\sqrt{2\varepsilon^3}=0.19615$.
4. For every critical vector $w$: $|\sigma'w|^2=\sigma'(r_c^2)=78.105$, so $|\sigma'w|=8.8377$.

*Proof.*
1. Factorization: $r_c^2=(\sqrt3-1)^2(7-2\sqrt3)$ (expand), and $N_{K/\mathbb Q}(7-2\sqrt3)=37$.
   - The prime $2$ has $e=2$, $f=2$ in $\mathbb Q(\zeta_{12})$: it ramifies in $\mathbb Q(i)$ and is inert in $\mathbb Q(\sqrt{-3})$. So $\mathfrak P=(1+\sqrt3)\Lambda=(\sqrt3-1)\Lambda$ is prime and $\mathfrak P=\bar{\mathfrak P}$.
   - $37\equiv1\pmod{12}$ splits completely, so $(7-2\sqrt3)\Lambda=\mathfrak q\bar{\mathfrak q}$ with $\mathfrak q\ne\bar{\mathfrak q}$: the decomposition group is trivial, so complex conjugation moves every prime above 37.
   - $\Lambda$ is a principal ideal domain. If $w\bar w=r_c^2$, then $(w)\in\{\mathfrak P\mathfrak q,\mathfrak P\bar{\mathfrak q}\}$, so $w=u\pi$ or $w=u\bar\pi$ with $u\bar u=1$.
   - $\mathbb Q(\zeta)$ is CM, so every conjugate of $u$ has modulus 1, and $u$ is a root of unity (Kronecker). That gives 24 elements.
   - Confirmed by exhaustive search over $[-12,12]^4$ (`rigid.py`) and by the engine's trace-form enumeration (`tdcsg-orbit critical-points -n 12 --r2 closed`).
2. Translate item 1. Exhaustive check: no point satisfies both equations.
3. Exact enumeration (`rigid.py`).
4. $\sigma'$ commutes with complex conjugation. $\square$

**Lemma 2.2 (tangency only at critical points).** A circle of radius $r_c$ about $c\in\Lambda$ is tangent to $\partial D_p(r_c)$ only if $c=p+2w$ with $|w|^2=r_c^2$, and then the point of contact $p+w$ is critical.

*Proof.* Equal radii allow only external tangency, $|c-p|^2=4r_c^2$. Since $(2)=\mathfrak P^2$, $v_{\mathfrak P}(4r_c^2)=4+2=6$, so $v_{\mathfrak P}(c-p)=3$. Hence $(c-p)/2\in\mathfrak P\subset\Lambda$ has norm $r_c^2$. $\square$

The engine reports 5 canonical circles tangent to a boundary circle in each restricted closure of §4, every one with its point of contact at a critical point.

---

## 3. Levels, the certified base, frozen points

**Levels.** Put $\delta_m=\varepsilon^m/10$ and $r_m^2=r_c^2-\delta_m$ ($m\ge0$). This is the phase of the referee's test; `critical-radius-n12.md` §4 uses $\delta_m=r_c^2-|p^\ast+i\varepsilon^m+1|^2$, which has the same ratio $\varepsilon$ asymptotically.

| $m$ | $\delta_m$ | $r_m$ | $r_c-r_m$ | core radius $0.09\varepsilon^m$ | field non-norm |
|---|---|---|---|---|---|
| 0 | 1/10.0 | 1.339732 | 0.036815 | 0.09000 | yes |
| 1 | 1/37.3 | 1.366780 | 0.009767 | 0.02412 | **no** (norm) |
| 2 | 1/139.3 | 1.373937 | 0.002610 | 0.00646 | **no** (norm) |
| 3 | 1/519.8 | 1.375848 | 0.000699 | 0.00173 | **no** (norm) |
| 4 | 1/1939.9 | 1.376360 | 0.000187 | 0.00046 | yes |
| 5 | 1/7240.0 | 1.376497 | 0.000050 | 0.00012 | yes |
| $\ge6$ | | | | | yes ($\sigma'(r_m^2)<0$) |

**The certified base.** The engine certificate at $\delta=1/180$ (`../certificates.md`; $r=1.374528$) gives finiteness for $r^2\le r_c^2-1/180$ by group monotonicity. Since $\delta_2=1/139.3>1/180$, **levels 0, 1, 2 are certified; level 3 is not.** Level 3 needs a certificate at $\delta\le1/520$. The cut set grew by a factor of about 13 in circles from $\delta=1/50$ to $1/180$, one level. Extrapolated, that suggests some $10^7$ circles at level 3, beyond the memory available here; this is an extrapolation, not a measurement.

**Lemma 3.1 (radii).**
1. *(Lattice sense, every $m$.)* No lattice point lies on a circle of radius $r_m$ about a lattice point, and no two such circles are tangent.
2. *(Field sense.)* $r_m^2$ is not of the form $|v|^2$, $v\in\mathbb Q(\zeta)$, for $m\in\{0,4,5\}$ and for all $m\ge6$. For $m=1,2,3$ it is.

*Proof.*
1. $|u|^2\in\mathbb Z[\sqrt3]$ for $u\in\Lambda$, while $r_m^2=r_c^2-\varepsilon^m/10$ and $4r_m^2$ are not in $\mathbb Z[\sqrt3]$, because $\varepsilon^m$ is a unit and $10\nmid\varepsilon^m$, $5\nmid2\varepsilon^m$.
2. $\mathbb Q(\zeta)=K(i)$ is cyclic over $K$, so by the Hasse norm theorem $\rho\in K^\times$ is a norm if and only if the Hilbert symbol $(\rho,-1)_v=1$ at every place $v$ of $K$.
   - Write $\rho_m=\alpha_m/10$ with $\alpha_m=400-220\sqrt3-\varepsilon^m$. Since $10=|3+i|^2$ is a norm, only $\alpha_m$ matters.
   - At an odd prime $\mathfrak l$ with $v_{\mathfrak l}(\alpha_m)$ odd, the symbol is $-1$ exactly when $N\mathfrak l\equiv3\pmod4$. At odd primes with even valuation it is $1$. At a real place it is $-1$ exactly when $\alpha_m$ is negative there. The symbol at the prime above $2$ is fixed by the product formula.
   - $N(\alpha_m)$ is: $14001=3\cdot13\cdot359$ ($m=0$); $14521=13\cdot1117$; $14481=3^2\cdot1609$; $13801=37\cdot373$; $11121=3\cdot11\cdot337$; $1081=23\cdot47$ ($m=5$).
   - For $m=0,4$, the ramified prime $(\sqrt3)$, with residue field $\mathbb F_3$, has odd valuation: non-norm. For $m=5$, the split primes above $23$ and $47$, both $\equiv11\pmod{12}$, have odd valuation: non-norm.
   - For $m=1,2,3$, every odd prime of odd valuation has $N\mathfrak l\equiv1\pmod4$. The valuation at $(\sqrt3)$ is $0$ or $2$, and $\alpha_m$ is totally positive. So all symbols at odd and real places are $1$, hence so is the one at $2$, and $\rho_m$ is a norm.
   - For $m\ge6$, $\sigma'(\rho_m)=78.105-\varepsilon^{-m}/10<0$, which is item 1 of the non-norm lemma (`sharp-lower-bound-n5.md` Lemma 2.2(1); valid for any CM field). $\square$

The referee's report calls these levels "non-norm radii, since $\varepsilon^m/10\notin\mathbb Z[\sqrt3]$". That argument gives item 1 only. Item 1 is all that the lattice computations of §7 need: no disk test at a lattice point is ever a tie. The passage from lattice points to all points (Lemma 3.4) needs item 2, so it is stated for the levels $m\in\{0,4,5\}\cup[6,\infty)$. A phase with all levels non-norm was looked for among $\delta_m=c\,\varepsilon^m$, for ten simple rationals $c$; each fails at some small $m$. By item 2 the levels $m\ge6$ are non-norm for every phase with $\sigma'(c)\ge1/10$.

**Lemma 3.2 (strict chains).** For $r<r_c$, every chain at radius $r$ becomes a strict chain at $r_c$ (each step at a point of the open disk of radius $r_c$) after its trivial steps are deleted (`sharp-lower-bound-combined.md` Lemma 3.3; general $n$).

Call a lattice point $y$ **frozen at level $m$ for $p=\pm1$** if $r_m^2<|y-p|^2<r_c^2$. There the generator about $p$ acts trivially at $r_m$, but would act in the strict system at $r_c$. At every other lattice point the two systems act in the same way. Critical points lie on $\partial D_p(r_c)$, so neither system rotates them about $p$.

**Lemma 3.3 (frozen points have large internal coordinate; proved).** Let $m\ge2$. If $y\in\Lambda$ is frozen at level $m$ for $p$, then
$$|\sigma'(y-p)|^2>\sigma'(r_c^2)+10\varepsilon^{-m}=78.105+10\varepsilon^{-m}.$$
Hence, on lattice points, **the level-$m$ orbit graph is the strict-$r_c$ orbit graph with the edges at frozen points deleted**, and every deleted edge sits at a point of internal radius (about $p$) above $14.7,\ 24.5,\ 44.9,\ 85.6,\ 164.6$ for $m=2,\dots,6$.

*Proof.* $N=r_c^2-|y-p|^2\in\mathbb Z[\sqrt3]$ satisfies $0<N<\varepsilon^m/10$. Its norm is a non-zero integer, so $|\sigma'N|>10\varepsilon^{-m}$. Now $\sigma'N=78.105-|\sigma'(y-p)|^2$. If $\sigma'N>0$, then $\sigma'N\le78.105<10\varepsilon^{-m}$ for $m\ge2$ ($10\varepsilon^{-2}=139.3$), a contradiction. So $\sigma'N<-10\varepsilon^{-m}$. $\square$

So the system at a fixed radius is "strict $r_c$ plus walls". The walls are the frozen points, which recede to infinity in internal space as $m\to\infty$. Since the generating set is symmetric, the level-$m$ graph is a subgraph of the level-$(m+1)$ graph, and both are subgraphs of the strict graph. That is orbit monotonicity on lattice points.

**Lemma 3.4 (lattice points suffice at field-non-norm levels; port of `sharp-lower-bound-n5.md` Theorem 4.1).** Let $r$ be a field-non-norm radius, for example $r_m$ with $m\in\{0,4,5\}\cup[6,\infty)$, and let $U$ be a finite union of open disks. Then
$$\sup_{x\in\mathbb C}|O_r(x)\cap U|=\sup_{y\in\Lambda}|O_r(y)\cap U|,\qquad \sup_x|O_r(x)|=\sup_{y\in\Lambda}|O_r(y)|.$$

*Proof.* Take finitely many orbit points $g_i(x)\in U$, $g_i$ the germs of words $w_i$. The arrangement of the test circles of $w_1,\dots,w_k$ is simple at a field-non-norm radius (Corollary 2.3 of the $n=5$ note, whose proof uses only that the centres lie in $\mathbb Q(\zeta)$). So a face adjacent to $x$, on the inner side of the at most two circles through $x$, has the itineraries of $x$ along every $w_i$ (Lemma 3.0 there, applied to the finite family).
- For $y$ in that face, close to $x$, the points $g_i(y)$ are distinct and lie in the open set $U$.
- $\Lambda$ is dense, so such a $y$ can be taken in $\Lambda$. $\square$

---

## 4. The bulk at $r_c$: restricted closures for $n=12$ (certified)

Windows are as in §3 of the combined note, for general $n$: for a shape $w\in\Lambda$, $W_0=\bigcap_{v\in\{\pm w,\pm\bar w\}}D(v,r_c)$, placed at all 48 critical points. I ran the repository engine read-only (`tdcsg-orbit certify-relative -n 12 --r2 closed --window w --symmetric` and `check-relative-certificate`). Disjointness of the 48 windows is proved exactly by the engine (1 128 pairs). Every decision of the generator was exact, and there were 0 coincidences.

**Table 4.1.** Restricted closures at $r_c$ for $n=12$. Counts are modulo $\pm z,\pm\bar z$; "in all" is the full count.

| shape $w$ | inradius | circumradius $\rho_W$ | circles | maximal arcs | in all (circles / arcs) | tangent circles | $\max|\sigma'c|$ | generator | checker |
|---|---|---|---|---|---|---|---|---|---|
| $(1,1,-5,5)$ | 0.04594 | 0.09148 | 18 258 | 31 205 | 72 789 / 123 824 | 5 (all at critical points) | 112.5 | 2.3 s, 25 MB | **VALID**, 69 228 (K3) images, 19 s |
| $(-13,10,7,-10)$ | 0.02252 | 0.03585 | 295 845 | 557 540 | 1 182 606 / 2 226 008 | 5 (all at critical points) | 519.5 | 90 s | **VALID**, 1 250 880 images, 400 s |
| $(-11,9,5,-10)$ | 0.01027 | 0.01968 | 387 208 | 1 665 780 | 1 547 506 / 6 651 352 | 5 (all at critical points) | 566.3 | 312 s | **VALID**, 3 744 064 images, 891 s |

SHA-256 of the files (in my scratch directory `sharp12/`): `b37d6a7ca2178b3356c0b45a5dd7c76222eb051268d914fb72eca73f1d195ea7` (row 1), `01de2f8f773ef81e787d197f98bf4099edbc181902d8bc6d6b077f11da07df4d` (row 2), `0cadc53247d2f6a208a5dd5ba198c82040bc85cf909687937334e987c465a64e` (row 3). A parallel run of the same engine, in the scratch directory `relcert/`, closed and checked VALID the shapes $(-6,5,1,-4)$ ($\rho_W=0.0915$), $(-4,4,2,-5)$ ($0.0718$) and $(-5,4,1,-2)$ ($0.0405$), and generated $(-3,1,2,-3)$ ($\rho_W=0.01243$, 4 618 187 circles); I did not check those myself.

**Theorem 4.1 (proved modulo the certified computation, any row of Table 4.1).** Let $W$ be the window set of row 1. There is $\beta_W<\infty$ such that, for every $r<r_c$ and every $x\in\mathbb C$, every chain at radius $r$ from $x$ whose intermediate points avoid $W$ has at most $\beta_W$ distinct endpoints.

*Proof.* Theorem 4.2 of the combined note, for general $n$ (bound $1+20nF=1+240F$), with Lemma 3.2. $\square$

**Corollary 4.2 (window reduction).** For every $r<r_c$ and every $z$, $|O_r(z)|\le\beta_W\max(1,\sup_x|O_r(x)\cap W|)$. Hence $GG_{12}(r)$ is finite if and only if $\sup_x|O_r(x)\cap W|<\infty$. And (B₁₂) holds if and only if this holds at every level $r_m$ (combined note, Corollary 4.3, verbatim).

**Proposition 4.3 (finite word set).** The pseudogroup induced on $W$ by $GG_{12}(r)$ is generated, for every $r<r_c$, by one finite set of itinerary words of length at most $\beta_W+1$, with a finite set of germs independent of $r$ (combined note, Proposition 4.4).

The engine prints $\max|\sigma'c|\cdot\rho_W\approx10$–$19$. So, as for $n=5$, the internal extent of the closure scales like $1/\rho_W$.

---

## 5. Rigidity away from the tight points (proved modulo an exact finite computation)

**Skeleta.** The skeleton $S_P$ of a critical point $P$ is the set of lattice points reached from $P$ by breadth-first search at $r_c$ with closed disks, where critical points other than $P$ are recorded and not expanded. Two independent programs compute it exactly: `skel12.c` (C, `__int128` signs) and `rigid.py` (Python, exact integers, 50-digit margins).

**Table 5.1.** The 12 classes. $C$-margins: (a) $\min\bigl||q-p|-r_c\bigr|$ over non-critical $q\in S_P$, $p=\pm1$; (b) $\min|q-Q|$ over non-critical $q\in S_P$ and critical $Q$; (c) $\bigl||P-p'|-r_c\bigr|$ for the disk $D_{p'}$ not tight at $P$.

| class representative (canonical) | value | other disk | $|S_P|$ | critical endpoints | (a) | (b) | (c) |
|---|---|---|---|---|---|---|---|
| $(-4,2,4,-5)=-\bar p^\ast$; $p^\ast=(0,-2,4,-3)$ | $\mp0.2679\mp0.5359i$ | inside | **infinite** (cap $2\cdot10^6$) | the other 7 tight points and 2 non-tight ones | | | 0.4693 |
| $(-5,3,5,-5)=P_4$ | $0.0981+0.8301i$ | inside | **infinite** (cap $2\cdot10^6$) | the other 7 tight points and 2 non-tight ones | | | 0.1508 |
| $(-3,1,5,-5)$ | $0.3660-0.1699i$ | inside | 14 | 3 | 0.22794 | 0.27740 | 0.7202 |
| nine classes (36 points) | | outside | 3 | 2 ($R_p^{\pm1}P$) | — | — | $\ge0.22794$ |

The 8 tight points are $\pm p^\ast,\pm\bar p^\ast$ (indices 7, 23, 24, 40 in the lexicographic list of `r12n.c`) and $\pm P_4,\pm\bar P_4$ (indices 4, 22, 25, 43). They are joined by linear germs: the excursion of $p^\ast$ itself (zoomed $\eta=0$) returns, at levels $2$–$5$, to the zoomed point $0$ of each of the other seven. This is presumably why every statistic in §7 is identical, count for count, at $p^\ast$ and at $P_4$; that the two core systems are conjugate is not proved.

**Theorem 5.1 (non-tight cores are rigid from level 0).** Let $C=0.09$, $m\ge0$, and let $P$ be one of the 40 non-tight critical points. For every $x\in\overline B(P,C\varepsilon^m)$, lattice point or not, every first return of $x$ to the core $B_m=\bigcup_Q\overline B(Q,C\varepsilon^m)$ at radius $r_m$ is linear, $x\mapsto Q'+\zeta^j(x-P)$. The excursion has at most $|S_P|\le14$ points.

*Proof.* This is the proof of Theorem 4.2 of `sharp-lower-bound-limit-system.md`, verbatim. It needs:
- $r_c-r_m=\delta_m/(r_c+r_m)\le\varepsilon^m/(10(r_c+r_0))<0.0369\,\varepsilon^m$;
- (a) $\ge(C+0.0369)\varepsilon^m=0.1269\,\varepsilon^m$;
- (b) $>2C\varepsilon^m=0.18\,\varepsilon^m$;
- (c) $>0.1269\,\varepsilon^m$.

The table gives (a) $0.2279$, (b) $0.2774$, (c) $\ge0.2279$, so all hold at $m=0$, hence for all $m$. The tight disk at $P$ maps the inside part of the core onto the core of the critical point $R_p^{\pm1}(P)$, and the chain stops there. $\square$

**Corollary 5.2.** For every $m\ge0$ and every orbit $O$ at radius $r_m$: $|O\cap B_m|\le576\max(1,|O\cap B_m^{\rm t}|)$, where $B_m^{\rm t}$ is the core of the 8 tight points and $576=48\cdot12$ bounds a linear class (limit-system note, Corollary 4.3).

**Definitions.**

- **(R-bulk₁₂)**: there are windows $W^{(j)}$ with $\rho_{W^{(j)}}\to0$ and $\beta^\ast(W^{(j)})<\infty$, that is, restricted closures exist at $r_c$.
- **(R-core-t₁₂)**: there are $m_0$ and $N$ with $|O_{r_m}(y)\cap\operatorname{int}B_m^{\rm t}|\le N$ for every $m\ge m_0$ and every lattice point $y$.

**Theorem 5.4 (assembly; proved).** (R-bulk₁₂) and (R-core-t₁₂) imply (B₁₂).

*Proof.*
- Restrict to the field-non-norm levels $m\ge\max(m_0,6)$.
- By Lemma 3.4, the bound of (R-core-t₁₂) holds for every $x\in\mathbb C$.
- By Corollary 5.2 it bounds $|O\cap\operatorname{int}B_m|$; the closed and open cores differ by a null set, which is irrelevant through Lemma 3.4.
- Choose $j$ with $W^{(j)}\subset\operatorname{int}B_m$, and apply Corollary 4.3 of the combined note. Then group monotonicity. $\square$

Instances of (R-bulk₁₂) computed (Table 4.1): $\rho_W=0.0915$, $0.0358$, $0.0197$, and $0.0124$ in the parallel run. A window fits inside the level-$m$ core when $\rho_W\le0.09\,\varepsilon^m$. Row 2 fits at level 0 and row 3 at level 1; nothing yet fits at level 2 ($0.00646$).

---

## 6. The zoomed arithmetic of an inductive step (proved)

Let $Q\in\partial D_p(r_c)$ be critical, $w=Q-p$, and $y=Q+\varepsilon^mY$ with $Y\in\Lambda$ (zoomed coordinate). Put $\lambda_Q(Y)=20\operatorname{Re}(Y\bar w)+1$.

**Lemma 6.1 (tight-test identity and transfer).**
1. $10(|y-p|^2-r_m^2)=\varepsilon^m\bigl(\lambda_Q(Y)+10\varepsilon^m|Y|^2\bigr)$ exactly. Also $\lambda_Q(Y)\in1+10\mathbb Z[\sqrt3]$, so $\lambda_Q(Y)\ne0$.
2. The tight disk test gives the same outcome at $Q+\varepsilon^mY$ (level $m$) and at $Q+\varepsilon^{m+1}Y=\Phi_Q(Q+\varepsilon^mY)$ (level $m+1$), unless $-10\varepsilon^m|Y|^2<\lambda_Q(Y)<-10\varepsilon^{m+1}|Y|^2$.
3. The *lune points* at level $m$ (disk test and tangent half-plane test $\lambda_Q<0$ disagree) are $\{-10\varepsilon^m|Y|^2<\lambda_Q(Y)<0\}$. This set decreases with $m$. Every lune point of a tight disk is a frozen point (§3) when $|Y|^2<\varepsilon^{-m}/10$, in particular when $|Y|\le1$ and $m\ge2$.

*Proof.*
1. Expand $|w+\varepsilon^mY|^2$ using $|w|^2=r_c^2$. Also $2\operatorname{Re}(Y\bar w)=Y\bar w+\bar Yw\in\Lambda\cap\mathbb R=\mathbb Z[\sqrt3]$.
2. The tests are $\lambda+10\varepsilon^m|Y|^2\le0$ and $\lambda+10\varepsilon^{m+1}|Y|^2\le0$. Neither is ever an equality, by Lemma 3.1(1).
3. Frozen means $0<r_c^2-|y-p|^2<\delta_m$, that is $\lambda-1+10\varepsilon^m|Y|^2<0<\lambda+10\varepsilon^m|Y|^2$. A lune point has $\lambda<0$, so the first inequality holds when $10\varepsilon^m|Y|^2<1$. $\square$

**Lemma 6.2 (lune lemma, $n=12$).** If $10\,\varepsilon^m|Y|^2\bigl(176.754\,|\sigma'Y|+1\bigr)<1$, then $Q+\varepsilon^mY$ is not a lune point at level $m$, nor at any level $m'\ge m$. The constant is $20|\sigma'w|=20\sqrt{40+22\sqrt3}$, the same at all 48 critical points.

*Proof.* $\lambda=1+10t$ with $t\in\mathbb Z[\sqrt3]$, so $N(\lambda)=1+10\operatorname{Tr}t+100N(t)\equiv1\pmod{10}$ is non-zero, and $|\lambda|\ge1/|\sigma'\lambda|$. Also $|\sigma'\lambda|\le20|\sigma'Y||\sigma'w|+1$, and Lemma 2.1(4) gives $|\sigma'w|$. If $|\lambda|>10\varepsilon^m|Y|^2$, item 3 of Lemma 6.1 excludes a lune. $\square$

On the referee's sample ($|Y|\le0.09$, $|\sigma'Y|\le100$), Lemma 6.2 guarantees freedom from lunes only from level $m=6$ on ($1432\,\varepsilon^m<1$). The excursions of §7 are lune-free much earlier than this a-priori bound, for most points.

**Lemma 6.3 (no parity obstruction for $n=12$).** For a test of $D_p$ at a far point with base vector $u=h(Q)-p\in\Lambda$, write the zoomed offset as $\tilde\delta_m(u)=10\varepsilon^{-m}(|u|^2-r_c^2)+1$. Then exactly
$$\sigma'\tilde\delta_m(u)-1=10\,\varepsilon^{m}\bigl(|\sigma'u|^2-\sigma'(r_c^2)\bigr),$$
so $\operatorname{sign}(\sigma'\tilde\delta_m-1)=\operatorname{sign}(|\sigma'u|-8.8377)$ for every $m$.

*Proof.* $\sigma'(\varepsilon^{-m})=\varepsilon^m$. $\square$

This is the referee's identity from §3 of `referee-report-sharp-lower-bound-limit-system.md`, transposed. For $n=5$ the factor is $(-\varphi^3)^{-k}$, which alternates in sign; here it is $\varepsilon^m>0$. **So the necessary condition that excludes period one for $n=5$ is absent for $n=12$.** This explains why period one is not excluded. It does not prove it: cuts need not recur for the return relation to recur (§7).

**Proposition 6.4 (what an exact period-one step would give; proved).** Suppose that for some $m_0$ and all $m\ge m_0$ the following holds: **for all zoomed core lattice points** $(Q,\eta),(Q',\eta')$ of the tight cores, $Q+\varepsilon^m\eta$ and $Q'+\varepsilon^m\eta'$ lie in one orbit at $r_m$ if and only if $Q+\varepsilon^{m+1}\eta$ and $Q'+\varepsilon^{m+1}\eta'$ lie in one orbit at $r_{m+1}$.
- Then $N_m:=\sup_y|O_{r_m}(y)\cap\operatorname{int}B_m^{\rm t}|$, taken over lattice points $y$, is constant for $m\ge m_0$.
- Its value is finite as soon as $GG_{12}(r_{m_0})$ is finite.
- Hence (R-core-t₁₂) holds, and with (R-bulk₁₂), so does (B₁₂).

*Proof.* $\eta\mapsto\eta$ is a bijection between the zoomed core lattice points of consecutive levels, since the core is $\overline B(Q,C\varepsilon^m)$ in zoomed units $\overline B(0,C)$. The hypothesis says that it maps core orbit sets onto core orbit sets. If $GG_{12}(r_{m_0})$ is finite, every orbit is finite. $\square$

This is the induction the task envisaged, with base $m_0$. §7 shows that **its hypothesis is false at $m_0=2$ and $m_0=3$**, and in a way that indicates it fails at every $m_0$.

---

## 7. Testing the inductive step (exact computations)

### 7.1 Method and validation

- **Program.** `r12n.c`, the referee's exact excursion engine (in `reflim/`), and my variants `r12m.c` (leaner hash), `r12c.c` (closure mode: full orbits, each core point processed once) and `r12f.c` (frozen-point statistics), all in `sharp12/`.
- **Disk tests.** Every disk test is the exact sign of an element of $\mathbb Z[\sqrt3]$, using `__int128`.
- **Core test.** $10^4|y-Q|^2\le 9^2\varepsilon^{2m}$, decided exactly after a float pre-filter with relative slack $10^{-6}$, far above the rounding error.
- **First-return set** $R_m(Q,\eta)$: the zoomed core points reached from $Q+\varepsilon^m\eta$ by chains at $r_m$ whose intermediate points avoid the core $B_m$ (radius $0.09\varepsilon^m$ about all 48 critical points).
- **Core orbit set**: $O_{r_m}(x)\cap B_m$ in zoomed coordinates.
- **Lune count**: the number of excursion points within zoomed distance 1 of a critical point that are lune points of a tight disk (exact).
- **Validation.**
  - The sample `gen.py 0.09 100 23`, chosen by exact norm tests, equals the referee's 265-point file byte for byte.
  - The referee's level-1 orbit was matched to the repository engine `tdcsg-orbit orbit -n 12`, as reported.
  - Skeleton sizes and margins agree between `skel12.c` and `rigid.py`.
  - The full orbit counts are consistent across the stopping and closure modes.
- **Samples.**
  - $S_{100}$: the referee's 265 points at $p^\ast$, $|\eta|\le0.09$, $|\sigma'\eta|\le100$.
  - $S_{300}$: 2 413 points with $|\sigma'\eta|\le300$ at each of $p^\ast$ and $P_4$ (4 826 starts).
  - $S_{\rm ann}$: 300 random points (seed 12) of the 14 676 with $300<|\sigma'\eta|\le800$ at $p^\ast$.

### 7.2 First-return sets

**Table 7.1.** Agreement of first-return sets $R_m=R_{m+1}$ (uncapped starts). Results at $p^\ast$ and $P_4$ are identical, count for count, so the $S_{300}$ counts are for one class.

| sample | $0\to1$ | $1\to2$ | $2\to3$ | $3\to4$ | $4\to5$ |
|---|---|---|---|---|---|
| $S_{100}$ (265) | 134 | 233 | **265** | **265** | **184/184** (81 capped at $4.4\cdot10^7$) |
| $S_{300}$ (2 413) | 1 181 | 2 195 | **2 364** | **2 391** | — |
| $S_{\rm ann}$ (300) | — | — | — | **299** | — |

Median excursion sizes on $S_{100}$: 332, 3 382, 31 406, 284 116, 2 581 034 and $2.35\cdot10^7$ at levels 0–5, a factor of about 9 per level. At level 5, 70 of the 184 uncapped starts have a non-linear return (560 non-linear returns). So the agreement $4\to5$ is not rigidity.

**Smallest internal radius of a disagreeing point**, $m\to m+1$: $13.9$, $26.9$, $124.5$, $142.7$ for $m=0,1,2,3$.

### 7.3 Orbit partitions of the core

**Table 7.2.** Closure mode (full orbits). A point *agrees* if its orbit block (its core orbit set intersected with the sample) is the same at both levels.

| sample | orbits per level | max core visits per orbit, levels 0,1,2,3,4 | $0\to1$ | $1\to2$ | $2\to3$ | $3\to4$ |
|---|---|---|---|---|---|---|
| $S_{100}$ | 136, 171, 165, 165, 165 | 280, 280, 280, 280, 280 | 187/265 | 253/265 | **265/265** | **265/265** |
| $S_{300}$ | 1 464 ($m=2$), 1 451 ($m=3$) | 280 ($m=2,3$) | | | **2 385/2 413** (1 438/1 464 blocks) | **1 485/1 489** (partial: 934 level-4 orbits, max 280 core visits) |

The 28 points that change between levels $2\to3$ on $S_{300}$ all **merge**: the level-2 core orbit set is a proper subset of the level-3 one (28 of 28), for example of size $8\to16$, $8\to24$, $16\to24$, $8\to38$, $30\to38$. The smallest internal radius among them is $124.5$.

Full orbits of 30 points of $S_{100}$ (every ninth) at levels 0–3, and 10 of them at level 4:
- orbit sizes about 2 550, 23 000, 209 000, $1.9\cdot10^6$, $1.7\cdot10^7$ (a factor of about 9 per level);
- the number of core visits per orbit has **the same distribution at levels 1, 2, 3**: $\{8^{13},30^5,38^2,168^1,224^9\}$ at level 1, and $\{8^{13},30^4,38^3,168,224^9\}$ at levels 2 and 3;
- at level 4 it is consistent with this ($8^4,30,38,168,224^3$ on 10 orbits).

### 7.4 The counterexamples (exact)

1. **Orbit partition, $2\to3$.** Take $\eta=-45+11\zeta+71\zeta^2-67\zeta^3$ at $p^\ast$, with $|\eta|=0.0290$ and $|\sigma'\eta|=124.5$.
   - At level 2 the core orbit set of $p^\ast+\varepsilon^2\eta$ has 8 points; at level 3 that of $p^\ast+\varepsilon^3\eta$ has 16, containing the 8.
   - First-return sets: 8 points (excursion 27 456) at level 2, 16 points (excursion 284 494) at level 3.
   - Its level-2 excursion contains 10 lune points; the level-3 one contains 6.
2. **First-return set, $3\to4$.** Take $\eta=-75+48\zeta+67\zeta^2-82\zeta^3$, with $|\eta|=0.0732$ and $|\sigma'\eta|=142.7$.

   | level | 0 | 1 | 2 | 3 | 4 |
   |---|---|---|---|---|---|
   | excursion size | 332 | 3 830 | 35 416 | 319 222 | 9 749 672 |
   | first-return set | 16 | 16 | 16 | 16 | 48 |
   | lune count | 56 | 26 | 2 | 2 | 0 |

   $R_3\subsetneq R_4$. Its full orbit, however, has the **same** core orbit set at levels 2, 3, 4 (224 core visits; orbit sizes 202 346, 1 837 436, 16 605 922). Here the level-4 first returns are shortcuts through points that at level 3 were core visits.

So changes of first-return sets and changes of orbit partitions are different events. The first are more frequent; Proposition 6.4 needs only the second. Both occur between levels 2 and 3. Every change is a growth, preceded by a lune at the earlier level.

### 7.5 The lune criterion and monotone growth

Over all comparisons made:

- **Lune-free implies no change.** If the level-$m$ excursion has no lune point (zoomed distance $\le1$), then $R_m=R_{m+1}$. The cases are:
  - $1\to2$: 1 258 of 1 258 ($S_{300}$, both classes);
  - $2\to3$: 2 678 of 2 678;
  - $3\to4$: 1 881 of 1 881 ($S_{300}$, $p^\ast$) and 217 of 217 ($S_{\rm ann}$);
  - $4\to5$: 182 of 182 ($S_{100}$).

  That is 6 216 cases with no failure. Conversely, all 2 464 + 436 + 98 + 22 + 1 changes have a lune point at the earlier level.
- **Lune-freeness persists.** No point that is lune-free at level $m\in\{1,2\}$ has a lune at $m+1$.
- **Changes stabilize.** All 49 points of $S_{300}$ at $p^\ast$ that change between $2\to3$ agree between $3\to4$. Of the 436 that change between $1\to2$, 412 agree between $2\to3$.
- **Monotone growth from level 1.** Every change of a first-return set at $1\to2$, $2\to3$, $3\to4$ is a strict growth: $R_m\subsetneq R_{m+1}$ in 436, 98, 22 and 1 of 436, 98, 22 and 1 cases. At $0\to1$ there are also shrinkings (1 556) and incomparable changes (92); level 0 is pre-asymptotic. Every change of an orbit block is a merge (28 of 28 at $2\to3$, 4 of 4 at $3\to4$).

**Why growth is expected (heuristic, not a proof).** By Lemma 6.1(3) the tight disk $D_p(r_m)$ lies inside its tangent half-plane $\{\lambda_Q<0\}$ near $Q$. So a lune point is a point where the level-$m$ system *does not rotate* but the straight-cut limit would. Lunes only delete edges, relative to the limit. As $m$ grows the lunes shrink (Lemma 6.1(3)), and edges come back. Away from the critical points the level-$m$ system deletes edges only at frozen points (Lemma 3.3), which the excursions do not reach far from the critical points (§7.6).

### 7.6 Where the level dependence lives: frozen hits

`r12f.c` records every excursion point that is frozen for a generator, and its distance to the nearest critical point.

| level | starts | frozen hits | max distance to nearest critical point (zoomed / physical) |
|---|---|---|---|
| 2 | 2 413 ($S_{300}$) | 133 764 | 2.62 / 0.188 |
| 3 | 2 413 ($S_{300}$) | 303 863 | 9.45 / 0.182 |
| 4 | 300 ($S_{\rm ann}$) | 104 615 | 35.3 / 0.182 |

**In every excursion computed (5 126 excursions at levels 2–4), no frozen point farther than $0.19$ from a critical point is visited.** So, in the data, excursions do not touch the frozen strips along $\partial D_p$ away from the critical neighbourhoods; this is not proved. All level dependence of the excursions sits in the frozen strips inside balls of fixed *physical* radius about the critical points. That radius is just below the minimal distance $0.196$ between critical points. In zoomed units it grows like $\varepsilon^{-m}$, so no localization at the zoomed scale holds. This is consistent with Proposition 4.3: everything happens inside fixed macroscopic windows.

### 7.7 Self-similarity of the critical orbit at $r_c$

Let $O(p^\ast)$ be the closed-disk orbit at $r_c$, which is infinite (Theorem A); $2\cdot10^7$ points were explored (`psi12.c`). Test: for $y\in O(p^\ast)$ with $|y-p^\ast|\le\rho$, and internal radius small enough that the image lies well inside the explored region (frontier internal radius 10 343, factor $0.5$), is $\Phi(y)\in O(p^\ast)$?

| $\rho$ | $\Phi=\Phi^1$ (ratio $\varepsilon$) | $\Phi^2$ |
|---|---|---|
| 0.05 | 877/877 | 95/95 |
| 0.10 | 2 153/2 153 | 237/237 |
| 0.14 | **4 149/4 149** | |
| 0.15 | 5 050/5 064 | |
| 0.20 | 8 648/9 024 | 973/1 009 |

Memberships found are exact. The failures are exact non-memberships. The first, at $|y-p^\ast|=0.1415$, is $y-p^\ast=-740+738\zeta+202\zeta^2-544\zeta^3$. The images of three tested failures, for example $p^\ast+\varepsilon\cdot(232-208\zeta-104\zeta^2+194\zeta^3)$, have **finite** orbits of 432 points at $r_c$ (repository engine, `orbit -n 12 --r2 closed`), so they are not in the infinite orbit $O(p^\ast)$. The larger cap $6\cdot10^7$ gives the same failures. So **near $p^\ast$, within distance $0.14$, the critical orbit is invariant under the period-one homothety $\Phi$**, and the invariance is local: it fails from $0.1415$ on. Compare $n=5$, where $\varphi^{-3}$ fails 22% of the time and only $\varphi^{-6}$ holds (limit-system note §5.3). This is the two-dimensional analogue, at $r_c$, of the Lean-proved one-dimensional closure (Lemma 2.3 of `critical-radius-n12.md`), as evidence; it is not proved.

---

## 8. The inductive step: what is refuted, what is conjectured, the gap

### 8.1 Refuted

**The hypothesis of Proposition 6.4 fails at $m_0=2$ and $m_0=3$ (orbit partitions; 28 points of $S_{300}$ at $2\to3$, 4 points at $3\to4$ with internal radius $\ge246.4$), and the first-return version fails at $m_0=2,3$ (49 and 22 points).** The failures are exact, by an engine whose arithmetic is exact and which was validated as in §7.1. In both cases the onset is at internal radius $\ge124.5$. The referee's sample ($\le100$) shows no failure from level 2 on, up to level 5.

Exact period one therefore holds **only on lattice points of bounded internal radius**, from a level that grows with the radius. The onset radii $13.9$, $26.9$, $124.5$, $142.7$ grow, and disagreements thin out (1 232, 218, 49, 22 on $S_{300}$), but on every tested pair some point with larger internal radius still changes. Lemma 6.2 explains the mechanism: a point is protected from lunes once $\varepsilon^m|Y|^2|\sigma'Y|\lesssim1/1768$ along its excursion, and the zoomed core contains points of every internal radius. No single $m_0$ protects all of them. Since the hypothesis of Proposition 6.4 quantifies over all zoomed core lattice points, I expect it to fail at every $m_0$ (conjecture; not tested beyond level 4).

In the terms of the task's step 2(ii): the lattice points that violate the inductive step are exactly the points whose excursion meets a lune of a tight disk, the thin region between the circle and its tangent line (Lemma 6.1(3)). They exist in the window at every level tested, and Lemma 6.2 controls them only for bounded internal radius. Step 2(iii) is confirmed and sharpened: the induced maps do *not* commute with $\Phi$ on all lattice points; the induced *partitions* do on bounded internal radius, and change only by merging.

### 8.2 Conjectures with exact evidence

**Conjecture E₁₂ (eventual period one, lune criterion).** For every zoomed tight-core lattice point $(Q,\eta)$, let $m^\ast(\eta)$ be the first level at which its excursion is lune-free. Then $R_m(Q,\eta)=R_{m^\ast}(Q,\eta)$ for all $m\ge m^\ast$, and likewise for the core orbit set.

Evidence: 6 216 lune-free cases with no change (§7.5); persistence of lune-freeness; every change is preceded by a lune.

**Conjecture M₁₂ (monotone coarsening).** For $m\ge1$ and every zoomed tight-core lattice point, the zoomed core orbit set at level $m$ is contained in the one at level $m+1$.

Evidence: every partition change observed is a merge (32/32), and every first-return change from level 1 on is a growth (557/557).

**Conjecture L₁₂ (bounded limit classes).** There is $N$ with $|\bigcup_m\{\text{zoomed core orbit set of }(Q,\eta)\text{ at level }m\}|\le N$ for every $(Q,\eta)$.

Evidence: the maximum number of core visits per orbit is 280 on $S_{100}$ and $S_{300}$ (levels 0–4 and 2–3), and the distribution of core visits is level-independent on the 30 full orbits (§7.3).

**Proposition 8.1 (proved).** M₁₂ and L₁₂ imply (R-core-t₁₂) with $m_0=1$. Hence M₁₂, L₁₂ and (R-bulk₁₂) imply (B₁₂), so $r_{\rm crit}(12)=\sqrt{40-22\sqrt3}$.

*Proof.* Under M₁₂ the level-$m$ zoomed core orbit set of every lattice point is contained in its limit, which has at most $N$ points by L₁₂. Apply Theorem 5.4. $\square$

Proposition 8.1 replaces the exact one-step induction, which is false, by a monotone limit. The base certificate is then not needed for the core; it is needed only if one wants explicit constants.

### 8.3 The exact remaining gap

(B₁₂) follows (Theorem 5.4, Proposition 8.1) from:

1. **(R-bulk₁₂)**: restricted closures at $r_c$ for windows of every scale, or any other proof that $\beta^\ast(W)<\infty$ along windows shrinking to the critical points. Certified instances: $\rho_W=0.0915$, $0.0358$, $0.0197$ (this note); generated: $0.0124$ (parallel run, not checked by me). They reach the core scale of level 1. Closures grow roughly like $\rho_W^{-1}$ in internal extent. No self-similarity argument reducing the infinite family to finitely many instances is known. The curvature of the circles of radius $r_c$ through the critical points prevents a literal $\Phi$-conjugacy of closures, as for $n=5$.
2. **(R-core-t₁₂)**: uniformly bounded visits to the tight cores, for all lattice points at all large levels. M₁₂ together with L₁₂ suffices. E₁₂ is the mechanism. **None of the three is proved.** The proof would need:
   - (i) a proof that lunes only delete edges *of the return relation*: the observed growth. This is an inclusion between induced relations at different levels, not an inclusion of graphs. Orbit monotonicity in $r$ compares the same points, and $\Phi$ moves points, so it does not give this;
   - (ii) a finite certificate for the limit classes, that is, for the system with straight tangent cuts at the 8 tight points. The limit-system note shows (§5.4 there) that the chain-domain cuts away from the critical points do not form a finite line arrangement. Here §7.6 shows that they are confined to fixed macroscopic balls about the critical points, which is the setting of the relative certificates of §4. A *hybrid* object — the induced pseudogroup on the windows of §4 (finite word set, Proposition 4.3), with its tight tests replaced by tangent half-planes — is the natural limit system. Its construction and the proof that its classes are bounded are not done;
   - (iii) the $r_c$ self-similarity of §7.7, proved instead of tested.

**The base.** Levels 0–2 are certified ($\delta=1/180$). Proposition 6.4 would have needed exactness from $m_0\le2$, which is refuted. Proposition 8.1 needs no base. Level 3 is not certified and appears out of reach of ordinary certificates in this memory budget.

---

## 9. Status and gaps

| claim | status |
|---|---|
| Lemma 2.1 (24 vectors, 48 critical points, 12 classes, minimal distance $\sqrt{2\varepsilon^3}$), Lemma 2.2 (tangency only at critical points) | **proved**; enumerations exact (two programs and the engine) |
| Lemma 3.1 (lattice non-norm at all levels; field non-norm at $m\in\{0,4,5\}\cup[6,\infty)$; norms at $m=1,2,3$) | **proved** (Hasse norm theorem, explicit factorizations) |
| Lemma 3.3 (frozen points), Lemma 3.4 (lattice points suffice at field-non-norm levels) | **proved** |
| Theorem 4.1, Corollary 4.2, Proposition 4.3 (window reduction for $n=12$) | **proved modulo the certified computation** (any row of Table 4.1: engine generator, float-free checker VALID); the theorem used is the combined note's Theorem 4.2 for general $n$, refereed for $n=5$ |
| Theorem 5.1 (40 non-tight points rigid from level 0, all points), Corollary 5.2 | **proved modulo an exact finite computation** (Table 5.1; two independent programs; margins far from the thresholds) |
| Theorem 5.4, Proposition 6.4, Proposition 8.1 (assembly) | **proved** |
| Lemmas 6.1–6.3 (tight-test transfer, lune lemma with constant 176.754, no parity) | **proved** |
| Literal period one (Proposition 6.4's hypothesis) from $m_0=2$ and $m_0=3$; first-return version from $m_0=2,3$ | **refuted** (exact counterexamples, §7.4, Table 7.2) |
| Period one on bounded internal radius: $S_{100}$ $2\to3\to4\to5$ | **computed**, exact; 265, 265, 184/184 |
| Conjectures E₁₂, M₁₂, L₁₂ | **conjectures**, exact evidence §7.5, §7.3 |
| $\Phi$-invariance of $O(p^\ast)$ within $0.14$ of $p^\ast$ at $r_c$ | **computed** (4 149/4 149 exact memberships; exact failures from $0.1415$ on) |
| (R-bulk₁₂) | open; three instances certified by me, one more generated in a parallel run |
| (R-core-t₁₂), (B₁₂), $r_{\rm crit}(12)=\sqrt{40-22\sqrt3}$ | **open** |

**Caveats.**
1. *Not refereed.* The excursion engines are the referee's `r12n.c` and my modifications of it, which change only the hash sizing, the stopping rule and the extra counters. Their results at levels $\le4$ were not re-derived by a second independent implementation. The level-1 orbit match with the repository engine was done by the referee, and the orbits of §7.7 were checked with the repository engine.
2. *Samples.*
   - The tests use lattice points of bounded internal radius ($\le800$) at the two tight classes.
   - Level 5 covers 184 uncapped points of $S_{100}$ only; 81 points exceed $4.4\cdot10^7$ points per excursion.
   - The orbit-partition comparison $3\to4$ on $S_{300}$ is partial (Table 7.2).
   - No test was run at the non-tight points; Theorem 5.1 covers them.
3. *Lune counts* are taken within zoomed distance 1 only; the frozen-hit statistics of §7.6 show that frozen points up to zoomed distance 35 are visited at level 4.
4. *Statistics in floating point.* The physical-distance figures of §7.6 and the window geometry ($\rho_W$) are double precision; they are evidence, not used in any proof. Window disjointness is exact (engine).

---

## 10. What transfers to $n=5,8,10$

- **Lattice versus field non-norm.** Lemma 3.1 shows that "level radii are non-norm" must be checked in the field sense where triple points matter. For $n=5$ this was proved through the prime above $2$ (`sharp-lower-bound-n5.md` Lemma 2.2(3)); for $n=12$ that argument fails, since $v_{\mathfrak P}(r_m^2)=-2$ is even, and three levels are norms. For $n=8,10$ the same Hilbert-symbol computation decides each level.
- **The frozen-point lemma** (Lemma 3.3) holds for every $n$ with $\varphi(n)=4$: replace $\sigma'(r_c^2)$ and $\varepsilon$. For $n=5$: $\sigma(r_c^2)=4-\varphi$, and $\sigma(\varepsilon^k)$ alternates in sign, so the threshold alternates, which matches the parity mechanism of the referee.
- **The lune lemma** with constant $20|\sigma w|$: $30.87$ for $n=5$, $176.75$ for $n=12$.
- **Rigidity** (Theorem 5.1) and the window reduction (§4) transfer verbatim. For $n=8,10$ only the skeleton table and a relative certificate at $r_c$ are needed (the parallel run has $n=8,10$ relative closures in progress).
- **First returns versus orbit partitions.** §7.4 shows that first-return sets can change while orbit partitions do not. The $n=5$ refutation of $\varphi^{-3}$ matching (limit-system note §5.2) was made on first-return sets; that of the combined note (§6.3) on orbit blocks. **The $n=5$ period-two conjecture should be re-tested on orbit partitions, and for monotone growth.** If M and L hold there, Proposition 8.1 needs no parity: monotone coarsening is insensitive to the period.
- **Frozen-hit localization** (§7.6) and the **local $\Phi$-invariance of the critical orbit** (§7.7) are cheap tests that apply to $n=5,8,10$ unchanged. For $n=5$ the latter is known: $\varphi^{-6}$ within distance 1, $\varphi^{-3}$ not.

---

## Appendix A. Data and reproduction

All programs and outputs are in the session scratch directory `sharp12/`; nothing but this note is in the repository.

- `skel12.c` (`cc -O2 -o skel12 skel12.c -lm`; `seq 0 47 | skel12 2000000`) and `rigid.py`: Table 5.1. `z12.py`: exact $\mathbb Z[\zeta_{12}]$ helpers.
- `gen.py C0 R0 idx` and `genann.py C0 R0 idx R1`: exact start samples ($S_{100}$ = `gen.py 0.09 100 23`, identical to the referee's `reflim/s12.txt`; $S_{300}$ = `gen.py 0.09 300 23,4`).
- `r12n.c` (the referee's), `r12m.c`, `r12c.c` (closure mode), `r12f.c` (frozen hits): usage `prog m cap < starts`, output `S idx e0..e3 size lune capped [F bins max]` then `R idx Y0..Y3` per core point. `NOSTOP=1` gives full orbits.
- Comparison scripts: `lf.py` (lune criterion), `cmp.py`, `bad.py`, `cmpart.py` and `partdiff.py` (orbit partitions).
- `psi12.c` (`psi12 0 20000000 rho m 0.5`): §7.7.
- Relative certificates: `n12-w1.rcert`, `n12-w-13,10,7,-10.rcert`, `n12-w-11,9,5,-10.rcert`, with logs `rc_w*.log`, `chk_w*.log`.
- Level indices of the tight points in the list of `r12n.c`: $p^\ast=23$, $P_4=4$, and $7,22,24,25,40,43$.
