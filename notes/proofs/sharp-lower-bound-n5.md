# Towards finiteness of $GG_5(r)$ for all $r<\sqrt{3+\varphi}$: non-norm radii, a lattice window criterion, and a computation at level two

Authors: Eric Vergo, Claude

**Statement and status.** Let $r_c=\sqrt{3+\varphi}\approx2.1489611$ and $r_{\rm crit}(5)=\sup\{r:GG_5(r)\text{ finite}\}$. It is proved (`critical-radius-n5.md`, Theorem A, refereed and Lean-checked) that $GG_5(r)$ is infinite for every $r\ge r_c$. The target is the converse, **(B): $GG_5(r)$ is finite for every $r<r_c$**, which gives $r_{\rm crit}(5)=r_c$. **(B) is proved by a different argument, in [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md); this note does not prove it.** Its results below do not depend on that proof. What is new:

1. **Certified range (not new here).** The best certified range is recorded in [`../certificates.md`](../certificates.md). It is generated and independently checked by the repository's exact Lean engine, whose checker uses no floating point. For $n=5$ it gives $GG_5(r)$ finite for $r^2\le3+\varphi-1/55$, that is $r\le2.144727$, $r_c-r\approx0.004235$. That range covers the level-one radius $\delta_1=\varepsilon/10$ ($r_c-r\approx0.0055$) and the radius $\delta_-=(18-11\varphi)/10$ treated below, since $1/55<\delta_-<\delta_1$. The level-one certificate has also been generated directly by the engine and found VALID by its checker, with an arc set identical to this note's (§5.3).
   **Computed, not certified: level two.** A new C program (§5) closes the cut set at the level-two radius $\delta_2=\varepsilon^2/10=(13-8\varphi)/10$ ($r\approx2.147664$, $r_c-r\approx0.0013$): 4.93 million canonical circles, 69.0 million canonical maximal arcs, (C2) and (C4) passed by its own re-check. This is one unrefereed program with floating-point ordering. Its angle error bound is hard-coded, not derived, and no independent program has read the output. It is therefore a computation awaiting certification, not part of what is proved (§5.1).
2. **Proved:** at *non-norm radii* (Definition 2.1; this includes every level $r_k^2=3+\varphi-\varphi^{-3k}/10$) no point of $\mathbb Q(\zeta)$ lies on any circle of radius $r$ about a point of $\mathbb Q(\zeta)$ (Lemma 2.2). Consequently three lattice-centred circles never meet in a point and two are never tangent, and the certificate theorem of `critical-radius-n5.md` simplifies to an equivalence: **at a non-norm radius, $GG_5(r)$ is finite if and only if the cut-set closure terminates.** Conditions (C3) and (C4) hold automatically, and no exact coincidence test is ever needed (Theorem 3.1).
3. **Proved: the lattice window criterion** (Theorem 4.1), the rigorous form of the invariant-window strategy. At a non-norm radius every piece of every group element is already realised at a point of $\mathbb Z[\zeta]$, so $GG_5(r)$ is finite if and only if the translation parts of the word maps at lattice points are bounded in internal space. A bootstrap (Theorem 4.3) reduces this to a *finite* set of lattice orbits, those of the lattice points in an explicit internal window, so finiteness at one radius is equivalent to a finite lattice computation.
4. **Proved: the Diophantine lune lemma** (Lemma 6.1) and the exact local renormalization it implies (Proposition 6.2). It applies asymptotically, from a level $k_0$ that grows with the normalized window: at the computed levels $0$–$2$ its hypothesis holds, in the tested window, only at $P$ itself (§6). Near a tight point $P$, for lattice points in a normalized window, the disk test at level $k$ coincides exactly with a half-plane test, and the substitution $y\mapsto P+\varepsilon(y-P)$, $\varepsilon=\varphi^{-3}$, carries level-$k$ membership to level-$(k+1)$ membership exactly. This is the mechanism that turns asymptotic self-similarity into exact self-similarity, but only for lattice points of bounded normalized internal coordinate.
5. **Computed (exact arithmetic):** the orbit of $0$ at levels $k=0,\dots,3$ (finite, of sizes $1\,433$, $30\,165$, $400\,519$, $5\,673\,561$; the sizes and internal maxima were reproduced exactly by the engine during refereeing). The following are evidence only. Its internal hull is a round disk of radius $\approx6.49/\delta$. Its part near $0$ is exactly nested under $x\mapsto\varepsilon x$. Level-$(k+1)$ orbits near $0$ are exact unions of $\varepsilon$-scaled level-$k$ orbits (§7).

**The certificate form of (B) is one statement** (Corollary 8.1, termination): *for a sequence of non-norm radii $r_j\uparrow r_c$, the closure $K(r_j)$ terminates.* By item 2 and group monotonicity this is equivalent to (B), so it holds, by the proof of (B) in [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md). By this note's own methods it is certified for the levels $k=0,1$ (by the engine certificates of `../certificates.md`) and computed, uncertified, for $k=2$. The renormalization step that would prove it for all $k$ is not found (§8, §9).

Throughout, "verified exactly" means that equalities and signs in $\mathbb Q(\sqrt5)$ are decided with integers. The C programs of §5 also order distinct points along a circle in double precision, guarded at run time by a margin; that ordering is not certified (§5.1).

**Review.** This note has been independently refereed; the report is [`referee-report-sharp-lower-bounds.md`](referee-report-sharp-lower-bounds.md). §10 records its verdicts and what it did not check.

---

## 1. Setting

As in `critical-radius-n5.md` §1:
- $\zeta=e^{2\pi i/5}$, $\varphi=(1+\sqrt5)/2$, $\Lambda=\mathbb Z[\zeta]$.
- $D_1,D_2$ are the closed disks of radius $r$ about $\mp1$.
- $A$ and $B$ are the rotations by $\zeta^{-1}$ about $-1$ and $+1$; $a=A$ on $D_1$ and $a=\mathrm{id}$ elsewhere, and likewise $b$; $GG_5(r)=\langle a,b\rangle$.
- $\sigma$ is the Galois automorphism $\zeta\mapsto\zeta^2$. It restricts to $\sqrt5\mapsto-\sqrt5$ on $\mathbb Q(\varphi)$ and commutes with complex conjugation. The map $x\mapsto(x,\sigma x)$ embeds $\Lambda$ as a lattice in $\mathbb C\times\mathbb C$ (physical $\times$ internal).
- $\varepsilon=\varphi^{-3}=2\varphi-3$, a unit with $\sigma(\varepsilon)=-\varphi^3$ and norm $-1$.
- **Levels:** $r_k^2=3+\varphi-\delta_k$ with $\delta_k=\varepsilon^k/10$.
- **Word maps.** For a word $w$ and a point $z$, $\mu_w(z)$ is the composite $x\mapsto\zeta^jx+t$ of the rotations actually applied to $z$ along $w$. Here $t\in(1-\zeta)\Lambda$. $\mathcal T(r)$ is the set of all word maps (`critical-radius-n5.md`, Lemma 4.1).
- **Cut set.** $K(r)$ is the closure of $\partial D_1\cup\partial D_2$ under $A^{\pm1}$ on $D_1$ and $B^{\pm1}$ on $D_2$. The certificate theorem (`critical-radius-n5.md`, Theorem 4.2) says: a finite union of radius-$r$ arcs satisfying (C1)–(C4) forces $GG_5(r)$ finite.
- **Monotonicity** (`boundary-contact.md`, Theorems 3.1 and 3.4, refereed). Orbits increase with $r$, and finiteness of the group at $r$ implies finiteness at every $r'\le r$. So (B) is equivalent to finiteness along any sequence $r_j\uparrow r_c$.
- **Bounded orbits** (`theorem1-converse.md`, Proposition 4.2). A finitely generated group of bijections with uniformly bounded orbits is finite.

---

## 2. Non-norm radii (proved)

**Definition 2.1.** A radius $r$ with $\rho=r^2\in\mathbb Q(\varphi)$ is a *non-norm radius* if $\rho\ne|w|^2$ for every $w\in\mathbb Q(\zeta)$.

**Lemma 2.2 (norm obstruction).** Let $\rho\in\mathbb Q(\varphi)$, $\rho>0$.
1. If $\sigma(\rho)<0$, then $\rho$ is a non-norm radius.
2. If the $2$-adic valuation $v_2(\rho)$ is odd, then $\rho$ is a non-norm radius. Here $(2)$ is prime in $\mathbb Z[\varphi]$ and $v_2$ is its valuation.
3. Every level radius $r_k$ ($k\in\mathbb Z$) is a non-norm radius. So are $r^2=3+\varphi-\delta$ for $\delta=1/10,\ 3/40$ and $\delta_-=(18-11\varphi)/10$.

*Proof.*
1. If $\rho=w\bar w$, then $\sigma(\rho)=\sigma(w)\overline{\sigma(w)}=|\sigma(w)|^2\ge0$, because $\sigma$ commutes with complex conjugation.
2. $\Phi_5=x^4+x^3+x^2+x+1$ is irreducible mod $2$, since $2$ has order $4$ mod $5$. So $\mathbb Z[\zeta]/(2)=\mathbb F_{16}$, and $(2)$ is prime in $\mathbb Z[\zeta]$. Its valuation restricts to $v_2$ on $\mathbb Q(\varphi)$, because $(2)$ is also prime in $\mathbb Z[\varphi]$ and is unramified. Complex conjugation preserves the ideal $(2)$, so $v_2(\bar w)=v_2(w)$. Hence $v_2(w\bar w)=2v_2(w)$ is even.
3. $10\rho_k=30+10\varphi-\varepsilon^k\equiv\varepsilon^k\pmod 2$ is a unit at $2$, and $v_2(10)=1$, so $v_2(\rho_k)=-1$. The same computation gives $10\rho=29+10\varphi$, $40\rho=117+40\varphi$ and $10\rho=12+21\varphi\equiv\varphi\pmod2$ for the other three, hence $v_2(\rho)=-1,-3,-1$. For $\delta_-$ also $\sigma(\rho)=3+\sigma(\varphi)-\sigma(\delta_-)=-0.0979<0$. $\square$

**Corollary 2.3.** Let $r$ be a non-norm radius, and consider circles of radius $r$ with centres in $\mathbb Q(\zeta)$.
1. No point of $\mathbb Q(\zeta)$ lies on such a circle. In particular, no lattice point does.
2. No two distinct such circles are tangent. The point of tangency would be the midpoint of the centres.
3. No three distinct such circles have a common point. The common point would be the circumcentre of the three centres, which lies in $\mathbb Q(\zeta)$.

So at a non-norm radius the arrangement of all lattice-centred circles of radius $r$ is *simple*: every crossing is a transversal crossing of exactly two circles.

**Remark.** At a radius where $4\delta\in\mathbb Z$ the cut-set closure meets a tangency (`critical-radius-n5.md` §4.2; for example $\delta=1$, where $\rho=2+\varphi$ is a norm). That is consistent with the lemma. By item 1 the set of norm radii in $\mathbb Q(\varphi)$ misses every $\rho$ with $\sigma(\rho)<0$. So non-norm radii are available arbitrarily close to $r_c$ from below in many ways, and by monotonicity (B) may be tested on them alone.

---

## 3. The certificate theorem at non-norm radii (proved)

Let $\mathcal F=\mathcal F(r)$ be the family of arcs generated recursively: the two boundary circles, and the non-degenerate components of $R(\gamma\cap D_q)$ for $\gamma\in\mathcal F$, $q=\pm1$ and $R\in\{R_q^{\pm1}\}$, where $R_q$ is the rotation by $\zeta^{-1}$ about $q$. Then $K(r)=\bigcup\mathcal F$.
- $\bigcup\mathcal F\subseteq K(r)$, because $K(r)$ is invariant under $a^{\pm1},b^{\pm1}$ and contains both circles.
- $K(r)\subseteq\bigcup\mathcal F$: following a point of $\partial D_p$ letter by letter, each letter either fixes it or rotates it inside an arc of $\mathcal F$. Degenerate (one-point) components lie on $\partial D_q$, which is already in $\mathcal F$.

**Lemma 3.0 (itineraries have interior).** Let $r$ be a non-norm radius, $z\in\mathbb C$ and $w$ a word. Let $S$ be the set of points $y$ that pass and fail the same disk tests as $z$ along $w$. Then $S$ has non-empty interior and $z\in\overline{\operatorname{int}S}$. For $y\in S$, $\mu_w(y)=\mu_w(z)$, so $\mu_w(z)$ is the isometry by which the element $w$ acts on the open set $\operatorname{int}S$.

*Proof.*
- Along $w$ the $i$-th test is $s_i(z)\in D_{p_i}$, where $s_i$ is the word map of the prefix. That is, $z\in D(c_i,r)$ with $c_i=s_i^{-1}(p_i)\in\Lambda$.
- By induction along $w$, points with the same test results have the same prefix maps, hence the same $c_i$ and the same $\mu_w$.
- Near $z$, the tests that $z$ fails, and those it passes in the interior of a disk, hold on a neighbourhood. The remaining tests come from circles through $z$. By Corollary 2.3 there are at most two, crossing transversally. The intersection of their closed disks contains an open sector with vertex $z$. $\square$

**Theorem 3.1.** Let $r$ be a non-norm radius. The following are equivalent:
1. $GG_5(r)$ is finite;
2. $\mathcal F(r)$ is finite;
3. the closure algorithm of `critical-radius-n5.md` §5.1 terminates.

In that case $K(r)$ is a finite union of arcs satisfying (C1)–(C4).

*Proof.*

(1)⇒(2). An arc of $\mathcal F$ of generation $n$ is the image, under the composite rotation of a word $w$ of length $n$, of a component of the set of $x\in\partial D_p$ at which every letter of $w$ applies. If $GG_5(r)$ is finite, then $\mathcal T(r)$ is finite. Indeed, by Lemma 3.0 every word map is an isometry by which some element $g$ acts on an open set. Each $g$ is a composite of two-piece maps, so the plane is cut into finitely many regions on each of which $g$ is one isometry, and an isometry is determined by its values on an open set. So each of the finitely many elements contributes finitely many word maps. Hence there are finitely many composite maps. Moreover the components have endpoints among the finitely many intersections of $\partial D_p$ with the circles $\operatorname{circle}(s^{-1}(q))$, $s\in\mathcal T(r)$. Hence $\mathcal F$ is finite.

(2)⇒(3). By induction, every stored piece is a sub-arc of an arc of $\mathcal F$ on the same circle, with endpoints among the endpoints of arcs of $\mathcal F$. There are finitely many such sub-arcs, and each is stored at most once.

(3)⇒(1). When the algorithm terminates, the finite union of its pieces is invariant and contains both circles. So it equals $K(r)$, and (C1), (C2) hold. (C3) is Corollary 2.3(2). The work is (C4).

*Claim.* If $\gamma\in\mathcal F$ has centre $c$ and starts (respectively ends) at a point $y$, and $y\in\partial D(e,r)$ for a lattice point $e\neq c$, then $\gamma$ runs into $\operatorname{int}D(e,r)$ at $y$.

The claim is proved by induction on the generation of $\gamma$. The boundary circles have no endpoints. Let $\gamma=R(\gamma'\cap D_q)$ and let $y=R(x)$ be its start, where $x$ is the start of a component of $\gamma'\cap D_q$.
- If $x$ is a clipping point of $\partial D_q$, then $y\in\partial D_q$ and $\gamma\subset D_q$ runs into $\operatorname{int}D_q$. Any further circle $\partial D(e)$ through $y$, with $e\ne q,c$, would make a triple point. That is excluded by Corollary 2.3(3).
- Otherwise $x$ is the start of $\gamma'$, and near $x$ the arc $\gamma'$ lies in $D_q$. If $y\in\partial D(e)$, then $x\in\partial D(R^{-1}e)$ with $R^{-1}e\in\Lambda$. By induction $\gamma'$ runs into $\operatorname{int}D(R^{-1}e)$ at $x$, and $R$ carries this to $\gamma$ running into $\operatorname{int}D(e)$ at $y$.

Ends are treated in the same way. The crossings are transversal by Corollary 2.3(2), so "runs into" is well defined.

*(C4).* Let $\alpha$ be a maximal arc of $K(r)$ on $\operatorname{circle}(c)$, $c\ne p$, starting at $y\in\partial D_p$.
- The arcs of $K(r)$ on $\operatorname{circle}(c)$ are the union of the finitely many stored pieces on that circle. So $y$ is the start of a piece $\pi$.
- $\pi$ is contained in an arc $\gamma\in\mathcal F$ on the same circle (induction, as in (2)⇒(3)). $\gamma$ contains $y$, and nothing of $K(r)$ on that circle precedes $y$, so $\gamma$ starts at $y$.
- By the claim with $e=p$, $\gamma$, and hence $\alpha$, runs into $\operatorname{int}D_p$.

Ends are similar. Now Theorem 4.2 of `critical-radius-n5.md` applies. $\square$

**Consequences for the computation.**
- At a non-norm radius, two distinct endpoint symbols $(e_1,s_1)\ne(e_2,s_2)$ on the same circle are distinct points; otherwise three circles would meet. So the exact coincidence test of `critical-radius-n5.md` §5.1 is provably unnecessary. Every computed run found that, as an observation; here it is a theorem.
- Checking (C4) is still done by the programs, as a consistency test.

---

## 4. The lattice window criterion (proved)

**Theorem 4.1.** Let $r$ be a non-norm radius. Then every word map is realised at a lattice point: $\mathcal T(r)=\mathcal T_\Lambda(r):=\{\mu_w(y):y\in\Lambda,\ w\text{ a word}\}$. Consequently the following are equivalent:
1. $GG_5(r)$ is finite;
2. $\mathcal T(r)$ is finite;
3. there is $R$ such that $|\sigma(t)|\le R$ for every word map $x\mapsto\zeta^jx+t$ realised at a lattice point;
4. the cut-set closure terminates.

*Proof.*
- By Lemma 3.0, $S$ has non-empty interior. Since $\Lambda$ is dense in $\mathbb C$, it contains a lattice point $y$, and $\mu_w(z)=\mu_w(y)$.
- The equivalences: (2)⇒(1) is Lemma 4.1(3) of `critical-radius-n5.md`, and (1)⇒(2) is shown in the proof of Theorem 3.1 (1)⇒(2), via Lemma 3.0. (2)⇔(3) is $\mathcal T=\mathcal T_\Lambda$, the discreteness of $\Lambda$ in $\mathbb C\times\mathbb C$, and $|t|\le2+2r$. (1)⇔(4) is Theorem 3.1. $\square$

**Remark 4.2 (what the window strategy must achieve).** Item 3 is the invariant-window formulation, and it is exact. The window must be *uniform over all lattice points*, including those with huge internal coordinate. Those are, physically, generic points of the plane. So a window argument cannot be confined to the low part of the lattice unless one also knows that every cell of the dynamics contains a low lattice point. The next theorem makes that step rigorous and finite.

**Theorem 4.3 (finite lattice certificate).** Let $r$ be a non-norm radius and $R>0$. Put
$$W_R=\{c\in\Lambda:\ |c|\le 3+2r,\ |\sigma(c)|\le R+1\},$$
a finite set. Let $f(R)>0$ be the smallest inradius of a bounded face of the arrangement of the circles $\operatorname{circle}(c,r)$, $c\in W_R$. Let $\rho_{\rm cov}$ be the covering radius of $\Lambda$ in $\mathbb C\times\mathbb C$ for the norm $\max(|x|,|u|)$. Rounding the coordinates in the basis $1,\zeta,\zeta^2,\zeta^3$, whose four vectors have norm $1$, gives $\rho_{\rm cov}\le2$. Put $C_0=\varphi^3\rho_{\rm cov}^2$ (so $C_0=4\varphi^3\approx16.9$ is admissible) and $M(R)=C_0/f(R)$ and suppose:

> $H(R)$: for every $y\in\Lambda$ with $|y|\le 3r+3$ and $|\sigma(y)|\le M(R)$, every word map at $y$ has $|\sigma(t)|\le R$.

Then $|\sigma(t)|\le R$ for every word map at every point of $\mathbb C$, so $GG_5(r)$ is finite. Conversely, if $GG_5(r)$ is finite then $H(R)$ holds with $R=\max\{|\sigma t|:t\in\mathcal T(r)\}$.

*Proof.* Induction on the length of $w$, at an arbitrary point $z$.
- The prefixes of $w$ have word maps with $|\sigma t|\le R$. So the test centres $c_i$ of $w$ at $z$ satisfy $|\sigma(c_i)|\le R+1$ and $|c_i|\le 3+2r$, that is, $c_i\in W_R$.
- If $z$ passes no test of $w$, then $\mu_w(z)=\mathrm{id}$. Otherwise, as in the proof of Theorem 4.1, some face $F$ of the arrangement of $W_R$ is adjacent to $z$, on the inner side of the at most two circles through $z$. $F$ lies inside a disk that $z$ passes, so it is bounded and lies in $|y|\le3r+3$. No circle of $W_R$ crosses $F$, so every point of $F$ has the same itinerary as $z$ along $w$.
- $F$ contains a disk $B(x_0,f)$, $f=f(R)$. Multiplication by $\varepsilon^{-m}$ is an automorphism of $\Lambda$. It carries $B(x_0,f)\times B(0,M)$ to a box with physical radius $f\varphi^{3m}$ and internal radius $M\varphi^{-3m}$; the product $fM$ is unchanged. Take the least $m$ with $f\varphi^{3m}\ge\rho_{\rm cov}$. Then $f\varphi^{3m}<\varphi^3\rho_{\rm cov}$, so the internal radius exceeds $fM/(\varphi^3\rho_{\rm cov})\ge\rho_{\rm cov}$ when $fM\ge C_0$. A box with both radii at least $\rho_{\rm cov}$ contains a lattice point.
- So $F$ contains a lattice point $y$ with $|\sigma y|\le M(R)$, and $\mu_w(z)=\mu_w(y)$ has $|\sigma t|\le R$ by $H(R)$.
- The converse is immediate. $\square$

**What this gives and does not give.**
- $H(R)$ is a finite computation: finitely many lattice orbits, each tracked with its rotation index $j$, stopped as soon as a displacement exceeds $R$. So Theorem 4.3 is an alternative certificate at one radius.
- It is not practical. Faces of the arrangement of $W_R$ include thin lenses between circles with nearby centres, so $f(R)$ is small. That it is polynomially small in $1/R$ is an unproved expectation. In any case $M(R)$ is far larger than the internal extent $R\approx19/\delta$ of the actual cut set (Table 5.1).
- It does not give (B). It turns (B) into "$H(R_k)$ for every level $k$", which still needs an induction on $k$.

---

## 5. Closure computations to level two (computed; certified ranges are in `../certificates.md`)

### 5.1 The computation

**Programs** (all in the session scratch directory `sharp5/`, not in the repository):
- `kcut.c` is a new C implementation of the closure of `critical-radius-n5.md` §5.1. It uses the same symbolic endpoints $(e,s)$ and stores *maximal* arcs directly.
- `kcut3.c` is the same program reduced by the symmetry group $\{z,-z,\bar z,-\bar z\}$. The cut set is invariant under this group because $z\mapsto-z$ conjugates $a$ to $b$ and $z\mapsto\bar z$ conjugates $a$ to $a^{-1}$. Only canonical circles are stored, and each stored circle also receives the images of its arcs under its stabiliser. It uses 16-bit coordinates, with an abort if any coordinate exceeds $15\,000$ in absolute value.
- `kcut4.c` is `kcut3.c` with cancellation-free angles (below); it produced the level-two output.
- `refcheck2.py` and `refcheck3.py` run the referee's (C1)–(C4) logic (`cut.py` of `ref4/`, unchanged) with the author's angle function in place of the referee's `theta`. `refcheck3.py` also replaces `covered` by a symmetry-canonicalising version and verifies that the canonical store is invariant under each stabiliser. So the (C1)–(C4) logic is independent of the generator, but the floating-point geometry is shared with it. These are not independent checkers.

**What the computation rests on.**
- Disk and tangency tests are integer sign tests in $\mathbb Z[\varphi]$ (128-bit). Endpoint equality means identical symbols; at non-norm radii this is exact by §3.
- Angles about a circle centre are computed in double precision as $\arg(e-c)+s\cdot\operatorname{atan2}(\sqrt g,\sqrt n)$, with $n=|e-c|^2$ and $g=4\rho-|e-c|^2$ evaluated from their integer coordinates $u+v\varphi$, through the conjugate $u+v\bar\varphi$ when that avoids cancellation.
- In `kcut4.c` also $2\operatorname{Re}d=(2x_0-x_1)+(x_1-x_2-x_3)\varphi$ and $\operatorname{Im}d/\sin72^\circ=(x_1-x_2+x_3)+(x_2-x_3)\varphi$ are evaluated in this way.
- **The per-angle error bound $5\cdot10^{-15}$ of `kcut4.c` is hard-coded, not derived.** It relies on the platform `atan2` and `sqrt` being accurate to about one ulp, which IEEE 754 does not guarantee. The rounding in the derived quantities that are actually compared (the reduction `fmod(th - bth + 2·TWOPI, TWOPI)` and the unrolled offsets `st`, `en`) is not accounted for. The referee estimates the total at about $10^{-14}$. One sort (`qsort` by start offset) compares raw doubles without the guard. The referee argues it is harmless, because stored arcs on a circle are disjoint and longer than the margin, but that argument is not part of a proof.
- **Run-time guard.** Every comparison of two distinct symbols aborts if their computed angles differ by less than $\mathrm{NEAR}=10^{-9}$; this never happened. With any true error below about $5\cdot10^{-10}$ this makes every guarded decision correct. Lemma 2.2 gives no lower bound on the separation of distinct points, so the sufficiency of the margin is observed at run time, not proved.
- In `kcut.c` and `kcut3.c` the error bound is computed per symbol ($4\cdot10^{-16}S/\sqrt n+2\cdot10^{-15}$, with $S$ the coefficient size); the worst value was $8.3\cdot10^{-11}$ up to level one. At level two `kcut3.c` reached $8.7\cdot10^{-10}$, which its own acceptance test ($<\mathrm{NEAR}/10$) rejects. `kcut4.c` gives a byte-identical output there.
- **Consequence.** Termination of the closure certifies finiteness (Theorem 3.1) only if every ordering decision was correct, because a wrong decision can stop the closure at a non-invariant set. The program's own (C2) pass uses the same decisions and cannot detect that. So the level-two result is a computation by one unrefereed program with floating-point ordering. An independent check would need a symmetry-reduced or streaming mode in the engine's checker: unreduced, about $2.8\cdot10^8$ arcs at the engine's measured 0.65–0.8 kB per arc would need of order $10^2$ GB.

**Validation of `kcut.c`.** Its maximal-arc sets are **byte-identical** to the referee's at $\delta=13/5,\ 1/2,\ 9/20,\ 9/10,\ 3/10,\ 1/5,\ 3/20,\ 1/10$. Those sets in turn match the author's at the radii of `critical-radius-n5.md` Table 5.1. It is also byte-identical to a fresh run of the referee's closure at $\delta=3/40$ (352,790 arcs). The symmetric `kcut3.c`, expanded by the symmetry group, is byte-identical to `kcut.c` at $\delta=1/10$ and $1/20$. At level one the canonical parts of the two outputs are identical (1,700,921 lines).

### 5.2 Results

**Table 5.1.** Closure of $K(r)$ at $r^2=3+\varphi-\delta$ by `kcut.c` (full) or `kcut3.c`/`kcut4.c` (symmetric; counts are then of canonical circles and canonical maximal arcs, excluding the inserted copy of $\partial D_2$; arc counts include full circles). These are computations. The certified ranges are those of `../certificates.md` (exact engine, through $\delta=1/55$).
- "Other check" is the referee's (C1)–(C4) logic with the author's angle function (`refcheck2/3.py`), or the exact engine where stated.
- $\max|\sigma(c)|$ is the largest internal modulus of a circle centre.

| $\delta$ | $r$ | $r_c-r$ | non-norm | circles | maximal arcs | pieces | (C4) endpoints / failures | $\max|\sigma(c)|$ | $\delta\max|\sigma c|$ | time, memory | other check |
|---|---|---|---|---|---|---|---|---|---|---|---|
| $1/10$ ($k=0$) | 2.125567 | 0.023394 | yes | 50 714 | 198 470 | 1 437 578 | 7 172 / 0 | 188.3 | 18.8 | 2 s, 31 MB | referee closure identical |
| $3/40$ | 2.131439 | 0.017522 | yes | 105 406 | 352 790 | 2 828 296 | 9 836 / 0 | 309.6 | 23.2 | 4 s, 53 MB | referee closure identical; checker passes |
| $1/20$ | 2.137296 | 0.011665 | no ($\rho$ is a norm, by the Hasse norm theorem) | 190 436 | 833 366 | 7 795 004 | 15 376 / 0 | 363.7 | 18.2 | 11 s, 103 MB | checker passes (C1–C4) |
| $\varepsilon/10$ ($k=1$) | 2.143461 | 0.005500 | yes | 1 007 612 | 6 796 360 | 83 680 776 | 45 680 / 0 | 844.7 | 19.9 | 134 s, 735 MB | `refcheck2.py` passes; **exact engine certificate VALID, arc set identical** (§5.3) |
| $(18-11\varphi)/10$ | 2.144265 | 0.004696 | yes ($\sigma\rho<0$) | 263 330 canonical | 1 906 993 canonical | 24 145 030 (sym.) | 13 314 / 0 | 844.7 | 17.0 | 40 s, 153 MB | `refcheck3.py` passes (its log counts 263 331 circles and 1 906 995 arcs, including the inserted copy of $\partial D_2$); stabiliser invariance holds |
| $\varepsilon^2/10$ ($k=2$) | 2.147664 | 0.001297 | yes | 4 929 752 canonical | 68 989 951 canonical | 1 370 392 834 (sym.) | 95 863 / 0 | 3431.4 | 19.1 | 2 970 s, 5.2 GB | none; `kcut3.c` and `kcut4.c` outputs identical. **Not certified** |

All finished runs: no tangency, no near-coincidence, (C2) re-verified with 0 uncovered images, and (C4) with 0 failures.

**Status of the rows.**
- Every row with $\delta\ge1/55$ lies inside the certified range of `../certificates.md` (exact engine, float-free checker). There these runs are consistent re-derivations and add nothing to what is proved.
- The level-two row is **computed, not certified** (§5.1). If it is certified, then Theorem 3.1 and group monotonicity give $GG_5(r)$ finite for $r\le r_2$, with $r_2^2=(17+18\varphi)/10$ and $r_c-r_2\approx0.0013$.

### 5.3 Recomputation by the referee

- **Level one** was generated by the exact engine (`tdcsg-orbit certify -n 5 --r2 re:41/10,4/5`, that is $r^2=(33+8\varphi)/10$): 1 007 612 circles, 6 796 360 maximal arcs, 0 inexact decisions. `check-certificate` returned VALID. The engine's arc set equals the triples of `kcut.c`'s output exactly. SHA-256 and sizes are in the referee report.
- **`kcut3.c` and `kcut4.c`** give byte-identical outputs at level one and level two.

**Growth.**
- In canonical counts, from level $0$ to $1$ to $2$ the circles grow by factors $19.8$ and $19.6$, the maximal arcs by $34.1$ and $40.6$, and the pieces by $68$ and $71$, while $\delta$ shrinks by $\varphi^3=4.236$ per level.
- At all three levels $\delta\max|\sigma(c)|\approx19$–$20$ ($18.8$, $19.9$, $19.1$), so the internal extent of the centres scales like $\delta^{-1}$, as for the orbit of $0$ (§7).
- The internal image of the centre set is a round disk to within $1\%$ in every one of ten angular sectors ($18.72$–$18.83$ at $k=0$, $19.92$–$19.94$ at $k=1$, after multiplying by $\delta$).
- The extreme centres sit physically at distance $\approx2r$ from a disk centre: circles that barely meet a disk.
- Per level the work grows by a factor of about $70$ and the memory by about $30$. Level three would need roughly $150$ GB with the present data layout (an extrapolation), so a direct computation cannot reach $r_c$.

---

## 6. The Diophantine lune lemma and exact local renormalization (proved)

A *tight point* is a lattice point $P$ with $|P-p|^2=3+\varphi$ for some $p=\pm1$. The tight points visited by the critical words are $\pm E$, $\pm\bar E$ and the lens corners $\pm(\zeta-\zeta^{-1})$ (`critical-radius-n5.md` §3.2). For $y\in\Lambda$ put
$$\ell_P(y)=2\operatorname{Re}\bigl((y-P)\overline{(P-p)}\bigr)\in\mathbb Z[\varphi],\qquad \nu_k(y)=10\,\ell_P(y)+\varepsilon^k\in\mathbb Z[\varphi].$$
Then exactly
$$10\bigl(|y-p|^2-r_k^2\bigr)=\nu_k(y)+10|y-P|^2.\tag{6.1}$$

**Lemma 6.1 (Diophantine margin; thin lunes contain no lattice points).**
1. For every $x\in\Lambda$, $p=\pm1$ and $k\in\mathbb Z$, the number $\mu=10(|x-p|^2-r_k^2)$ lies in $\mathbb Z[\varphi]$, $\mu\equiv\varepsilon^k\pmod{10}$ and $N(\mu)\equiv(-1)^k\pmod{10}$. Hence
$$\bigl||x-p|^2-r_k^2\bigr|\ \ge\ \frac{1}{10\,\bigl(10|\sigma(x)-p|^2+24+\varphi^{3k}\bigr)}.$$
2. (Lune lemma.) If $y\in\Lambda$ satisfies
$$10\,|y-P|^2\,\bigl(20\,|\sigma(y)-\sigma(P)|\,|\sigma(P)-p|+\varphi^{3k}\bigr)<1,$$
then $\nu_k(y)\ne0$ and $y\in D_p(r_k)\iff\nu_k(y)<0$. That is, on such lattice points the disk test equals the half-plane test $\ell_P(y)<-\varepsilon^k/10$: no such lattice point lies in the lune between the circle and its tangent half-plane.

*Proof.*
1. $|x-p|^2\in\mathbb Z[\varphi]$ and $10r_k^2=30+10\varphi-\varepsilon^k$, so $\mu=10m+\varepsilon^k$ with $m\in\mathbb Z[\varphi]$. Then $N(\mu)=N(\varepsilon)^k+10(\cdots)$ with $N(\varepsilon)=-1$. So $|N(\mu)|\ge1$, that is, $|\mu|\ge1/|\sigma(\mu)|$. Finally $|\sigma(\mu)|=|10(|\sigma x-p|^2-3-\sigma\varphi)+\sigma(\varepsilon)^k|\le10|\sigma x-p|^2+24+\varphi^{3k}$.
2. $\nu_k(y)\equiv\varepsilon^k\pmod{10}$, so as in item 1, $|\nu_k(y)|\ge1/|\sigma(\nu_k(y))|$. Since $\sigma$ commutes with $\operatorname{Re}$ and conjugation, $|\sigma\ell_P(y)|\le2|\sigma y-\sigma P||\sigma P-p|$. So $|\nu_k(y)|>10|y-P|^2$, and by (6.1) the two signs agree. $\square$

**Proposition 6.2 (exact local renormalization at a tight point).** Let $\Psi_P(y)=P+\varepsilon(y-P)$, a bijection of $\Lambda$.
1. $\nu_{k+1}(\Psi_Py)=\varepsilon\,\nu_k(y)$, so the half-plane tests of $y$ at level $k$ and of $\Psi_P(y)$ at level $k+1$ agree exactly.
2. If $y$ satisfies the hypothesis of Lemma 6.1(2) at level $k$, then $\Psi_P^m(y)$ satisfies it at level $k+m$ for all $m\ge0$, with left side multiplied by $\varepsilon^m$. Hence $y\in D_p(r_k)\iff\Psi_P^m(y)\in D_p(r_{k+m})$ for all $m\ge0$.
3. In normalized coordinates $y-P=\varepsilon^k\eta$, $\sigma(y-P)=\sigma(\varepsilon)^k\eta'$, the hypothesis reads $10\varepsilon^k|\eta|^2(20|\eta'||\sigma P-p|+1)<1$. For any bounded set of $(\eta,\eta')$ it holds for all $k\ge k_0$, and the membership of $P+\varepsilon^k\eta$ at level $k$ is then the $k$-independent sign of $10\,\ell_P(P+\eta)+1$.
4. Every isometry $g(x)=\zeta^jx+t$ with $t\in\Lambda$ satisfies $g\circ\Psi_P=\Psi_{g(P)}\circ g$.

*Proof.* (1) $\ell_P$ is real-linear in $y-P$ and $\varepsilon$ is real. (2) is (1) plus the scaling of the hypothesis: $|\Psi y-P|^2=\varepsilon^2|y-P|^2$ and $|\sigma\Psi y-\sigma P|=\varphi^3|\sigma y-\sigma P|$. (3) is a rewriting. (4) $g(P+\varepsilon(y-P))=g(P)+\varepsilon\zeta^j(y-P)$. $\square$

**Remark (heuristic, not proved).** Item 4 suggests that a lattice chain shadowing the global-rotation orbit $P_0,P_1,\dots$ of a tight point is carried by $\Psi$ to a chain at the next level. Making this precise needs hypotheses that are not established here. $g(P)$ need not be a tight point. At non-tight $P_i$ the membership must be decided by a margin at both levels $k$ and $k+1$. At tight $P_i$ the lune hypothesis must hold at each step.

**Coverage at small $k$.** For $y\ne P$ the norm bound $|y-P|\,|\sigma(y-P)|\ge1$ makes the hypothesis very restrictive. It forces $|y-P|<1/(200|\sigma P-p|)\approx1/309$ and $|y-P|<\varphi^{-3k/2}/\sqrt{10}$. The referee counted, for one tight pair $(P,p)$, the points $y=P+\varepsilon^k\eta$, $\eta\in[-3,3]^4$ (2 401 points), that satisfy the hypothesis:

| $k$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| points satisfying the hypothesis | 1 | 1 | 1 | 15 | 53 | 171 | 723 | 1 871 |

At $k=0,1,2$ the single point is $y=P$. For $|\eta|,|\sigma\eta|\le1$ the hypothesis holds from $k_0=4$, and for $\le2$ from $k_0=6$. So at the computed levels $0$–$2$ the lemma says nothing beyond $P$ itself. It is untested against the certified data of §5 and §7, and any induction based on it needs its base at level $4$ or deeper.

**Recomputation.** The referee tested 76 832 lattice points $y=P+\varepsilon^k\eta$, $\eta\in[-3,3]^4$, $k=0,\dots,3$, over all eight tight pairs.
- (6.1), $\nu_{k+1}(\Psi y)=\varepsilon\nu_k(y)$ and $N(\mu)\equiv(-1)^k\pmod{10}$ hold on all of them.
- On the 144 points satisfying the hypothesis, membership equals the half-plane test and is carried to levels $k+1$, $k+2$, $k+3$, with 0 failures.
- On 7 624 points outside the hypothesis the two tests disagree, so the hypothesis cannot simply be dropped.

**What this does and does not achieve.**
- It is exactly the step that the asymptotic Conjecture R of `critical-radius-n5.md` §6 lacked: an *exact*, $k$-independent description of the disk tests near the tight points. It needs no curvature estimates, but it holds only for lattice points in a normalized window.
- It does not control the chains that leave the neighbourhoods of the tight-point orbits. The orbit of a tight point under global rotations is not confined: $E$ lies on the critical chord, whose orbit at $r_c$ is infinite.
- By Theorem 4.1 the group needs *all* lattice points, including those whose normalized internal coordinate is large.

---

## 7. The orbit of $0$ at levels $0$–$3$ (exact computation; evidence for renormalization)

Breadth-first search on integer 4-vectors with exact disk tests (`lat.py`).

| $k$ | $\delta_k$ | $|O_{r_k}(0)|$ | $\max|\sigma(x)|$ | $\delta_k\max|\sigma x|$ |
|---|---|---|---|---|
| 0 | 0.1000 | 1 433 | 53.75 | 5.375 |
| 1 | 0.02361 | 30 165 | 273.21 | 6.450 |
| 2 | 0.005573 | 400 519 | 1165.0 | 6.492 |
| 3 | 0.001316 | 5 673 561 | 4933.2 | 6.490 |

The referee reproduced all four sizes and internal maxima exactly with the engine (`tdcsg-orbit orbit -n 5 --start 0`).

**Proved modulo this computation.** By orbit monotonicity, the orbit of $0$ is finite, of size at most $5\,673\,561$, for every $r\le r_3$, where $r_c-r_3\approx3.1\cdot10^{-4}$. So $r^\ast(0)>r_3$ in the notation of `boundary-contact.md`. This is a statement about one orbit, not the group.

**Observations (evidence, exact data).**
1. *Internal hull.* In every one of twenty angular sectors $\delta_k\max|\sigma x|$ lies within $1.6\%$ of $6.49$ at $k=2$: the internal hull of the orbit is a round disk of radius $\approx6.49/\delta$. The maximal internal coordinates occur physically next to the tight points $\pm E$, the lens corners, and points near $\pm(2.21\pm1.2i)$.
2. *Exact nesting of the core.* Put $C_k(c_0)=\varepsilon^{-k}\bigl(O_{r_k}(0)\cap\{|x|\le c_0\varphi^{-3k}\}\bigr)\subset\Lambda$.
   - $C_k(c_0)\subseteq C_{k+1}(c_0)$ for $c_0\le1$ and $k=0,1,2$.
   - The sizes for $c_0=0.2,\,0.4,\,0.7,\,1.0$ are $(9,17,17,17)$, $(41,77,81,89)$, $(93,177,193,209)$, $(165,333,361,385)$ for $k=0,\dots,3$.
   - So the rescaled core grows monotonically, and for $c_0=0.2$ it is already constant from $k=1$.
   - Since $C_k(c_0)$ lies in a bounded window of $\mathbb C\times\mathbb C$ *if* $\max|\sigma x|=O(\varphi^{3k})$ (observation 1), a monotone sequence of such sets must become constant. This would be exact eventual self-similarity of the core, but it rests on the unproved internal bound.
   - Outside $|x|\approx1.1$ the inclusion $\varepsilon O_k\subseteq O_{k+1}$ fails: 460 of the 1 433 points at $k=0$ do not scale into $O_1$, all with $|x|\ge1.19$.
3. *Merging.* $\varepsilon^{-1}\bigl(O_{r_{k+1}}(0)\cap\{|x|\le\varphi^{-3}\}\bigr)$ is **exactly** the union of the parts in $\{|x|\le1\}$ of complete level-$k$ lattice orbits:
   - for $k=0$: the orbit of $0$ (1 433 points), two orbits of 543 and six of 40;
   - for $k=1$: the orbit of $0$ (30 165), four orbits of 590 and one hundred of 40.

   So a level-$(k+1)$ orbit near $0$ is a finite union of rescaled level-$k$ orbits: the equivalence relation "same orbit" on the core at level $k+1$ is *coarser* than the rescaled one at level $k$. This is a substitution, and it is what makes the orbit grow by $\approx13$–$14$ per level.
4. *Bounded distance to a fixed core.* Every point of $O_{r_k}(0)$ is within $3$ letters of $\{|x|\le1\}$ ($k=0,1,2$), within $9$ of $\{|x|\le\tfrac12\}$, and within $9,15,16,16$ ($k=0,\dots,3$) of $\{|x|\le\tfrac14\}$.

These are the lattice analogues of the "exact germ recursion" observed for $n=8$ in `sharp-lower-bound-n8.md` §6, found independently here. For $n=5$ the observed period is one level ($\varepsilon=\varphi^{-3}$).

---

## 8. Termination along the levels

**Corollary 8.1 (termination).** There are non-norm radii $r_j\uparrow r_c$ (for instance the levels $r_k$) such that the closure $K(r_j)$ is a finite union of arcs for every $j$.

**Equivalence.** By Theorem 3.1 and group monotonicity, Corollary 8.1 is *equivalent* to (B). Since (B) is proved ([`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md)), Corollary 8.1 holds. It is Corollary R$^\ast$ of `critical-radius-n5.md` without (C3) and (C4), which hold automatically at non-norm radii. Certified for $k=0,1$ (`../certificates.md`; level one also directly by the engine, §5.3). Computed, not certified, for $k=2$ (§5).

**Equivalent lattice form** (Theorem 4.1). For each $k$ there is $R_k$ with $|\sigma(t)|\le R_k$ for every word map at every lattice point, at radius $r_k$. It holds, with $R_k\le(160\sqrt5+32r_c^2)/\delta_k$, $\delta_k=\varepsilon^k/10$ (Corollary of §4 of [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md); written proof only).

**What a renormalization proof would supply.** In the order a renormalization proof would need them:
1. **(Exact local step)** Proposition 6.2, valid from a level $k_0\ge4$ that grows with the window (§6).
2. **(Substitution)** a finite description of how level-$(k+1)$ orbits are assembled from rescaled level-$k$ orbits. That is a finite set of "merging" excursions, independent of $k$ for $k\ge k_0$, of the kind seen in §7(3).
3. **(Bounded excursions)** a $k$-independent bound on how far a level-$(k+1)$ orbit wanders from the rescaled core before returning. §7(4) suggests it is uniform for a fixed core, but this is evidence only.
4. **(Generic points)** passage from lattice points with bounded normalized internal coordinate to all lattice points. By Theorem 4.3 this is a statement about faces of the circle arrangement. It is the step at which the exactness of Proposition 6.2 is lost, because the low window that Proposition 6.2 controls is much smaller than the window $M(R)$ of Theorem 4.3.

No step beyond 1 is proved here.

---

## 9. Attempts that failed, and why

1. **The full-circle closure.** Replacing arcs by full circles gives an over-approximation $K^{\rm full}$, for which (C4) is vacuous. It is finite only if the orbit of $\pm1$ under the lattice action with disks of radius $2r$ is finite. That orbit is infinite at $\delta=1/10,\,13/5,\,3/2$ (more than $2\cdot10^6$ points, internal modulus over $1\,400$), as expected since $2r>r_c$. Arcs are essential.
2. **A global similarity.** $x\mapsto\varepsilon x$ maps the level-$k$ orbit of $0$ into the level-$(k+1)$ orbit only inside $|x|\lesssim1.1$ (§7(2)). A global affine lattice map cannot conjugate the levels, by the curvature argument of `critical-radius-n5.md` §6.4, and the orbit data confirm this.
3. **A simple polygonal window.** The internal hull is a round disk (§7(1)), but the orbit fills only a fractal part of it (filling fraction decreasing with $k$, `critical-radius-n5.md` §7.1). Theorem 4.1 shows why no small window can work: the window must be uniform over lattice points of every internal size.
4. **The limiting line arrangement near $0$.** Rescaling $K(r_k)$ near $0$ by $\varphi^{3k}$ does not give a sparse line arrangement: already at $k=0$, 1 743 distinct arcs pass within rescaled offset $1.5$ of $0$, in many directions. This agrees with the finding for $n=8$ (`sharp-lower-bound-n8.md` §4) that the cut set has no locally finite scaling limit at a typical point. The renormalizable objects are orbits (pseudogroup germs), not the arc arrangement.

---

## 10. Status and gaps

The verdicts are those of `referee-report-sharp-lower-bounds.md`, after its fixes were applied.

| claim | status |
|---|---|
| Lemma 2.2, Corollary 2.3 (non-norm radii; all levels $r_k$ are non-norm) | **proved**; refereed correct |
| Lemma 3.0, Theorem 3.1: at non-norm radii, finite group $\iff$ closure terminates; (C3), (C4) automatic | **proved**; refereed correct after minor fixes (the direction finite group ⇒ $\mathcal T$ finite now goes through Lemma 3.0) |
| Theorem 4.1 (lattice window criterion), Theorem 4.3 (finite lattice certificate, $C_0=\varphi^3\rho_{\rm cov}^2$) | **proved**; refereed correct (explicit $C_0$ added after the report, not yet refereed) |
| Lemma 6.1, Proposition 6.2(1)–(4) | **proved**; refereed correct and tested on 76 832 lattice points. Applies only from a level $k_0\ge4$ (§6). The shadowing remark after it is heuristic |
| Finiteness for $r^2\le3+\varphi-1/55$ (covers levels $0,1$ and $\delta_-$) | **proved modulo the exact engine certificates** of `../certificates.md`; level one also certified directly by the referee with the engine |
| Level two ($r\le r_2$, $r_c-r_2\approx0.0013$) | **computed, not certified**: one C program, hard-coded error bound, no independent check |
| Orbit of $0$ finite for $r\le r_3$ ($r_c-r_3\approx3.1\cdot10^{-4}$) | **proved modulo an exact BFS**; sizes and internal maxima reproduced exactly by the engine |
| §5.2 growth data, §7 observations 1–4 | computed, exact; evidence only; not checked by the referee beyond the orbit sizes |
| Corollary 8.1 (termination) $\iff$ (B) $\iff$ $r_{\rm crit}(5)=\sqrt{3+\varphi}$ | **holds**, since (B) is proved in [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md); the equivalence is refereed correct (a reformulation, not a reduction to an easier statement) |

**Not checked by the referee:**
- level two by any independent program;
- the byte-identity claims at the nine radii of §5.1, and the symmetry-reduction cross-checks beyond `cmp` of the level-one and level-two outputs;
- `lat.py`, `merge.py` and the §7 observations 1–4 (only orbit sizes and internal maxima were reproduced);
- the Lean engine's own correctness (resting on `../certificates.md` and its report).

**Caveats.**
1. *Durability.* The C programs and their outputs live in a session scratch directory, not in the repository. The certified results rest on the engine certificates recorded in `../certificates.md`.
2. *Level two.* It is the only range beyond `../certificates.md`, and it is not certified (§5.1). Certifying it needs either a written error analysis of `kcut4.c` together with an independent checker, or the engine's checker with a symmetry-reduced or streaming mode.
3. *Symmetry reduction.* The canonical-circle reduction is justified in §5.1 and cross-checked against the full computation at $\delta=1/10$, $1/20$ and level one.

---

## 11. What transfers to $n=8,10,12$

- **Non-norm radii.** For $\varphi(n)=4$ the field $\mathbb Q(\zeta_n)$ is a CM quadratic extension of a real quadratic field $K^+$, so Lemma 2.2(1) holds verbatim: if a conjugate of $\rho$ is negative, no point of $\mathbb Q(\zeta_n)$ lies on a circle of radius $\sqrt\rho$ about a point of $\mathbb Q(\zeta_n)$. Item 2 holds with any prime of $K^+$ inert in $\mathbb Q(\zeta_n)$. The rational primes $p\equiv\pm2\pmod5$ for $n=5,10$ play the role of $2$ here. Radii $r_c^2-c\,\varepsilon^{2j}$ have a negative conjugate for large $j$ in all four cases. `sharp-lower-bound-n8.md` Lemma 2.2 proves the lattice-point case for $n=8$ along its sequences; the $\mathbb Q(\zeta)$ version here is what removes triple points.
- **Theorem 3.1** ((C3), (C4) automatic; finite group $\iff$ finite cut set) and **Theorems 4.1 and 4.3** (lattice window criterion) hold for $n=8,10,12$ with the same proofs. They use only that the circle centres lie in $\mathbb Z[\zeta_n]$, that this ring is dense in $\mathbb C$ and discrete in its Minkowski embedding, and Corollary 2.3.
- **Lemma 6.1 and Proposition 6.2** need lattice tight points and the unit $\varepsilon$ with $\delta_k\propto\varepsilon^k$.
  - $n=10$: as for $n=5$, the lens corners are lattice points at $r_c$ (`critical-radius-n5.md` §3.2).
  - $n=8,12$: `sharp-lower-bound-n8.md` finds 32 critical lattice points for $n=8$, so the lemma applies there with $\varepsilon=\sqrt2-1$. The identity $N(\varepsilon)=\pm1$ and the congruence argument carry over with $10$ replaced by the denominator of $\delta$.
- **Computation.** `kcut.c` hard-codes $\mathbb Z[\zeta_5]$.
  - $n=10$ uses the same ring with the rotation $\zeta_{10}^{-1}=-\zeta_5^{2}$: a one-line change.
  - $n=8,12$ need the reductions modulo $x^4+1$ and $x^4-x^2+1$ and sign tests in $\mathbb Q(\sqrt2)$, $\mathbb Q(\sqrt3)$.
  - The symmetry reduction by $\{\pm z,\pm\bar z\}$ applies to every $n$.
  - At the speeds observed (level one of $n=5$ in two minutes), the $n=8$ certificates of `sharp-lower-bound-n8.md` could be pushed several levels deeper.

---

## Appendix A. Reproduction

All in `sharp5/` of the session scratch directory.
- `kcut.c` (full), `kcut3.c` (symmetric) and `kcut4.c` (symmetric, exact arguments; used for level two). Compile with `cc -O2 -o kcut kcut.c -lm`.
  - Usage: `kcut da db den maxpieces out.txt` for $\delta=(d_a+d_b\varphi)/\mathrm{den}$. Level one is `-3 2 10`, level two `13 -8 10`, and $\delta_-$ is `18 -11 10`.
  - Output: one line per maximal arc, `A c0 c1 c2 c3 e0 e1 e2 e3 s0 f0 f1 f2 f3 s1`: the centre, then the start and end symbols, ccw. A line `F c0..c3` marks a full circle.
- `cmpk.py` and `canonfilter.py` compare outputs with the referee's JSON; `refcheck2.py` and `refcheck3.py` run the referee's checker.
- `lat.py` contains the exact lattice dynamics; `renorm1.py`, `lvl3.py`, `merge.py`, `mergecount.py` and `dist.py` produce §7.
