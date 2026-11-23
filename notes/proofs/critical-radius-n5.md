# Bounds on the critical radius of $GG_5$: infinite for $r\ge\sqrt{3+\varphi}$, finite for $r\le r_\ast$

Authors: Eric Vergo, Claude

**Statement.** Let $r_c=\sqrt{3+\varphi}\approx 2.1489611$, where $\varphi=(1+\sqrt5)/2$. In this note $r_c$ always denotes this number. The *critical radius* of the family is written $r_{\rm crit}(5)=\sup\{r:GG_5(r)\text{ finite}\}$. It is well defined because finiteness is monotone in $r$ (§2). The target theorem is:

> (A) $GG_5(r)$ is infinite for every $r\ge r_c$; and (B) $GG_5(r)$ is finite for every $r<r_c$.

Together they give $r_{\rm crit}(5)=r_c$, the value conjectured in the paper from numerics. This note proves (A), and (B) on an initial range by a cut-set certificate. (B) in full is proved by a different argument in [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md).

**Status.**
- **Proved: (A).** $GG_5(r)$ is infinite for every $r\ge r_c$, so $r_{\rm crit}(5)\le r_c$.
  - At $r=r_c$ this is the paper's Theorem 2. Here every point, word and disk test of its proof is checked in exact arithmetic in $\mathbb Z[\zeta_5]$ (§3).
  - The extension to $r>r_c$ is direct: the disks only grow, so every disk test still passes and the same words act in the same way.
  - **Proved in Lean** as `TDCSG.CriticalRadius.infinite_GG_five` and `infinite_orbit_zero_five` (`TDCSG/CriticalRadius/Five.lean`, stated in `TDCSG/CriticalRadius/Statements.lean`), which give `1 ≤ criticalRadius 5 ≤ √(3 + φ)`. The written proof below is kept.
- **Proved modulo an exact computation, which was reproduced independently: finiteness on an initial range.** $GG_5(r)$ is a finite group for every $r\le r_\ast$, where $r_\ast^2=3+\varphi-1/10$, $r_\ast\approx2.12557$ and $r_c-r_\ast\approx0.0234$. Hence $r_\ast\le r_{\rm crit}(5)$.
  - This is the full group statement, which is stronger than "every orbit is finite".
  - It follows from a cut-set certificate (Theorem 4.2), verified by computer at $r_\ast$ (§5), together with the already-proved group monotonicity.
  - This is the refereed range. Like every certified range, it is proved modulo the computation and has no Lean counterpart. The deepest certified range is recorded in [`../certificates.md`](../certificates.md): the repository's Lean engine generates and independently checks a certificate at $\delta=1/55$, giving finiteness for $r\le2.144727$ ($r_c-r\approx0.004235$), modulo that computation.
- **Proved elsewhere: (B) on $r_\ast<r<r_c$,** and hence the equality $r_{\rm crit}(5)=r_c$, by the integer-coordinate argument of [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md); machine-checked, with headline Lean theorem `TDCSG.CriticalRadius.criticalRadius_five`. That argument uses no certificate.
  - §6 records the renormalization data (the scale unit $\varphi^3$, the exact self-similarity of the critical chord, threshold ratios).
  - It states a certificate form of (B) (Corollary R$^\ast$, which follows from (B), see §6.4) and a structural Conjecture R describing the expected mechanism of the cut set.
  - §7 explains why the most direct routes to (B) through the cut set fail as stated.
- **Review.** The note has been independently refereed: `referee-report-critical-radius-n5.md` in this directory. §8 lists the referee's verdicts and what the referee did not check.

Throughout, "verified exactly" means:
- equalities and the signs of elements of $\mathbb Q(\sqrt5)$ are decided by integer and rational arithmetic;
- the only non-exact ingredient is in §5: strict inequalities between angles of distinct circle-intersection points, decided by outward-rounded interval arithmetic. Equality of such points is always decided exactly. The repository engine's reproduction of these certificates ([`../certificates.md`](../certificates.md)) decides the order exactly as well.

---

## 1. Setting and notation

- $\zeta=e^{2\pi i/5}$, $\varphi=(1+\sqrt5)/2$. We have $\zeta+\zeta^{-1}=\varphi-1$ and $\zeta^2+\zeta^{-2}=-\varphi$.
- $D_1,D_2$ are the closed disks of radius $r$ centred at $-1$ and $+1$.
- $A(z)=-1+\zeta^{-1}(z+1)$ and $B(z)=1+\zeta^{-1}(z-1)$ are the global clockwise rotations by $2\pi/5$.
- $a=A$ on $D_1$ and $a=\mathrm{id}$ off $D_1$; $b=B$ on $D_2$ and $b=\mathrm{id}$ off $D_2$. Since $A(D_1)=D_1$, $a$ is a bijection of $\mathbb C$ with $a^{-1}=A^{-1}$ on $D_1$; likewise for $b$.
- $GG_5(r)=\langle a,b\rangle$, a group of bijections of $\mathbb C$.
- Words are read left to right, as in the paper: $(gh)(z)=h(g(z))$.

**Arithmetic.**
- Elements of $\mathbb Z[\zeta]$ are integer vectors $(x_0,x_1,x_2,x_3)$ meaning $\sum x_i\zeta^i$, reduced by $\zeta^4=-1-\zeta-\zeta^2-\zeta^3$.
- For $w\in\mathbb Q(\zeta)$, $|w|^2=w\bar w$ lies in $\mathbb Q(\varphi)$ and is written $\alpha+\beta\varphi$.
- The sign of $\alpha+\beta\varphi$ with $\alpha,\beta\in\mathbb Q$ is decided exactly: put $u=2\alpha+\beta$, $v=\beta$. The number is $(u+v\sqrt5)/2$. If $u$ and $v$ do not have opposite signs the answer is immediate; otherwise compare $u^2$ with $5v^2$.
- So "$|z-c|\le r$" for $z,c\in\mathbb Q(\zeta)$ and $r^2\in\mathbb Q(\varphi)$ is decided exactly.

**Lemma 1.1 (translation lattice).**
1. Every rotation used has the form $z\mapsto\zeta^{k}z+c(1-\zeta^{k})$ with $c=\pm1$, and $1-\zeta^k\in(1-\zeta)\mathbb Z[\zeta]$.
2. Hence for every word $w$ and point $z$, the composite of the rotations actually applied to $z$ along $w$ is a map $\mu_w(z)\colon x\mapsto \zeta^j x+t$ with $t\in(1-\zeta)\mathbb Z[\zeta]$. Call it the *word map of $w$ at $z$*.

**Lemma 1.2 (convexity).** If both endpoints of a closed segment $[p,q]$ lie in the closed disk $D_i$, then the whole segment lies in $D_i$. The generator of $D_i$ then acts on $[p,q]$ as the global rotation, and maps it onto the segment between the rotated endpoints. *Proof.* Disks are convex. $\square$

---

## 2. Two facts used in Part B (already proved elsewhere)

These are proved and refereed in `boundary-contact.md` and `theorem1-converse.md` in this directory:

- **Orbit monotonicity** (`boundary-contact.md`, Theorem 3.1). If $r'\le r$ then $O_{r'}(z)\subseteq O_r(z)$ for every $z$.
- **Group monotonicity** (`boundary-contact.md`, Theorem 3.4, via `theorem1-converse.md`, Proposition 4.2). If $GG_5(r)$ is finite, then $GG_5(r')$ is finite for every $r'\le r$.

So $\{r: GG_5(r)\text{ finite}\}$ is a down-set. To prove (B) it is enough to prove finiteness along any sequence $r_k\uparrow r_c$.

---

## 3. Part A: $GG_5(r)$ is infinite for every $r\ge r_c$

### 3.1 The points

In the paper's notation, with $E'=-E$ and so on:

| point | element of $\mathbb Z[\zeta]$ | vector | numerical value | multiple of $E$ |
|---|---|---|---|---|
| $E$ | $\zeta-\zeta^2$ | $(0,1,-1,0)$ | $1.1180+0.3633i$ | $1$ |
| $F$ | $1-\zeta+\zeta^2-\zeta^3$ | $(1,-1,1,-1)$ | $0.6910+0.2245i$ | $\varphi^{-1}$ |
| $G$ | $2F-E$ | $(2,-3,3,-2)$ | $0.2639+0.0858i$ | $\varphi^{-3}=2\varphi-3$ |
| $E',F',G'$ | $-E,-F,-G$ | | | $-1,-\varphi^{-1},-\varphi^{-3}$ |

Checked exactly:
- $\varphi F=E$ and $G=(2\varphi-3)E$.
- $|E+1|^2=3+\varphi=r_c^2$, so $E\in\partial D_1$ and, by the symmetry $z\mapsto -z$, $E'\in\partial D_2$.
- The six points lie on the chord $E'E$ through $0$, in the order $E',F',G',0,G,F,E$.

Note that $G=\varphi^{-3}E$: the critical segment already shows the scale $\varphi^3$ that governs the fractal (§6).

### 3.2 The three words

With $x^{-1}$ written for inverses, the paper's three words are:
- $w_1=a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}$, which maps $[E',F']$ onto $[G,F]$;
- $w_2=a\,b\,a\,b\,b$, which maps $[F',G']$ onto $[F,E]$;
- $w_3=a\,b\,a\,b^{-1}a^{-1}b^{-1}$, which maps $[G',E]$ onto $[E',G]$.

**Lemma 3.1.** For $r=r_c$, each $w_i$ acts on its segment as a translation:
- $w_1$ and $w_2$ act as translation by $2F=2\varphi^{-1}E$;
- $w_3$ acts as translation by $G-E=-2\varphi^{-2}E$.

Moreover, every intermediate image of the segment lies in the lens $D_1\cap D_2$.

*Proof (exact computation by a program outside the repository, re-done independently by the referee).*
1. Apply the letters left to right to both endpoints. Before each letter, check exactly that both current endpoints lie in the closed disk of that letter. By Lemma 1.2 the letter then acts on the whole current segment as the global rotation.
2. In fact both endpoints are checked to lie in both disks at every stage. So every intermediate segment lies in the lens.
3. The exponents of $\zeta$ add up to $0\bmod 5$ for each word, so each composite is a translation.
4. The final endpoints equal the target endpoints exactly, in the stated order. $\square$

The trajectories (exact vectors in the basis $1,\zeta,\zeta^2,\zeta^3$):

| word | stage | image of first endpoint | image of second endpoint |
|---|---|---|---|
| $w_1$ | start | $E'=(0,-1,1,0)$ | $F'=(-1,1,-1,1)$ |
| | $a^{-1}$ | $(-1,1,-1,1)$ | $(-2,-1,0,-2)$ |
| | $a^{-1}$ | $(-2,-1,0,-2)$ | $(1,1,1,2)$ |
| | $b^{-1}$ | $(3,-1,1,2)$ | $(-1,-2,-1,-1)$ |
| | $a^{-1}$ | $(-3,2,-3,-1)$ | $(0,1,-1,0)$ |
| | $b^{-1}$ | $G=(2,-3,3,-2)$ | $F=(1,-1,1,-1)$ |
| $w_2$ | start | $F'=(-1,1,-1,1)$ | $G'=(-2,3,-3,2)$ |
| | $a$ | $(0,-1,1,0)$ | $(3,-2,3,1)$ |
| | $b$ | $(1,2,1,1)$ | $(-3,1,-1,-2)$ |
| | $a$ | $(-1,-1,-1,-2)$ | $(2,1,0,2)$ |
| | $b$ | $(2,1,0,2)$ | $(1,-1,1,-1)$ |
| | $b$ | $F=(1,-1,1,-1)$ | $E=(0,1,-1,0)$ |
| $w_3$ | start | $G'=(-2,3,-3,2)$ | $E=(0,1,-1,0)$ |
| | $a$ | $(3,-2,3,1)$ | $(-1,-2,-1,-1)$ |
| | $b$ | $(-3,1,-1,-2)$ | $(1,1,1,2)$ |
| | $a$ | $(2,1,0,2)$ | $(-2,-1,0,-2)$ |
| | $b^{-1}$ | $(-1,-1,-1,-2)$ | $(3,-1,1,2)$ |
| | $a^{-1}$ | $(1,2,1,1)$ | $(-3,2,-3,-1)$ |
| | $b^{-1}$ | $E'=(0,-1,1,0)$ | $G=(2,-3,3,-2)$ |

**All three words are tight at $r_c$.** In each word, the largest squared distance from an intermediate endpoint to a disk centre is exactly $3+\varphi$. It is attained exactly at three pairs of points:
- $\pm E$;
- $\mp\bar E=\pm(\zeta^3-\zeta^{-1})$, the vector $(1,1,1,2)$ and its negative, the mirror images of $\mp E$ in the real axis. The point $(1,1,1,2)$ lies on $\partial D_2$ and its negative on $\partial D_1$;
- the lens corners $\pm(\zeta-\zeta^{-1})=\pm 2i\sin 72^\circ=\pm1.9021i$, the vector $(1,2,1,1)$ and its negative.

Each word fails already at $r^2=3+\varphi-10^{-6}$.

The lens corners are $\pm i\sqrt{r^2-1}$. So **$r_c$ is exactly the radius at which the lens corners become the lattice points $\pm(\zeta-\zeta^{-1})$**: $r_c^2=1+|\zeta-\zeta^{-1}|^2=1+4\sin^2(2\pi/5)$. The same identity holds for $n=10$: $1+4\sin^2(2\pi/10)=4-\varphi=r_c(10)^2$. It does **not** hold for $n=8$ or $n=12$.

### 3.3 The interval exchange and the infinite orbit

Parametrize the chord by $t\mapsto tE$, $t\in[-1,1]$. Define $T\colon[-1,1)\to[-1,1)$ by
$$T(t)=\begin{cases}t+2\varphi^{-1}, & -1\le t<-\varphi^{-3},\\ t-2\varphi^{-2}, & -\varphi^{-3}\le t<1.\end{cases}$$

**Realization by the words.**
- On $[-1,-\varphi^{-1}]$ the map $T$ is realized by $w_1$, and on $[-\varphi^{-1},-\varphi^{-3}]$ by $w_2$.
- On $[-\varphi^{-3},1]$ it is realized by $w_3$. The endpoint $-\varphi^{-3}$ is assigned to $w_3$.

Since $2\varphi^{-1}+2\varphi^{-2}=2$, $T$ is the rotation $t\mapsto t+2\varphi^{-1}\pmod 2$ of the circle $\mathbb R/2\mathbb Z$, written on the fundamental domain $[-1,1)$.

**Theorem A.** For every $r\ge r_c$, the orbit of $0$ under $GG_5(r)$ is infinite. Hence $GG_5(r)$ is infinite.

*Proof.*
1. For $r\ge r_c$ every disk test of Lemma 3.1 still holds, because the disks only grow. So the words act on the three closed sub-segments exactly as at $r_c$.
2. Put $t_0=0$ and $t_{k+1}=T(t_k)$. Each $t_kE$ is the image of $0$ under the product of the $k$ words used.
3. We have $t_k\equiv 2k\varphi^{-1}\pmod 2$. If $t_k=t_l$ then $(k-l)\varphi^{-1}\in\mathbb Z$, which forces $k=l$ because $\varphi$ is irrational.
4. So the points $t_kE$ are pairwise distinct, and the orbit of $0$ is infinite.
5. An infinite orbit forces an infinite group. $\square$

**Remarks.**
- The whole chord $E'E$ is invariant under the three words, and $T$ is minimal (every $T$-orbit is dense). So every point of the chord has an infinite orbit at every $r\ge r_c$.
- The closed-disk convention is used at the tight points $\pm E$, $\pm\bar E$ and $\pm(\zeta-\zeta^{-1})$. All of them lie on a boundary circle exactly at $r=r_c$, and the words visit them.

---

## 4. Part B: reductions

### 4.1 Internal space (window formulation)

Let $\sigma\colon\zeta\mapsto\zeta^2$. The map $x\mapsto(x,\sigma(x))$ embeds $\mathbb Z[\zeta]$ as a lattice in $\mathbb C\times\mathbb C$ (physical $\times$ internal). Let $\mathcal T(r)$ be the set of all word maps $\mu_w(z)=(x\mapsto\zeta^jx+t)$, over all words $w$ and all points $z\in\mathbb C$.

**Lemma 4.1.** We have the following.
1. If $\mu_w(z)\neq\mathrm{id}$, then $z$ and $w(z)$ lie in $D_1\cup D_2$. Hence $|t|\le 2+2r$.
2. Therefore $\mathcal T(r)$ is finite if and only if $\sup\{|\sigma(t)|\}<\infty$ over $\mathcal T(r)$. That is, the translation parts are bounded in internal space.
3. If $\mathcal T(r)$ is finite, then $GG_5(r)$ is finite.

*Proof.*
1. A non-identity word map means some rotation was applied. The disks are invariant under their own rotations, and every point outside both disks is fixed. So $z$ and $w(z)$ lie in $D_1\cup D_2$, which has diameter at most $2+2r$.
2. This follows from item 1 and the fact that the lattice is discrete in $\mathbb C\times\mathbb C$.
3. Let $\mathcal D$ be the finite family of disks $s^{-1}(D_p)$, for $s\in\mathcal T(r)$ and $p=\pm1$.
   - Along any word, the current word map $s$ of the prefix lies in $\mathcal T(r)$. Whether the next letter applies is the condition $s(z)\in D_p$, that is, $z\in s^{-1}(D_p)$.
   - So the word map of $w$ at $z$ depends only on which members of $\mathcal D$ contain $z$.
   - Hence every $w$ is determined by a function from a finite set of membership patterns to the finite set $\mathcal T(r)$. There are finitely many such functions. $\square$

**A sufficient condition in Minkowski space.** (B) at radius $r$ follows from the existence of a **compact invariant window**: a compact $W\subset\mathbb C\times\mathbb C$ containing $(D_1\cup D_2)\times\{0\}$ and invariant under the lifted maps
$$(y,u)\mapsto(A^{\pm1}y,\ \sigma(A)^{\pm1}u)\ \text{ if } y\in D_1,\qquad (y,u)\mapsto(B^{\pm1}y,\ \sigma(B)^{\pm1}u)\ \text{ if } y\in D_2.$$
Here $\sigma(A)$ is the rotation by $\zeta^{-2}$ about $-1$, and $\sigma(B)$ is the rotation by $\zeta^{-2}$ about $+1$. The window is gated by the physical coordinate only. If such a $W$ exists, then the translation parts of all word maps have internal coordinate bounded by $\max\{|u|:(y,u)\in W\}$. Indeed, starting from $(z,0)$, the internal coordinate after a word is $\sigma(t)$ for the word map $x\mapsto\zeta^jx+t$, by Lemma 1.1, because $\sigma$ is a ring homomorphism and the generators' translation parts are $\pm(1-\zeta^{\pm1})$. So $\mathcal T(r)$ is finite by Lemma 4.1(2), and the group is finite by Lemma 4.1(3). I do not claim the converse: taking the closure of all lifted orbits gives an invariant set only after an argument about the discontinuities of the maps, which I have not made.

### 4.2 The cut-set certificate

**Theorem 4.2 (finiteness certificate).** Fix $r$. Let $K\subset\mathbb C$ be a finite union of closed arcs of circles of radius $r$ with:
- **(C1)** $\partial D_1\cup\partial D_2\subseteq K$;
- **(C2)** $a^{\pm1}(K)\subseteq K$ and $b^{\pm1}(K)\subseteq K$. Equivalently, $A^{\pm1}(K\cap D_1)\subseteq K$ and $B^{\pm1}(K\cap D_2)\subseteq K$;
- **(C3)** no circle carrying an arc of $K$, other than $\partial D_p$ itself, is tangent to $\partial D_p$ ($p=\pm1$);
- **(C4)** every endpoint of a maximal arc of $K$ that lies on $\partial D_p$ is the endpoint of an arc of $K$ that enters $\operatorname{int}D_p$ there.

Then $\mathcal T(r)$ and $GG_5(r)$ are finite. Consequently, by §2, $GG_5(r')$ is finite for every $r'\le r$.

*Proof.*
1. **$K$ is invariant.** By (C2), $a(K)\subseteq K\subseteq a(K)$, so $a(K)=K$; likewise for $b$. Hence $g(K)=K$ for all $g\in GG_5(r)$.
2. **The singular set $V$.** Call $x\in K$ *regular* if some neighbourhood $U$ of $x$ meets $K$ in a single open circular arc through $x$. Let $V$ be the set of non-regular points.
   - $V$ is contained in the set of arc endpoints together with the pairwise intersections of the finitely many carrying circles. So $V$ is finite.
3. **$a(V)=V$.** Take $x\in V$.
   - If $x\notin D_1$, then $a$ is the identity near $x$, so $a(x)=x$.
   - If $x\in\operatorname{int}D_1$, then $a=A$ near $x$, and $A$ maps $K\cap D_1$ onto $K\cap D_1$. So $A$ carries the local picture at $x$ to the local picture at $A(x)$, and $A(x)\in V$.
   - If $x\in\partial D_1$, then $x$ is non-regular because some other arc of $K$ meets $\partial D_1$ at $x$. By (C3) that arc is not tangent to $\partial D_1$. If it crosses $\partial D_1$ at $x$, part of it lies in $\operatorname{int}D_1$. If it ends at $x$, then by (C4) some arc of $K$ ending at $x$ enters $\operatorname{int}D_1$.
   - In both sub-cases, $A$ carries that inner arc to an arc of $K$ meeting $\partial D_1$ at $A(x)$ from inside. So $A(x)\in V$.
   - Thus $a(V)\subseteq V$. The same argument for $a^{-1}$ and $b^{\pm1}$, and finiteness, give equality.
4. **The cell decomposition.** The cells are:
   - the points of $V$;
   - the *edges*, the components of $K\setminus V$, which are open arcs or full circles;
   - the *faces*, the components of $\mathbb C\setminus K$.
   They partition $\mathbb C$. There are finitely many cells: $V$ is finite, $K\setminus V$ has finitely many components, and the complement of a finite union of circular arcs has finitely many components.
5. **Faces.** By (C1), a face lies in $\operatorname{int}D_1$ or misses $D_1$. So $a$ is a single isometry on it ($A$ or $\mathrm{id}$). Its image is a connected subset of $\mathbb C\setminus K$, and applying the same to $a^{-1}$ shows the image is a face.
6. **Edges.** An edge not contained in $\partial D_1$ does not meet $\partial D_1$, since a crossing point would lie in $V$. So an edge lies in $\partial D_1$, in $\operatorname{int}D_1$, or misses $D_1$, and $a$ is a single isometry on it ($A$ or $\mathrm{id}$). Its image is a connected subset of $K\setminus V$, and applying the same to $a^{-1}$ shows the image is an edge. This covers edges that are full circles. The same holds for $b$.
7. **Every group element acts on cells.** Every $g\in GG_5(r)$ permutes the cells. Along any word, the letter applied at a point $z$ is the isometry by which that letter acts on the cell containing the current point. Hence the word map $\mu_w(z)$ is an isometry $x\mapsto\zeta^jx+t$ carrying the cell $X$ of $z$ onto the cell $w(X)$.
8. **Counting the possible word maps.**
   - The unbounded face misses $D_1\cup D_2$: by (C1) the boundary circles lie in $K$, so a face lies inside $D_1\cup D_2$ or outside it, and the unbounded one lies outside. So every generator fixes it pointwise, and the only word map on it is the identity. ($K$ may contain arcs outside $D_1\cup D_2$, so the unbounded face need not be all of $\mathbb C\setminus(D_1\cup D_2)$; that does not matter.)
   - Every other cell is bounded. For a bounded edge or face $X$ and a target cell $Y$, there are at most $5$ maps $x\mapsto\zeta^jx+t$ carrying $X$ onto $Y$: at most one $t$ for each $j$, since a non-trivial translation cannot map a bounded set onto itself.
   - For $X=\{x\}\subset V$, the image lies in the finite set $V$, giving at most $5|V|$ maps.
   - Since there are finitely many cells, $\mathcal T(r)$ is finite, and Lemma 4.1(3) gives finiteness of the group. $\square$

**The minimal certificate.** The natural candidate is the *cut set* $K(r)=\bigcup_{g}g(\partial D_1\cup\partial D_2)$, the smallest set satisfying (C1)–(C2).
- If $GG_5(r)$ is finite, then $K(r)$ is a finite union of arcs, because each element is a piecewise isometry with finitely many circular pieces.
- But a finite $K(r)$ need not satisfy (C3)–(C4). For example, at $\delta=1$ (where $4\delta\in\mathbb Z$) the closure meets a tangency, although $GG_5$ is presumably finite there.
- So computing $K(r)$ and checking (C3)–(C4) is a **sufficient** test of finiteness at a single radius, not a necessary one.

---

## 5. Part B: finiteness up to $r_\ast$, by an exact finite computation

### 5.1 The computation

**Where the computation lives.** The certificate was produced by a program **outside this repository**: a Python program written in a working session, not archived here, because the repository holds Lean code only. Two things make the result reproducible without that program:
- this section describes the algorithm and data formats fully enough to re-implement it;
- the referee wrote an independent second implementation from the theorem statements alone (`referee-report-critical-radius-n5.md`, "Independent computations"). It produced byte-identical sets of maximal arcs at $\delta=13/5,\ 1/2,\ 9/10,\ 9/20,\ 3/10,\ 1/5$ and $1/10$, and matching counts at $3/20$. At $\delta=1/10$ the shared output is 50,714 circles, 1,437,580 pieces and 198,470 maximal arcs. The referee's separate checker of (C1)–(C4) also passes on the author's merged output.

The computation is also implemented in the repository's Lean engine (`tdcsg-orbit certify` and `tdcsg-orbit check-certificate`, see [`../certificates.md`](../certificates.md)). It exports the certificate as the list of maximal arcs and verifies it with a separate, float-free checker of (C1)–(C4). It reproduces every row of Table 5.1 with identical arc sets, and certifies further rows down to $\delta=1/55$.

**Algorithm.** Input: a rational $\delta$, with $r^2=\rho:=3+\varphi-\delta$. The program computes $K(r)$ by closure:
1. Start from the two full circles $\partial D_{1}$ and $\partial D_2$.
2. Repeatedly take a newly added arc, intersect it with $D_1$ and $D_2$, and rotate the parts by $A^{\pm1}$ and $B^{\pm1}$ respectively.
3. Add the parts of the images that are not yet covered.
4. Stop when nothing new appears.

**Representation.**
- A circle is its centre $c\in\mathbb Z[\zeta]$, stored as an integer 4-vector. All circles have radius $r$.
- An arc endpoint is a symbol $(e,s)$ meaning the intersection point of $\operatorname{circle}(c)$ with $\operatorname{circle}(e)$, $e\in\mathbb Z[\zeta]$, on side $s\in\{\pm1\}$. Concretely the point is $c+\tfrac d2(1+i s h)$ with $d=e-c$ and $h=\sqrt{4\rho/|d|^2-1}$.
- Clipping by $D_p$ creates symbols $(p,\pm1)$. A rotation $R$ about $p$ maps the symbol $(e,s)$ on $\operatorname{circle}(c)$ to $(R e,s)$ on $\operatorname{circle}(Rc)$.
- So all endpoints stay symbolic and exact.

**Decisions.**
- *Does $\operatorname{circle}(c)$ meet $\operatorname{int}D_p$?* That is, is $0<|c-p|^2<4\rho$? This is decided exactly in $\mathbb Q(\sqrt5)$. Tangency $|c-p|^2=4\rho$ would abort the run. It cannot occur when $4\delta\notin\mathbb Z$, because $|c-p|^2\in\mathbb Z[\varphi]$. All $\delta$ used satisfy $4\delta\notin\mathbb Z$, so (C3) holds automatically.
- *Are two endpoints on $\operatorname{circle}(c)$ the same point?* Identical symbols are equal. For different symbols $(e_1,s_1)$ and $(e_2,s_2)$ the answer is decided exactly:
  - compute the circumcentre $O$ of $c,e_1,e_2$ in $\mathbb Q(\zeta)$, as $O-c=(|u|^2v-|v|^2u)/(\bar uv-u\bar v)$ with $u=e_1-c$ and $v=e_2-c$;
  - test $|O-c|^2=\rho$ in $\mathbb Q(\varphi)$;
  - test the two side conditions $\operatorname{sign}\operatorname{Im}((O-c)\bar u)=s_1$ and $\operatorname{sign}\operatorname{Im}((O-c)\bar v)=s_2$. The sign of $\operatorname{Im}z$ is computed exactly as the sign of the real element $(z-\bar z)/(\zeta-\zeta^{-1})\in\mathbb Q(\varphi)$.
- *Order of distinct endpoints along a circle.* The angle is $\arg d+s\arccos(|d|/2r)$. It is computed in `mpmath.iv` (outward-rounded interval arithmetic, 120 bits), with the quadrant of $\arg d$ fixed by exact signs of $\operatorname{Re}d$ and $\operatorname{Im}d$.
  - Two endpoints are declared distinct only if their angle intervals are disjoint modulo $2\pi$. Otherwise the exact equality test is run.
  - If that test says "different" while the intervals overlap, the precision is doubled. This never happened.
  - A cheap pre-filter skips pairs of arcs whose floating angle ranges are more than $10^{-6}$ apart. The interval widths are below $10^{-20}$, so this skips only certainly-disjoint pairs.
- After closure, (C4) is checked: every piece endpoint that lies on $\partial D_p$ (detected by exact symbol equality with $(p,\pm1)$) and is not shared with an adjacent piece must start or end the arc going into $D_p$.

When the closure terminates, $K(r)$ is the finite union of the stored arcs. Every stored arc had its four clipped images added, so (C1) and (C2) hold by construction. Then Theorem 4.2 applies.

**Certificate format (for re-implementation and checking).**
- Header: $n=5$; $\delta$ as an exact rational; the radius convention $r^2=3+\varphi-\delta$; the basis $1,\zeta,\zeta^2,\zeta^3$.
- One record per maximal arc:
  - the centre $c$, as an integer 4-vector;
  - the start and end endpoint symbols $(e,s)$, each an integer 4-vector $e$ and a sign $s\in\{\pm1\}$;
  - the arc runs counterclockwise from start to end.
  A full circle is a record with a full-circle flag, and the two boundary circles $c=\mp1$ are full.
- **The checker** reads only this file and verifies:
  - (C1): the two full circles are present;
  - (C2): for every arc, every $p=\pm1$ and $k=\pm1$, the part of the arc in $D_p$, rotated by $\zeta^{-k}$ about $p$, lies inside a single maximal arc of the target circle;
  - (C3): $|c-p|^2\neq4\rho$ for every centre $c\neq p$, checked exactly;
  - (C4): every maximal-arc endpoint equal to a symbol $(p,\pm1)$ is the start symbol $(p,-1)$ or the end symbol $(p,+1)$ of its arc, so that the arc runs into $D_p$.
- Orderings may use interval arithmetic, or floating point with a proven error bound, as long as distinct endpoints closer than the error bound are sent to the exact equality test.

### 5.2 Results

**Table 5.1.** Computation of the cut set $K(r)$ at $r^2=3+\varphi-\delta$.
- "Pieces" are the stored arcs before adjacent ones are merged. This number depends on processing order and is not an invariant of $K$.
- "Maximal arcs" is the invariant count, from the referee's merge.
- "(C4) endpoints" is the number of maximal-arc endpoints lying on a boundary circle, all of which pass (C4).
- $\max|\sigma(c)|$ is the largest internal-space modulus of a circle centre.

| $\delta$ | $r$ | $r_c-r$ | closed | circles | maximal arcs | pieces | (C4) endpoints / failures | $\max|\sigma(c)|$ | $\delta\cdot\max|\sigma(c)|$ |
|---|---|---|---|---|---|---|---|---|---|
| $13/5$ | 1.42058 | 0.72839 | yes | 54 | 64 | 112 | 60 / 0 | 7.3 | 19.0 |
| $9/10$ | 1.92822 | 0.22074 | yes | 466 | 952 | 2 040 | 316 / 0 | 18.2 | 16.4 |
| $9/20$ | 2.04158 | 0.10738 | yes | 1 722 | 4 222 | 10 303 | 864 / 0 | 37.6 | 16.9 |
| $3/10$ | 2.07799 | 0.07097 | yes | 5 044 | 13 138 | 35 667 | 1 696 / 0 | 57.6 | 17.3 |
| $1/5$ | 2.10191 | 0.04705 | yes | 11 606 | 35 194 | 185 541 | 2 964 / 0 | 89.1 | 17.8 |
| $3/20$ | 2.11377 | 0.03519 | yes | 30 776 | 87 922 | 496 587 | 4 420 / 0 | 156.4 | 23.5 |
| $1/10$ | 2.12557 | 0.02339 | yes | 50 714 | 198 470 | 1 437 580 | 7 172 / 0 | 188.3 | 18.8 |
| $3/40$, $1/20$ | | | not finished (stopped at the cap of $10^6$ pieces) | | | | | | |

**Notes on the runs.**
- In every finished run: no tangency occurred, the interval precision never had to be raised, and (C4) had no failures.
- The run at $9/10$ was also done with an earlier version that called the exact equality test on every comparison (345,586 exact tests). It gave identical output.
- From $\delta=9/20$ on, the author's store contains two degenerate pieces, each a single point. They lie on a boundary circle, which is contained in $K$, so they do not change the set $K$ or any hypothesis of Theorem 4.2. They account for the difference of 2 between the author's and the referee's piece counts at several radii; piece counts are not invariants in any case.

**Theorem B (proved modulo the computation of Table 5.1).** $GG_5(r)$ is finite for every $r\le r_\ast$, where $r_\ast^2=3+\varphi-\delta_\ast$ with $\delta_\ast=1/10$, i.e. $r_\ast\approx 2.12557$ and $r_c-r_\ast\approx 0.0234$.

*Proof.* The run for $\delta_\ast$ terminates and outputs $K(r_\ast)$ satisfying (C1)–(C4). Theorem 4.2 then gives finiteness at $r_\ast$, and group monotonicity (§2) extends it to every $r'\le r_\ast$. $\square$

**Remarks.**
- The circle counts at $\delta=13/5$, $3/10$, $1/5$ and $1/10$ (54, 5044, 11606, 50714) also agree with a floating-point implementation of the same closure by the same author, which merges arcs numerically. That is a consistency check by the author, not an independent check and not part of the proof; the independent check is the referee's.
- In every run, all coincidences of endpoints were between identical symbols. The circumcentre equality test was never needed to identify two different symbols.

### 5.3 Why the computation cannot reach $r_c$

The size of $K(r)$ grows like a power of $\delta^{-1}$ (Table 5.1). The internal extent of the circle centres grows like $\delta^{-1}$, consistent with the orbit-of-$0$ data in [`../arithmetic.md`](../arithmetic.md) §3.2, where $R\cdot\delta$ stays bounded. Each factor $\varphi^3$ in $\delta$ multiplies the work by a roughly constant factor. So no single finite computation reaches $r_c$. A proof of (B) on all of $(r_\ast,r_c)$ needs an induction along the renormalization (§6).

---

## 6. Renormalization data

These are the precise objects a renormalization proof would use, recorded so that they can be reused for $n=8,10,12$.

**6.1 Scale unit.** $\varepsilon=\varphi^{-3}=2\varphi-3\in\mathbb Z[\varphi]^\times$, with Galois conjugate $\sigma(\varepsilon)=-\varphi^{3}$.
- Multiplication by $\varepsilon$ is an automorphism of the lattice $\mathbb Z[\zeta]$. It contracts the physical coordinate by $\varphi^3$ and expands the internal one by $\varphi^3$.
- **Proved:** on the critical chord, $G=\varepsilon E$ and $G'=\varepsilon E'$ exactly.
- **Measured:**
  - the same-type thresholds $\delta_k=r_c^2-r_k^2$ of the orbit of $0$ have successive ratios $4.167$, $4.220$, $4.233\to\varphi^3=4.236$;
  - the internal extent of orbits grows by $4.23$–$4.28$ per generation;
  - the orbit size grows by a factor of about $12$–$13$ per generation.

  Sources: [`../experiments.md`](../experiments.md) E3, [`../arithmetic.md`](../arithmetic.md) §3.2, and the exact threshold sweep of [`../engine.md`](../engine.md). The first orbit-of-$0$ threshold is $\delta_1=0.8541=4.618-3.764$, i.e. $r_1^2=7-2\varphi=|2-\zeta|^2$.

**6.2 Critical interval exchange.**
- The induced dynamics on the chord $E'E$ is the rotation by $2\varphi^{-1}$ on a circle of length $2$ (§3.3). Its rotation number $\varphi^{-1}$ is a fixed point of the Gauss map.
- So its first-return map to a sub-interval of relative length $\varphi^{-1}$ is again a rotation with the same rotation number: the standard golden renormalization, with period one and scale $\varphi$.
- Three steps of this 1-D renormalization give $\varphi^3$, the scale of the 2-D pattern. In the measured threshold sequence there are 2–3 jump types per factor $\varphi^3$ ([`../experiments.md`](../experiments.md) E3).
- That the 2-D minimal period is three 1-D steps is an observation, not a proved statement.

**6.3 Geometry of the critical configuration (proved).**
- At $r=r_c$ the boundary circles pass through the lattice points $\pm E$ (the chord's ends), $\pm\bar E$, and the lens corners $\pm(\zeta-\zeta^{-1})$.
- Every word of §3 touches a boundary circle at some of these points.

**6.4 What can and cannot renormalize exactly.**
- **Only the 1-D chord map renormalizes exactly, and only at $r_c$.** The interval exchange $T$ on $E'E$ (§3.3, §6.2) is exactly self-similar, and $G=\varepsilon E$.
- **The 2-D cut set does not renormalize exactly by a similarity at any $r$, including $r_c$.** A similarity of ratio $\varphi^{\pm3}$ maps a circle of radius $r$ to a circle of radius $\varphi^{\pm3}r$. So it cannot carry an arrangement of radius-$r$ arcs onto an arrangement of radius-$r'$ arcs with $r'\approx r$, over any region containing a non-degenerate arc.
- This argument excludes only conjugacy by similarities. It says nothing against other kinds of exact conjugacy.
- Near the accumulation point, at depth $k$, the boundary is a circle that deviates from its tangent line by $O(\varphi^{-6k})$ across a region of size $\varphi^{-3k}$. So at best the 2-D renormalization is exact *combinatorially and asymptotically*. This matches the threshold ratios converging to $\varphi^3$ rather than being equal to it.

**A certificate form of (B).** By Theorem 4.2 and group monotonicity, the following statement implies (B). At a general radius it is stronger than finiteness, because a finite cut set need not satisfy (C4) (§4.2). It holds: at the levels $r_k$, which are non-norm radii by Lemma 2.2(3) of [`sharp-lower-bound-n5.md`](sharp-lower-bound-n5.md), finiteness of $GG_5(r_k)$ implies that the closure terminates with $K(r_k)$ satisfying (C1)–(C4) (Theorem 3.1 of [`sharp-lower-bound-n5.md`](sharp-lower-bound-n5.md)), and finiteness below $r_c$ is proved in [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md).

**Corollary R$^\ast$.** Put $r_k^2=3+\varphi-\tfrac1{10}\varepsilon^{k}$ for $k\ge0$, with $\varepsilon=\varphi^{-3}$. Then for every $k\ge0$ the cut set $K(r_k)$ is a finite union of arcs satisfying (C3) and (C4).

**Why R$^\ast$ suffices, and what is already known.**
- Since $r_k\uparrow r_c$, Theorem 4.2 and §2 give finiteness for every $r<r_c$, which is (B).
- (C3) holds automatically at every $r_k$. We have $4\rho_k=12+4\varphi-\tfrac25\varepsilon^k$. Here $\varepsilon^k=\alpha+\beta\varphi$ is a unit of $\mathbb Z[\varphi]$, so $5$ does not divide both $\alpha$ and $\beta$. Hence $4\rho_k\notin\mathbb Z[\varphi]$, while every $|c-p|^2$ lies in $\mathbb Z[\varphi]$.
- $k=0$ is Table 5.1 ($\delta=1/10$).
- The content of R$^\ast$ is therefore that the closure terminates at every level, and that (C4) holds. Both follow from (B) by Theorem 3.1 of `sharp-lower-bound-n5.md`.

**Conjecture R (structural mechanism).** There exist a compact region $U\ni E$ and $k_0$ with the following property. For each $k\ge k_0$, the combinatorial type of $K(r_k)$ inside the $\varepsilon^{k}$-scaled copy $E+\varepsilon^k(U-E)$ (and its images under the symmetries $z\mapsto-z$, $z\mapsto\bar z$) is the image under $z\mapsto E+\varepsilon(z-E)$ of the type of $K(r_{k-1})$ inside $E+\varepsilon^{k-1}(U-E)$.

Here combinatorial type means:
- the set of circles meeting the region, as centres modulo the scaling;
- the cyclic order of the arc endpoints on each such circle.

**What Conjecture R gives and does not give.**
- It gives only the **local** structure of $K(r_k)$ near $\pm E$ and $\pm\bar E$, uniformly in $k$.
- It does **not** give, by itself, that $K(r_k)$ is finite as a whole (outside the copies of $U$), or that (C4) holds.
- To deduce R$^\ast$ from R one would also need:
  - (i) that outside the copies of $U$ the cut set has a bounded number of arcs at every level;
  - (ii) that the closure process at a fixed $r_k$ enters the nested copies only finitely many times, i.e. the recursion stops after about $k$ levels;
  - (iii) an explicit bound showing that the curvature correction does not change the sign of any of the finitely many disk tests defining the type, once $k\ge k_0$.
- Item (iii) is part of what R asserts. Items (i) and (ii) are additional.
- So R would describe the mechanism of the cut set; it is not by itself a proof of (B).

**Template for $n=8,10,12$.** The same objects are expected with:

| $n$ | field | scale unit | $r_c^2$ (conjectured) |
|---|---|---|---|
| 8 | $\mathbb Q(\sqrt2)$ | $1+\sqrt2$ | $10-5\sqrt2$ |
| 10 | $\mathbb Q(\sqrt5)$ | $\varphi^3$ | $4-\varphi$ |
| 12 | $\mathbb Q(\sqrt3)$ | $2+\sqrt3$ | $40-22\sqrt3$ |

The values of $r_c^2$ are the paper's (Table 1 and its section on geometric constructions), as are the scale factors $\sqrt2-1$ and $2-\sqrt3$. The scale units are also measured in [`../experiments.md`](../experiments.md) E3.

Theorem 4.2 holds for any $n$ with the same proof. The algorithm of §5 generalizes routinely: replace $\mathbb Z[\zeta_5]$ by $\mathbb Z[\zeta_n]$ (reduction modulo $\Phi_n$) and $\mathbb Q(\sqrt5)$ by the real quadratic field, and replace $\zeta_5-\zeta_5^{-1}$ in the exact sign test for $\operatorname{Im}$ by $\zeta_n-\zeta_n^{-1}$. The author's program hard-codes $n=5$; the referee's field code shows that the generalization is routine. For $n=8$ and $12$ the paper's infinite-orbit constructions are limit-point arguments, not finite interval exchanges. Part A for those $n$ needed a new exact construction; it is given in `critical-radius-n8.md` and `critical-radius-n12.md` (a self-similar family of partial isometries of a chord through a critical lattice point), and for $n=10$ in `critical-radius-n10.md`.

---

## 7. Attempted routes that did not close

1. **A simple window (approach (i)).** The internal-space images of orbits below $r_c$ are not filled by a fixed polygon or union of disks scaled with $\delta^{-1}$. The filling fraction of orbit points in the natural window decreases as $r\uparrow r_c$ (from $0.029$ to $0.012$ for $n=5$; [`../experiments.md`](../experiments.md) E4). The invariant set is fractal, so no describable window $W(r)$ was found. Lemma 4.1 still reduces (B) to the existence of *some* compact invariant window, and $K(r)$ is the finite combinatorial substitute used in §5.
2. **Exact periodic renormalization (approach (ii)).** Only the 1-D chord map renormalizes exactly, and only at $r_c$. The 2-D cut set admits no exact similarity renormalization at any $r$, including $r_c$ (§6.4). And at $r_c$ the group is infinite, so a renormalization there would not by itself control $r<r_c$.
3. **Direct certification along $r_k\uparrow r_c$ (approach (iii)).** It is carried out for finitely many $k$ (Table 5.1). It cannot be continued indefinitely without a uniform pattern such as Conjecture R, because the computation grows like a power of $\delta^{-1}$.
4. **Literature (approach (iv)).** Cited from memory, except that the referee confirmed the bibliographic data and statement of Akiyama–Brunotte–Pethő–Steiner.
   - The closest proved results are global-stability theorems for single planar piecewise isometries or discretized rotations with quadratic rotation parameters, proved by self-similar domain-exchange renormalization:
     - Adler, Kitchens and Tresser (ETDS 2001), piecewise affine maps of the torus;
     - Kouptsov, Lowenstein and Vivaldi, "Quadratic rational rotations of the torus and dual lattice maps" (Nonlinearity 2002), the cases $q=5,8,10,12$;
     - Akiyama, Brunotte, Pethő and Steiner, "Periodicity of certain piecewise affine planar maps" (Tsukuba J. Math. 32 (2008), no. 1): every *integer* sequence with $0\le a_{k-1}+\lambda a_k+a_{k+1}<1$ is periodic, for $\lambda\in\{(\pm1\pm\sqrt5)/2,\pm\sqrt2,\pm\sqrt3\}$. These are lattice orbits of the discretized rotation, and the parameters are exactly the $n=5,10,8,12$ cases;
     - Lowenstein, Hatjispyros and Vivaldi (Chaos 1997), the golden case of the round-off rotation;
     - Goetz and Poggiaspalla, and Lowenstein, Kouptsov and Vivaldi, for rotations by $\pi/7$.
   - None of these applies directly. They treat one map on a fixed polygonal domain at one parameter. $GG_5(r)$ is a two-generator group, gated by disks, in a one-parameter family whose boundaries are curved.
   - The Akiyama–Brunotte–Pethő–Steiner method is the best template. One finds a finite set of polygonal "atoms" and an exact induced map that reproduces itself after scaling by the unit. The new ingredients needed here are control of the curvature correction uniformly in $k$ and global finiteness at each level (known from (B); §6.4).
   - Reduction to the single map $ab^{-1}$, which the paper mentions, would not suffice for group finiteness in any case. Finiteness of the orbits of one element does not bound the orbits of the group.

---

## 8. Status and gaps

The referee's verdicts are in `referee-report-critical-radius-n5.md`. The table states the current status after the referee's fixes were applied.

| claim | status |
|---|---|
| Lemma 1.1, 1.2; §2 monotonicity | proved (§2 cites refereed notes) |
| Theorem A: infinite for all $r\ge r_c$, so $r_{\rm crit}(5)\le r_c$ | **proved**; refereed correct after minor fixes. Every arithmetic step verified exactly, and re-verified independently by the referee. **Proved in Lean** (`TDCSG.CriticalRadius.infinite_GG_five`) |
| Side fact: $r_c$ is where the lens corners are $\pm(\zeta-\zeta^{-1})$ (also $n=10$; not $n=8,12$) | proved; refereed correct |
| Lemma 4.1 and Theorem 4.2 (cut-set certificate, a sufficient test) | proved; refereed correct after minor fixes |
| Theorem B: finite for $r\le r_\ast$, so $r_\ast\le r_{\rm crit}(5)$ | **proved modulo the computation of §5**, refereed correct given the computation. The computation was reproduced by an independent implementation with identical arc sets. The original program and files are not archived in the repository (§5.1); the repository's Lean engine reproduces the certificate with an independent checker and certifies deeper ranges, down to $\delta=1/55$ ([`../certificates.md`](../certificates.md)) |
| finite for $r_\ast<r<r_c$; $r_{\rm crit}(5)=r_c$ | **proved** by the integer-coordinate argument of [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md) (refereed in `referee-report-sharp-lower-bound-n5-pentagrid.md` and, for its conclusion and Lean coverage, in `referee-report-sharp-lower-bound-n5-pentagrid-conclusion.md`; machine-checked as `TDCSG.CriticalRadius.criticalRadius_five`), not by this note's certificates, which reach the range of `../certificates.md`; also supported numerically by orbit scans up to $\delta\approx4\cdot10^{-3}$ ([`../arithmetic.md`](../arithmetic.md) §3.2) and the paper's searches. Reductions: `sharp-lower-bound-n5.md`, `sharp-lower-bound-combined.md` |
| Corollary R$^\ast$ (implies (B)) | holds, as a consequence of (B), Lemma 2.2(3) and Theorem 3.1 of `sharp-lower-bound-n5.md` (§6.4); deduction refereed in `referee-report-sharp-lower-bound-n5-pentagrid-conclusion.md` |
| Conjecture R (structural) | conjecture, with the evidence of §6 |
| infinite at $r_c=\sqrt{3+\varphi}$ | proved (this is the paper's Theorem 2). The paper's footnote 4, that the group is infinite at the critical radius, holds for $n=5$, since (B) gives $r_{\rm crit}(5)=r_c$ |
| The sufficient-condition argument for the window (§4.1) and the remarks of §6 other than the deduction of Corollary R$^\ast$ | written after refereeing; **not yet refereed** |

**Not checked by the referee:**
- the measured renormalization data in §6.1 and the files they cite;
- the column $\max|\sigma(c)|$ of Table 5.1;
- run times;
- group orders at known radii;
- the literature beyond Akiyama–Brunotte–Pethő–Steiner;
- §9 (Lean);
- the correctness of `mpmath.iv` beyond a spot check.

The referee's own orderings rest on a stated double-precision error bound rather than interval arithmetic. The two implementations agree exactly, so they cross-check each other.

**Remaining caveats.**
1. Durability: the author's program behind Theorem B lives outside the repository. The mathematical claim rests on two independent implementations that agree exactly, on the algorithm and certificate format described in §5.1, and on the repository engine's reproduction ([`../certificates.md`](../certificates.md)), whose small certificates are committed in `certificates/` and whose larger ones are recorded by SHA-256.
2. Strict angle comparisons in the author's program rely on `mpmath.iv` being correctly outward-rounded for `sqrt` and `atan2`. That is standard, but it is trust in a library.
3. (C4) is checked on endpoints of maximal arcs. The author's program checks a stricter version on pieces.
4. Theorem A's statement "the group is infinite" uses only one orbit. It does not need, and does not prove, anything about the structure of $GG_5(r)$ beyond infinitude.
5. This note alone does not show that $r_c$ is the critical radius of the group. That requires (B) on $(r_\ast,r_c)$, which is proved in [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md).

---

## 9. Lean formalization: what is done and what is not

**Formalized** (`TDCSG/CriticalRadius/`; statements in `Statements.lean`):
1. $\mathbb Z[\zeta_5]$ as integer vectors with the reduced multiplication, conjugation and the map to $\mathbb C$, with soundness lemmas linking the computable checks to $\mathbb C$ (`Five.lean`).
2. The generators as `Equiv.Perm ℂ` (`TDCSG.permA`, `TDCSG.permB`), words acting on segments, and the convexity lemma (`CriticalRadius/Basic.lean`).
3. **Part A in full**: `TDCSG.CriticalRadius.infinite_orbit_zero_five` and `infinite_GG_five`, hence `criticalRadius_five_le` and `one_le_criticalRadius_five`. The word checks are plain `decide` on integer data, linked to the real generators by proved lemmas.
4. **Part B in full, by a different route**: finiteness of $GG_5(r)$ for every $r<r_c$ and `criticalRadius 5 = √(3 + φ)` (headline theorem `TDCSG.CriticalRadius.criticalRadius_five`), following the integer-coordinate argument of [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md) (its §5 says what Lean covers). It does not use the certificates of this note.

**Not formalized:**
1. Theorem 4.2 itself, the certificate theorem: it is a refereed written result with no Lean counterpart, and the library has no certificate predicate. Its cost is the cell-decomposition argument (finite unions of arcs, regular points, components of complements). A cheaper route may be Lemma 4.1(3) with an explicit finite $\mathcal T(r)$ and a certificate that $\mathcal T(r)$ is closed, which needs region-emptiness proofs for intersections of disks and disk complements.
2. The link between a certificate file and the hypotheses (C1)–(C4). The engine's checker (`tdcsg-orbit check-certificate`) is a compiled, tested Lean program, not a kernel-checked proof; a verified checker would be a Lean function with a soundness theorem against a Lean definition of a certificate ([`../certificates.md`](../certificates.md) §7).
3. Hence Theorem B of this note is proved modulo the computation, not in Lean.
