# The critical radius of $GG_5$

Authors: Eric Vergo, Claude

**Statement.** Let $r_c=\sqrt{3+\varphi}\approx 2.1489611$, where $\varphi=(1+\sqrt5)/2$. The target theorem is:

> (A) $GG_5(r)$ is infinite for every $r\ge r_c$; and (B) $GG_5(r)$ is finite for every $r<r_c$.

**Status.**
- **(A) is proved.** The proof reconstructs the paper's Theorem 2. Every point, word and disk test is checked in exact arithmetic in $\mathbb Z[\zeta_5]$ (§3). One small extension: the same argument gives an infinite orbit (of $0$) at every $r\ge r_c$, not only at $r_c$.
- **(B) is open.** It is proved here only on an explicit initial range $r\le r_\ast$, as a corollary of a finite exact computation (§5) combined with the already-proved group monotonicity. Here $r_\ast^2=3+\varphi-1/10$, so $r_\ast\approx2.12557$ and $r_c-r_\ast\approx0.0234$; this is the closest radius in Table 5.1 for which the computation finished. The remaining window $r_\ast<r<r_c$ is not proved.
- **What is proved for $r\le r_\ast$.** The full group statement: $GG_5(r)$ is a finite group. This is stronger than "every orbit is finite".
- **Evidence for the rest.** §6 records the renormalization data (the scale unit $\varphi^3$, the exact self-similarity of the critical segment, threshold ratios) and states the missing step as a precise conjecture. §7 explains why the most direct routes to (B) fail as stated.

Throughout, "verified exactly" means:
- equalities and the signs of elements of $\mathbb Q(\sqrt5)$ are decided by integer and rational arithmetic;
- the only non-exact ingredient is in §5: strict inequalities between angles of distinct circle-intersection points, decided by outward-rounded interval arithmetic. Equality of such points is always decided exactly.

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

*Proof (exact computation, `t4/partA.py`).*
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

**All three words are tight at $r_c$.** In each word, the largest squared distance from an intermediate endpoint to a disk centre is exactly $3+\varphi$. It is attained at $\pm E$ and at the lens corners $\pm(\zeta-\zeta^{-1})=\pm 2i\sin 72^\circ=\pm1.9021i$, the vector $(1,2,1,1)$ and its negative.

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
- Only the closed-disk convention at $E$ and $E'$ is used. Both lie on a boundary circle exactly at $r=r_c$.

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

Equivalently, (B) asks for a **compact invariant window**: a compact $W\subset\mathbb C\times\mathbb C$ containing $(D_1\cup D_2)\times\{0\}$ and invariant under the lifted maps
$$(y,u)\mapsto(A^{\pm1}y,\ \sigma(A)^{\pm1}u)\ \text{ if } y\in D_1,\qquad (y,u)\mapsto(B^{\pm1}y,\ \sigma(B)^{\pm1}u)\ \text{ if } y\in D_2.$$
Here $\sigma(A)$ is the rotation by $\zeta^{-2}$ about $-1$, and $\sigma(B)$ is the rotation by $\zeta^{-2}$ about $+1$. The window is gated by the physical coordinate only.

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
   - the *edges*, the components of $K\setminus V$, which are open arcs;
   - the *faces*, the components of $\mathbb C\setminus K$.
   They partition $\mathbb C$.
5. **Faces.** By (C1), a face lies in $\operatorname{int}D_1$ or misses $D_1$. So $a$ is a single isometry on it ($A$ or $\mathrm{id}$). Its image is a connected subset of $\mathbb C\setminus K$, and applying the same to $a^{-1}$ shows the image is a face.
6. **Edges.** An edge not contained in $\partial D_1$ does not meet $\partial D_1$, since a crossing point would lie in $V$. So $a$ is again a single isometry on each edge, and maps it onto an edge. The same holds for $b$.
7. **Every group element acts on cells.** Every $g\in GG_5(r)$ permutes the cells. Along any word, the letter applied at a point $z$ is the isometry by which that letter acts on the cell containing the current point. Hence the word map $\mu_w(z)$ is an isometry $x\mapsto\zeta^jx+t$ carrying the cell $X$ of $z$ onto the cell $w(X)$.
8. **Counting the possible word maps.**
   - The unbounded face is $\mathbb C\setminus(D_1\cup D_2)$, by (C1). Every generator fixes it pointwise.
   - For a bounded edge or face $X$ and a target cell $Y$, there are at most $5$ maps $x\mapsto\zeta^jx+t$ carrying $X$ onto $Y$: at most one $t$ for each $j$, since a non-trivial translation cannot map a bounded set onto itself.
   - For $X=\{x\}\subset V$, the image lies in the finite set $V$, giving at most $5|V|$ maps.
   - So $\mathcal T(r)$ is finite, and Lemma 4.1(3) gives finiteness of the group. $\square$

**The minimal certificate.** The natural candidate is the *cut set* $K(r)=\bigcup_{g}g(\partial D_1\cup\partial D_2)$, the smallest set satisfying (C1)–(C2). The obvious "if" direction also holds: if $GG_5(r)$ is finite, then $K(r)$ is a finite union of arcs, because each element is a piecewise isometry with finitely many circular pieces. So computing $K(r)$ is the canonical finite test of finiteness at a single radius.

---

## 5. Part B: finiteness up to $r_\ast$, by an exact finite computation

### 5.1 The computation

Program: `certify.py` (with `z5.py`; Part A is `partA.py`), kept in the working session's scratch directory `t4/`, not in this repository. The description below is complete enough to re-implement it. Input: a rational $\delta$, with $r^2=\rho:=3+\varphi-\delta$. It computes $K(r)$ by closure:
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

### 5.2 Results

**Table 5.1.** Computation of the cut set $K(r)$ at $r^2=3+\varphi-\delta$. "Pieces" are stored arcs before merging adjacent ones. $\max|\sigma(c)|$ is the largest internal-space modulus of a circle centre.

| $\delta$ | $r$ | $r_c-r$ | closed | circles | pieces | endpoints on $\partial D_p$ / (C4) failures | $\max|\sigma(c)|$ | $\delta\cdot\max|\sigma(c)|$ | run time |
|---|---|---|---|---|---|---|---|---|---|
| $13/5$ | 1.42058 | 0.72839 | yes | 54 | 112 | 68 / 0 | 7.3 | 19.0 | 0.1 s |
| $9/10$ | 1.92822 | 0.22074 | yes | 466 | 2 040 | 356 / 0 | 18.2 | 16.4 | 3 s |
| $9/20$ | 2.04158 | 0.10738 | yes | 1 722 | 10 303 | 1 000 / 0 | 37.6 | 16.9 | 14 s |
| $3/10$ | 2.07799 | 0.07097 | yes | 5 044 | 35 667 | 2 024 / 0 | 57.6 | 17.3 | 52 s |
| $1/5$ | 2.10191 | 0.04705 | yes | 11 606 | 185 541 | 3 744 / 0 | 89.1 | 17.8 | 291 s |
| $3/20$ | 2.11377 | 0.03519 | yes | 30 776 | 496 587 | 5 636 / 0 | 156.4 | 23.5 | 787 s |
| $1/10$ | 2.12557 | 0.02339 | yes | 50 714 | 1 437 580 | 9 228 / 0 | 188.3 | 18.8 | 2244 s |
| $3/40$, $1/20$ | | | not finished (cap) | | | | | | |

In every finished run: no tangency occurred, the interval precision never had to be raised, and (C4) had no failures. The run at $9/10$ was also done with an earlier version of the program that called the exact equality test on every comparison (345 586 exact tests). It gave identical output.

**Theorem B (proved modulo the computation of Table 5.1).** $GG_5(r)$ is finite for every $r\le r_\ast$, where $r_\ast^2=3+\varphi-\delta_\ast$ with $\delta_\ast=1/10$, i.e. $r_\ast\approx 2.12557$ and $r_c-r_\ast\approx 0.0234$.

*Proof.* The run for $\delta_\ast$ terminates and outputs $K(r_\ast)$ satisfying (C1)–(C4). Theorem 4.2 then gives finiteness at $r_\ast$, and group monotonicity (§2) extends it to every $r'\le r_\ast$. $\square$

**Remarks.**
- The circle counts at $\delta=13/5$, $3/10$, $1/5$ and $1/10$ (54, 5044, 11606, 50714) agree exactly with an independent floating-point implementation of the same closure (`t4/arcs_float.py`), which merges arcs numerically. That is a consistency check, not part of the proof.
- In every run, all coincidences of endpoints were between identical symbols. The circumcentre equality test was never needed to identify two different symbols.

### 5.3 Why the computation cannot reach $r_c$

The size of $K(r)$ grows like a power of $\delta^{-1}$ (Table 5.1). The internal extent of the circle centres grows like $\delta^{-1}$, consistent with the orbit-of-$0$ data in `twodisk_arith.md` §3.2, where $R\cdot\delta$ stays bounded. Each factor $\varphi^3$ in $\delta$ multiplies the work by a roughly constant factor. So no single finite computation reaches $r_c$. A proof of (B) on all of $(r_\ast,r_c)$ needs an induction along the renormalization (§6).

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

  Sources: `twodisk_experiments.md` E3, `twodisk_arith.md` §3.2, and the exact thresholds in `twodisk_exp/exact5.json`. The first orbit-of-$0$ threshold is $\delta_1=0.8541=4.618-3.764$, i.e. $r_1^2=7-2\varphi=|2-\zeta|^2$.

**6.2 Critical interval exchange.**
- The induced dynamics on the chord $E'E$ is the rotation by $2\varphi^{-1}$ on a circle of length $2$ (§3.3). Its rotation number $\varphi^{-1}$ is a fixed point of the Gauss map.
- So its first-return map to a sub-interval of relative length $\varphi^{-1}$ is again a rotation with the same rotation number: the standard golden renormalization, with period one and scale $\varphi$.
- Three steps of this 1-D renormalization give $\varphi^3$, the scale of the 2-D pattern. In the measured threshold sequence there are 2–3 jump types per factor $\varphi^3$ (`twodisk_experiments.md` E3).
- That the 2-D minimal period is three 1-D steps is an observation, not a proved statement.

**6.3 Geometry of the critical configuration (proved).**
- At $r=r_c$ the boundary circles pass through the lattice points $\pm E$ (the chord's ends) and through the lens corners $\pm(\zeta-\zeta^{-1})$.
- Every word of §3 touches a boundary circle at one of these points.

**6.4 The obstruction to an exact renormalization off criticality.**
- A similarity of ratio $\varphi^{3}$ maps circles of radius $r$ to circles of radius $\varphi^3r$. So no similarity can conjugate $GG_5(r)$ restricted to a small region to $GG_5(r')$ restricted to a larger one, for $r$ and $r'$ near $r_c$.
- Near the accumulation point, at depth $k$, the boundary is a circle that deviates from its tangent line by $O(\varphi^{-6k})$ across a region of size $\varphi^{-3k}$.
- Consequently the renormalization can be exact only *combinatorially and asymptotically*. This matches the threshold ratios converging to $\varphi^3$ rather than being equal to it.

**Conjecture R (renormalization).** There exist a compact region $U\ni E$, a finite set of words, and $k_0$ with the following property. For each $k\ge k_0$, the combinatorial type of $K(r)$ inside $\varepsilon^{k}$-scaled copies of $U$ around $E$ (and the symmetric points), for $r^2\in[r_c^2-\delta_{k},\,r_c^2-\delta_{k+1}]$, is the image under $z\mapsto E+\varepsilon(z-E)$ of the type at level $k-1$.

Here combinatorial type means:
- the set of circles, as centres modulo the scaling;
- the cyclic order of the arc endpoints on each circle.

The correction from curvature never changes the sign of any of the finitely many disk tests that define the type, once $k\ge k_0$. Conjecture R plus Table 5.1 at level $k_0$ would prove (B) by induction on $k$.

**Template for $n=8,10,12$.** The same objects are expected with:

| $n$ | field | scale unit | $r_c^2$ (conjectured) |
|---|---|---|---|
| 8 | $\mathbb Q(\sqrt2)$ | $1+\sqrt2$ | $10-5\sqrt2$ |
| 10 | $\mathbb Q(\sqrt5)$ | $\varphi^3$ | $4-\varphi$ |
| 12 | $\mathbb Q(\sqrt3)$ | $2+\sqrt3$ | $40-22\sqrt3$ |

These are measured in `twodisk_experiments.md` E3. The certificate of Theorem 4.2 and the program of §5 carry over verbatim: replace $\mathbb Z[\zeta_5]$ by $\mathbb Z[\zeta_n]$ and $\mathbb Q(\sqrt5)$ by the real quadratic field. For $n=8$ and $12$ the paper's infinite-orbit constructions are limit-point arguments, not finite interval exchanges. Part A for those $n$ therefore needs a new exact construction, for example an invariant segment found at $r_c$ in the computed cut set.

---

## 7. Attempted routes that did not close

1. **A simple window (approach (i)).** The internal-space images of orbits below $r_c$ are not filled by a fixed polygon or union of disks scaled with $\delta^{-1}$. The filling fraction of orbit points in the natural window decreases as $r\uparrow r_c$ (from $0.029$ to $0.012$ for $n=5$; `twodisk_experiments.md` E4). The invariant set is fractal, so no describable window $W(r)$ was found. Lemma 4.1 still reduces (B) to the existence of *some* compact invariant window, and $K(r)$ is the finite combinatorial substitute used in §5.
2. **Exact periodic renormalization (approach (ii)).** It is exact only at $r_c$, for the curvature reason in §6.4. At $r_c$ itself the group is infinite, so a renormalization there does not by itself control $r<r_c$.
3. **Direct certification along $r_k\uparrow r_c$ (approach (iii)).** It is carried out for finitely many $k$ (Table 5.1). It cannot be continued indefinitely without the uniform pattern of Conjecture R, because the computation grows like a power of $\delta^{-1}$.
4. **Literature (approach (iv); cited from memory, not re-checked).**
   - The closest proved results are global-stability theorems for single planar piecewise isometries or discretized rotations with quadratic rotation parameters, proved by self-similar domain-exchange renormalization:
     - Adler, Kitchens and Tresser (ETDS 2001), piecewise affine maps of the torus;
     - Kouptsov, Lowenstein and Vivaldi, "Quadratic rational rotations of the torus and dual lattice maps" (Nonlinearity 2002), the cases $q=5,8,10,12$;
     - Akiyama, Brunotte, Pethő and Steiner, "Periodicity of certain piecewise affine planar maps" (Tsukuba J. Math. 2008), all orbits periodic for the quadratic parameters $\lambda=\pm\varphi^{\pm1},\pm\sqrt2,\pm\sqrt3$, i.e. exactly the $n=5,10,8,12$ cases;
     - Goetz and Poggiaspalla, and Lowenstein, Kouptsov and Vivaldi, for rotations by $\pi/7$.
   - None of these applies directly. They treat one map on a fixed polygonal domain at one parameter. $GG_5(r)$ is a two-generator group, gated by disks, in a one-parameter family whose boundaries are curved.
   - The Akiyama–Brunotte–Pethő–Steiner method is the best template. One finds a finite set of polygonal "atoms" and an exact induced map that reproduces itself after scaling by the unit. The new ingredient needed here is control of the curvature correction uniformly in $k$ (Conjecture R).
   - Reduction to the single map $ab^{-1}$, which the paper mentions, would not suffice for group finiteness in any case. Finiteness of the orbits of one element does not bound the orbits of the group.

---

## 8. Status and gaps

| claim | status |
|---|---|
| Lemma 1.1, 1.2; §2 monotonicity | proved (§2 cites refereed notes) |
| Theorem A: infinite for all $r\ge r_c$ | **proved**; every arithmetic step verified exactly (`t4/partA.py`) |
| Lemma 4.1 (window criterion; $\mathcal T$ finite $\Rightarrow$ group finite) | proved |
| Theorem 4.2 (cut-set certificate) | proved |
| Theorem B: finite for $r\le r_\ast$ | **proved modulo the computation of §5**. Exact except for strict angle comparisons, which use certified interval arithmetic |
| finite for $r_\ast<r<r_c$ | **open**; strongly supported numerically by orbit scans up to $\delta\approx4\cdot10^{-3}$ (`twodisk_arith.md` §3.2) and the paper's searches |
| Conjecture R | conjecture, with the evidence of §6 |
| infinite orbit exactly at $r_c$ (paper's footnote 4) | proved here for $n=5$ (Theorem A) |

**Gaps and caveats, from my own adversarial check.**
1. The computation of §5 was written and run by the same author as this note. It has not been re-implemented independently. In particular the cyclic-interval logic (intersection and subtraction of arcs) deserves an independent re-check. The exact agreement with the floating-point implementation at $\delta=3/10$ is reassuring but not a proof.
2. Strict angle comparisons rely on `mpmath.iv` being correctly outward-rounded for `sqrt` and `atan2`. That is standard but is trust in a library.
3. (C4) is checked only for endpoints not shared with an adjacent stored piece on the same circle. Pieces that meet at a common endpoint form one maximal arc, so that is the right condition. The check matches endpoints by exact symbol equality.
4. Theorem A's statement "the group is infinite" uses only one orbit. It does not need, and does not prove, anything about the structure of $GG_5(r)$ beyond infinitude.
5. Nothing here shows that $r_c$ is the critical radius of the *group*. That requires (B) on $(r_\ast,r_c)$.

---

## 9. What a Lean formalization would need

1. **$\mathbb Z[\zeta_5]$ as $\mathbb Z^4$** with the reduced multiplication, conjugation, and the map to $\mathbb C$. Also a decision procedure for the sign of $\alpha+\beta\varphi$ (`Real.sqrt 5` facts plus `norm_num`/`decide` on rationals).
2. **The generators** as `Equiv.Perm ℂ`, defined piecewise from closed disks, and the left-to-right word action.
3. **Part A:**
   - Lemma 1.2 (convexity, `Convex.segment_subset`);
   - the three words as explicit lists, checked letter by letter by `decide` on the integer data;
   - the irrational rotation: injectivity of $k\mapsto 2k\varphi^{-1}\bmod 2$ from `irrational_sqrt_five` or `Irrational` lemmas;
   - "infinite orbit $\Rightarrow$ infinite group" (`Set.Infinite.of_image` style).
4. **Part B, finite range:**
   - the cell-decomposition argument of Theorem 4.2. This is the main formalization cost: finite unions of arcs, regular points, components of complements. A cheaper route for Lean is Lemma 4.1(3) with an explicit finite $\mathcal T(r)$ and a certificate that $\mathcal T(r)$ is closed. That needs region-emptiness proofs for intersections of disks and disk complements, which may be harder;
   - the certificate data from §5, exported as a list of circles and arcs with symbolic endpoints;
   - a verified checker for (C1)–(C4), with exact arithmetic for equalities and verified interval arithmetic (or exact nested-square-root sign tests in the tower $\mathbb Q(\sqrt5,\sin72^\circ,h_1,h_2)$) for orderings;
   - group monotonicity from `boundary-contact.md`.
5. **Part B, full:** Conjecture R would have to be proved first. A Lean proof would then be an induction on the level $k$ with explicit error bounds for the curvature correction.
