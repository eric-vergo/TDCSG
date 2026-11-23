# The critical radius of $GG_8$

Authors: Eric Vergo, Claude

**Statement.** Let $\zeta=e^{2\pi i/8}$, $\varepsilon=\sqrt2-1$ and $r_c=\sqrt{10-5\sqrt2}\approx1.711412$, the paper's conjectured critical radius. The target theorem is:

> (A) $GG_8(r)$ is infinite for every $r\ge r_c$; and (B) $GG_8(r)$ is finite for every $r<r_c$.

**Status.**
- **(A) is proved, in writing and in Lean.** The Lean theorems are `TDCSG.CriticalRadius.mem_orbit_pStar_eight_pow`, `infinite_orbit_pStar_eight` and `infinite_GG_eight` (statements in `TDCSG/CriticalRadius/Statements.lean`; the finite closure data of Appendix A are checked by kernel reduction, `decide +kernel`, in `TDCSG/CriticalRadius/Eight.lean`), which give `1 ≤ criticalRadius 8 ≤ √(10 - 5√2)`. The written proof follows. The infinite orbit is the orbit of the lattice point $p^\ast=1-2\zeta+\zeta^2-\zeta^3=-1+(2+i)(1-\zeta)$. It lies exactly on $\partial D_1$ when $r=r_c$, since $|p^\ast+1|^2=5|1-\zeta|^2=10-5\sqrt2$. For every $r\ge r_c$ the orbit of $p^\ast$ contains the points $p^\ast+i(4\sqrt2-4)\varepsilon^k$ for all $k\ge0$ (Theorem A, §2.5). These points accumulate at $p^\ast$ along a straight vertical line, at ratio $\varepsilon$. This is consistent with the limit point and the scale of the paper's "path from the centre to the boundary"; whether it is that path is not shown (§2.6). The mechanism is a one-dimensional self-similar structure on a chord through $p^\ast$: 31 partial isometries of the chord, each realized by an explicit group word, form a family that is closed under rescaling by $\varepsilon$ about $p^\ast$. Every disk test, domain endpoint and composition behind this closure was checked in exact arithmetic. The data are listed in full in Appendix A, so they can be re-checked independently.
- **(B) is open.** It is proved only on an initial range $r\le r_\ast$, with $r_\ast^2=r_c^2-\delta_\ast$, by an exact finite computation (§3) combined with the already-refereed group monotonicity.
  - The refereed certificate is at $\delta=1/7$ ($r\approx1.669154$). Like every certified range, it is proved modulo the computation and has no Lean counterpart.
  - This note's own exact certificates reach $\delta_\ast=1/14$ ($r_\ast\approx1.690415$, Table 3.1); those beyond $\delta=1/7$ are not refereed.
  - The deepest certified range is recorded in [`../certificates.md`](../certificates.md): the repository's Lean engine generates and independently checks a certificate at $\delta=1/36$, giving finiteness for $r\le1.703278$, an open window of length $r_c-r\approx0.008135$, modulo that computation. The best certified radius is now $\delta=547/25000=0.02188$ ($r\le1.705008$, open window $0.006404$), from a symmetry-reduced closure checked with (C1)–(C4) ([`../relative-certificates.md`](../relative-certificates.md) §§7, 10).
  - The window between the certified radius and $r_c$ is not proved.
- **Refereeing.** This note was independently refereed; see `referee-report-critical-radius-n8-n12.md` in this directory. The referee reproduced Part A fully and exactly, from Appendix A and the definitions, including end-to-end checks that expand the induction into explicit group words for $k\le7$ and apply them letter by letter with the true generators. It reproduced the Theorem B certificates at every table radius up to $\delta=1/7$ with its own closure program, which used floating-point comparisons; all canonical invariants agree.
- **Is $r_c$ the exact threshold?** What is proved is $r_\ast\le\inf\{r: GG_8(r)\text{ infinite}\}\le r_c$. The closed form is confirmed as an *upper bound* for the critical radius, and as the exact radius at which this particular mechanism switches on: $p^\ast$ enters $D_1$ exactly at $r_c$. Whether some other point already has an infinite orbit at a radius in $(r_\ast,r_c)$ is not excluded. The numerical evidence (§5) says no.

Throughout, "verified exactly" means that every equality, and the sign of every real number used, is decided by integer and rational arithmetic in $\mathbb Q(\sqrt2)$ or in towers $\mathbb Q(\sqrt2)(\sqrt{H_1},\sqrt{H_2})$ with $H_i\in\mathbb Q(\sqrt2)$. No floating-point decision enters any proof step. Floats are used only to *search* for the data that are then checked.

---

## 1. Setting and notation

- $\zeta=e^{2\pi i/8}=(1+i)/\sqrt2$. Then $\sqrt2=\zeta-\zeta^3$ and $i=\zeta^2$.
- $D_1,D_2$ are the closed disks of radius $r$ centred at $-1$ and $+1$.
- $A(z)=-1+\zeta^{-1}(z+1)$ and $B(z)=1+\zeta^{-1}(z-1)$ are the global clockwise rotations by $2\pi/8$.
- $a=A$ on $D_1$ and $a=\mathrm{id}$ off $D_1$; $b=B$ on $D_2$ and $b=\mathrm{id}$ off $D_2$.
- $GG_8(r)=\langle a,b\rangle$. Inverses are written as capitals: $\mathtt A=a^{-1}$, $\mathtt B=b^{-1}$.
- **Words are read left to right**: the word $\mathtt{bbab}$ applies $b$, then $b$, then $a$, then $b$.
- The scale unit is $\varepsilon=\sqrt2-1=\tan(\pi/8)$. It is the fundamental unit of $\mathbb Z[\sqrt2]$ up to sign and inversion, with Galois conjugate $\bar\varepsilon=-1-\sqrt2$.

**Arithmetic.**
- Elements of $\mathbb Z[\zeta]$ are integer vectors $(x_0,x_1,x_2,x_3)$ meaning $\sum x_j\zeta^j$, with $\zeta^4=-1$.
- For $w=\sum x_j\zeta^j$: $\operatorname{Re}w=x_0+\tfrac{x_1-x_3}{2}\sqrt2$, $\operatorname{Im}w=x_2+\tfrac{x_1+x_3}{2}\sqrt2$, and $|w|^2=\sum x_j^2+(x_0x_1+x_1x_2+x_2x_3-x_0x_3)\sqrt2$.
- The sign of $\alpha+\beta\sqrt2$ with $\alpha,\beta\in\mathbb Q$ is decided by comparing $\alpha^2$ with $2\beta^2$ when $\alpha$ and $\beta$ have opposite signs.
- The sign of $\alpha+\beta\sqrt H$ with $\alpha,\beta,H\in\mathbb Q(\sqrt2)$, $H\ge0$, is decided the same way, by one sign test in $\mathbb Q(\sqrt2)$. Two radicals are handled by squaring once more.

**Lemma 1.1 (convexity).** Let $[x,y]$ be a segment, $g\in\{a^{\pm1},b^{\pm1}\}$ with disk $D$, and suppose $x,y\in D$. Then $[x,y]\subseteq D$, and $g$ acts on $[x,y]$ as the global rotation. *Proof.* Disks are convex. $\square$

**Definition 1.2 (word valid on a segment).** A word $w=g_1\cdots g_\ell$ is *valid* on a segment $\sigma$ if, for each $j$, the image of $\sigma$ under the global rotations of $g_1,\dots,g_{j-1}$ lies in the disk of $g_j$. Every letter is thus required to *rotate* the whole segment; a letter is never allowed to act as the identity. This is what makes an endpoint check sufficient: "inside a disk" is a convex condition, while "wholly outside a disk" is not. So by Lemma 1.1 it suffices to check validity at the two endpoints. Then $w$ acts on $\sigma$ as the composite isometry $x\mapsto\zeta^jx+t$, and $w(y)\in O(y)$ for every $y\in\sigma$.

If a word is valid on $\sigma$ at radius $r_0$, it is valid on $\sigma$ at every $r\ge r_0$, with the same action, because the disks only grow.

---

## 2. Part A: an infinite orbit for every $r\ge r_c$

### 2.1 The critical point

Put
$$p^\ast=-1+(2+i)(1-\zeta)=1-2\zeta+\zeta^2-\zeta^3=\Big(1-\tfrac{\sqrt2}2\Big)-i\Big(\tfrac{3\sqrt2}2-1\Big)\approx0.292893-1.121320\,i.$$

Checked exactly:
- $|p^\ast+1|^2=|2+i|^2\,|1-\zeta|^2=5(2-\sqrt2)=10-5\sqrt2=r_c^2$. So $p^\ast\in\partial D_1$ exactly when $r=r_c$, $p^\ast\in\operatorname{int}D_1$ for $r>r_c$, and $p^\ast\notin D_1$ for $r<r_c$.
- $|p^\ast-1|^2=6-3\sqrt2\approx1.757<r_c^2$. So $p^\ast\in\operatorname{int}D_2$.

This identifies the arithmetic content of the closed form: $r_c^2=5\,|1-\zeta|^2$ is the squared distance from $-1$ to the lattice point $p^\ast$.

There are exactly 16 lattice points on $\partial D_1$ at $r=r_c$, namely $-1+(2\pm i)(1-\zeta)\zeta^k$ for $k\bmod 8$. *Proof.*
1. $\mathbb Z[\zeta_8]$ is a principal ideal domain. In it, $5=(2+i)(2-i)$ with both factors prime: the order of $5$ mod $8$ is $2$. And $1-\zeta$ is the prime above $2$.
2. So $w\bar w=5(2-\sqrt2)=(2+i)(2-i)(1-\zeta)(1-\bar\zeta)$ forces $w=u(2\pm i)(1-\zeta)$ with $u\bar u=1$.
3. Then $u$ is a root of unity, by Kronecker's theorem. $\square$

These 16 points are the images of $p^\ast$ under powers of $a$ (for $r\ge r_c$) and under complex conjugation. Conjugation maps orbits to orbits, because $\bar{\ }\circ a\circ\bar{\ }=a^{-1}$, and likewise for $b$. So everything proved below for $p^\ast$ holds for all 16. The map $z\mapsto-z$ gives the corresponding points on $\partial D_2$.

### 2.2 The critical chord

Let $\ell=\{p^\ast+it: t\in\mathbb R\}$, the vertical line through $p^\ast$.
- $\ell\cap D_1$ is the segment $t\in[0,\,3\sqrt2-2]$, from $p^\ast$ to $\bar p^\ast$. Both endpoints lie on $\partial D_1$ at $r=r_c$.
- $\ell\cap D_2$ is the chord $J$: $t\in[T_0-Y,\,T_0+Y]$, where $T_0=\tfrac{3\sqrt2}2-1$ and $Y=\sqrt{19/2-5\sqrt2}$, i.e. $t\in[-0.437183,\,2.679824]$. Its endpoints are not in $\mathbb Q(\zeta)$, since $19/2-5\sqrt2$ is not a square in $\mathbb Q(\sqrt2)$: its norm is $161/4$.
- So $p^\ast$, at $t=0$, is an interior point of $J$, where the circle $\partial D_1$ crosses $J$.

The coordinate $t$ identifies $\ell$ with $\mathbb R$. A word whose composite rotation is $\zeta^0$ or $\zeta^4=-1$, and which maps one point of $\ell$ into $\ell$, maps $\ell$ to $\ell$ as $t\mapsto t+c$ or $t\mapsto c-t$, with $c\in\mathbb Z[\sqrt2]$. For such a word $w$, its **domain** $D_w$ is the set of $t\in J$ such that $w$ is valid at $p^\ast+it$ and $w(p^\ast+it)\in J$.

Each validity condition says that a point moving affinely along a line lies in a closed disk. That is a quadratic inequality $t^2+2qt+k\le0$ with $q,k\in\mathbb Q(\sqrt2)$. So $D_w$ is a closed interval whose endpoints have the form $u\pm\sqrt d$ with $u,d\in\mathbb Q(\sqrt2)$, and they are computed exactly. The relevant endpoints turn out to lie in $\mathbb Q(\sqrt2)$ or in $\mathbb Q(\sqrt2)\big(\sqrt{19/2-5\sqrt2}\big)$; see Appendix A.

*Observation (not used in the proof).* In a 2.4-million-point exact computation of the orbit of $0$ at $r=r_c$, the 1520 orbit points on $\ell$ fill $J$ with uniform density. That is how $J$ was found.

### 2.3 The renormalization lemma

Let $S(t)=\varepsilon t$, the similarity of $\ell$ of ratio $\varepsilon$ centred at $p^\ast$. On the lattice it is $z\mapsto p^\ast+\varepsilon(z-p^\ast)$, an automorphism of the coset structure, because $\varepsilon$ is a unit.

**Lemma 2.1 (renormalization).** Let $\mathcal F$ be a finite set of pairs $(f,D_f)$. Each $f$ is an isometry of $\mathbb R$ and each $D_f$ a closed interval. Suppose:
1. **(Realization)** for each $f$ there is a word $w_f$ valid on $\{p^\ast+it: t\in D_f\}$ at radius $r$ and acting there as $t\mapsto f(t)$;
2. **(Closure)** for each $f\in\mathcal F$, the interval $\varepsilon D_f$ is a finite union of closed intervals $I_1,\dots,I_m$. For each $I_j$ there is a sequence $g_1,\dots,g_L\in\mathcal F$ such that, for every $t\in I_j$, the points $t_0=t$, $t_i=g_i(t_{i-1})$ satisfy $t_{i-1}\in D_{g_i}$, and $t_L=\varepsilon f(t/\varepsilon)$.

Then for every $k\ge0$, every $f\in\mathcal F$ and every $t\in\varepsilon^kD_f$, the point $p^\ast+i\varepsilon^kf(t/\varepsilon^k)$ lies in the $GG_8(r)$-orbit of $p^\ast+it$.

*Proof.* Induction on $k$; write $O(t)$ for the orbit of $p^\ast+it$.
1. $k=0$ is (Realization).
2. Assume the claim for $k$. Let $t\in\varepsilon^{k+1}D_f$ and $s=t/\varepsilon^k\in\varepsilon D_f$. Choose $I_j\ni s$ and its sequence $g_1,\dots,g_L$, with points $s_0=s,\dots,s_L=\varepsilon f(s/\varepsilon)$ and $s_{i-1}\in D_{g_i}$.
3. Then $\varepsilon^ks_{i-1}\in\varepsilon^kD_{g_i}$. By the induction hypothesis, $\varepsilon^kg_i(s_{i-1})=\varepsilon^ks_i$ lies in $O(\varepsilon^ks_{i-1})$.
4. Chaining over $i$ gives $\varepsilon^ks_L=\varepsilon^{k+1}f(t/\varepsilon^{k+1})\in O(t)$. $\square$

**Corollary 2.2.** If some $f\in\mathcal F$ has $0\in D_f$ and $f(0)=c\neq0$, then the orbit of $p^\ast$ contains $p^\ast+ic\varepsilon^k$ for all $k\ge0$. These points are pairwise distinct, so the orbit of $p^\ast$ is infinite.

### 2.4 The certificate

Appendix A lists a family $\mathcal F$ of **31 words**. For each word it gives its type $t\mapsto\pm t+c$, with $c\in\mathbb Z[\sqrt2]$, its exact domain $D_f$, and, for the closure, the decomposition of $\varepsilon D_f$ into pieces with the sequence of family members used on each piece. There are 46 pieces and 172 composition steps in total; every sequence has length at most 4. (Appendix A also lists 3 redundant one-point pieces, in rows 10, 13 and 15. Each consists only of the right endpoint of $\varepsilon D_f$, which the previous piece already reaches. They are valid but play no role, and are ignored in the counts and in Lemma 2.3. The Lean data `TDCSG.Eight.pieces` include them: 49 pieces and 184 steps, the 3 one-point pieces having sequences of length 4.) The words have length at most 12.

**Lemma 2.3 (exact check).** At $r=r_c$:
1. For each of the 31 words, the word is valid at both endpoints of the listed interval $D_w$, hence on all of it. (The listed intervals are in fact the maximal domains, but the proof uses only validity on them.) The endpoints are computed as roots of the binding quadratic constraints and compared exactly. Validity at an endpoint $u+v\sqrt d$ is the sign of an element of $\mathbb Q(\sqrt2)(\sqrt d)$.
2. The composite rotation of each word is $\pm1$, and the translation part is the listed $c$, exactly in $\mathbb Z[\sqrt2]$.
3. For each family member $f$ and each listed piece $[x,R]\subseteq\varepsilon D_f$, with sequence $g_1,\dots,g_L$:
   - every intermediate image interval lies in the next domain $D_{g_i}$, checked exactly by comparing endpoints in towers with at most two radicals;
   - the composite equals $t\mapsto\varepsilon f(t/\varepsilon)$ exactly;
   - consecutive pieces share endpoints and cover $\varepsilon D_f$; pieces listed after full coverage is reached are ignored.

*Proof.* Exact computation: program `verify_closure_n.py` with the module `exactn.py`, data file `closure_bbab.pkl`, run as `python3 -I verify_closure_n.py 8 closure_bbab.pkl`. Output:
```
all 31 maps: exact domains agree with float; words valid at both endpoints
closure verified exactly; 172 composition steps
```
The programs and data are in the working session's scratch directory `t4_8/`, not in this repository. Appendix A contains everything needed to redo the check from scratch. $\square$

**How the family was found.** The search used floating point. It is not part of the proof, but it is recorded so that it can be repeated.
1. All reduced words of length at most 12 were enumerated depth first. For each prefix, the floating-point interval of $t\in J$ on which every letter so far is valid was tracked, and a branch was pruned as soon as that interval became empty.
2. Every word whose composite maps $\ell$ to $\ell$ was kept with its domain, giving 218 maps.
3. Starting from the seed, the closure was grown by searching, for each member $f$, depth-first compositions of at most 4 library maps realizing $t\mapsto\varepsilon f(t/\varepsilon)$ on $\varepsilon D_f$. The covering was greedy: each piece is extended as far right as some composition reaches.
4. Members whose rescaled version could not be found were discarded and the search was repeated.
5. The flips with $c=8\sqrt2-8$ had to be excluded. The resulting 31-member family is closed.

The first entry of Appendix A is the **seed** $\mathtt{bbab}$. It acts on $\ell$ as $t\mapsto(4\sqrt2-4)-t$, the reflection in the point $t=2\sqrt2-2$. Its domain is $[T_0-Y,\,T_0+Y-2]\approx[-0.437,\,0.680]$, which contains $t=0$.

### 2.5 Theorem A

**Theorem A.** For every $r\ge r_c=\sqrt{10-5\sqrt2}$, the orbit of $p^\ast=1-2\zeta+\zeta^2-\zeta^3$ under $GG_8(r)$ contains the pairwise distinct points
$$p^\ast+4i\,\varepsilon^{k+1}\qquad(k=0,1,2,\dots).$$
Hence the orbit is infinite and $GG_8(r)$ is infinite.

*Proof.*
1. At $r=r_c$, Lemma 2.3 gives the hypotheses of Lemma 2.1 for the 31-element family.
2. For $r>r_c$ no monotonicity theorem is needed. Every letter of every word rotates because the point lies in the closed disk at $r_c$; the disks only grow, so the same letters still rotate, with the same action (§1). The closure condition refers only to the fixed intervals $D_f$ and isometries $f$, so it still holds.
3. The seed has $0\in D_{\mathtt{bbab}}$ and $\mathtt{bbab}(0)=4\sqrt2-4=4\varepsilon\neq0$. Corollary 2.2 gives the points $p^\ast+4i\varepsilon\cdot\varepsilon^k$.
4. They are distinct because $0<\varepsilon<1$. An infinite orbit forces an infinite group. $\square$

**Remarks.**
1. *Where $r_c$ enters.* The seed itself does **not** need $p^\ast\in\partial D_1$. Its four disk tests at $p^\ast$ have squared distances $6-3\sqrt2,\ 6-3\sqrt2,\ 14-9\sqrt2,\ 22-15\sqrt2$ to the relevant centres (checked exactly), so $\mathtt{bbab}$ is valid at $t=0$ for every $r\ge\sqrt{6-3\sqrt2}\approx1.3256$. What needs $r=r_c$ is the family as a whole. The domains in Appendix A are the maximal domains at $r_c$, and at many of their endpoints the active constraint is a letter's disk test holding with equality at $r=r_c$. For example, along row 9 ($\mathtt{bbaabbaBABaB}$, domain $[0,3\sqrt2-4]$) started at $t=0$, the 7th letter $a$ and the 9th letter $\mathtt A$ are applied to the lattice points $-2+\zeta+2\zeta^2-2\zeta^3$ and $-\zeta+2\zeta^2-2\zeta^3$, which lie exactly on $\partial D_1$ at $r_c$ (squared distance $10-5\sqrt2$ from $-1$; they are among the 16 critical points of §2.1). This is where the closed-disk convention is used. For $r<r_c$ those domains shrink, Lemma 2.3 as stated fails, and the argument says nothing.
2. *Independent sanity check (not part of the proof).* An exact breadth-first search of the orbit of $p^\ast$ at $r_c$, capped at $3\cdot10^6$ points, finds $p^\ast+4i\varepsilon^{k+1}$ for $k=0,\dots,6$. The internal-space modulus grows like $|\bar\varepsilon|^{k}=(1+\sqrt2)^k$, as it must.
3. *The orbit of $0$.* The same kind of search finds that at $r_c$ the orbit of $0$ contains $p^\ast+i\varepsilon^m$ for $m=0,\dots,8$, reached by words of lengths $3,1,7,9,27,57,143,337,819$, growing like $(1+\sqrt2)^m$. Whether the orbit of $0$ is infinite at $r_c$ is not proved here, although this strongly suggests it.

### 2.6 Relation to the paper's construction

The paper describes a path of segments that follows the fractal from a disk centre towards the boundary, with segments shrinking by $\sqrt2-1$. It obtains $r_c$ from the assumption that the path's limit point lies on the boundary. Theorem A replaces this by the following precise statements.
- **The limit point is the lattice point $p^\ast$, and it lies on $\partial D_1$ exactly at $r_c$**, by the identity $|p^\ast+1|^2=5|1-\zeta|^2$. No assumption is needed.
- **The self-similarity is exact and one-dimensional.** The renormalization is the similarity $z\mapsto p^\ast+\varepsilon(z-p^\ast)$ of the chord $J$. The induced pseudogroup of partial isometries of $J$ near $p^\ast$ reproduces itself under it (Lemma 2.3).
- **The construction stays inside the disks.** Every letter of every word is checked to be applied inside its closed disk. Validity is in fact all that is ever used.
- **Approach to the boundary.** The points $p^\ast+4i\varepsilon^{k+1}$ approach $p^\ast$ along $J$ from inside $D_1$. In the threshold sweep of the orbit of $0$ (`notes/engine.md`), the entering points at the main jumps of one type are $p^\ast+i\varepsilon^{2k+1}$. Exactly, these are $(1,27,-40,28)$ at $r^2=3117-2202\sqrt2$ and $(1,167,-238,168)$ at $r^2=112761-79732\sqrt2$. The jumps of the other type enter near the points $-1+(2-i)(1-\zeta)\zeta^{k}$.
- What was **not** reproduced: the paper's statement that consecutive segments "traverse angles of $\pi/8$". In the construction here the approach to $p^\ast$ is along a straight line. The paper's figure could not be inspected for this note. One observation (from the referee report): if "traverse angles of $\pi/8$" meant that consecutive segment vectors differ by the factor $\varepsilon e^{i\pi/8}$, the vertices could not all be orbit points of a lattice point, because differences of such orbit points lie in $\mathbb Z[\zeta_8]$ and $e^{i\pi/8}\notin\mathbb Q(\zeta_8)$. So either the paper's path is not made of orbit points, or "angle" means something else; in either case the straight-line mechanism here does not contradict the paper's text.

---

## 3. Part B: finiteness for $r\le r_\ast$

### 3.1 Two facts used (already proved and refereed)

From `boundary-contact.md` (Theorems 3.1 and 3.4) and `theorem1-converse.md` (Proposition 4.2):
- **Orbit monotonicity.** If $r'\le r$, then $O_{r'}(z)\subseteq O_r(z)$ for every $z$.
- **Group monotonicity.** If $GG_8(r)$ is finite, then $GG_8(r')$ is finite for every $r'\le r$.

So it suffices to certify finiteness at single radii. What is proved is the full group statement, $|GG_8(r)|<\infty$, not only finiteness of each orbit.

### 3.2 The cut-set certificate

The certificate is the one formulated for $n=5$ in `critical-radius-n5.md` (Theorem 4.2). Its proof is restated here and re-checked for $n=8$, because nothing in it depends on $n$.

**Theorem 3.1.** Fix $r>1$. Let $K\subset\mathbb C$ be a finite union of non-degenerate closed arcs of circles of radius $r$ such that:
- **(C1)** $\partial D_1\cup\partial D_2\subseteq K$;
- **(C2)** $A^{\pm1}(K\cap D_1)\subseteq K$ and $B^{\pm1}(K\cap D_2)\subseteq K$;
- **(C3)** no circle carrying an arc of $K$, other than $\partial D_p$ itself, is tangent to $\partial D_p$ ($p=1,2$);
- **(C4)** every endpoint of a maximal arc of $K$ (a connected component of $K\cap C$ for a circle $C$) that lies on $\partial D_p$ belongs to a maximal arc entering $\operatorname{int}D_p$ there.

Then $GG_8(r)$ is finite.

*Proof.*
1. **Invariance.** By (C2), $a(K)\subseteq K$ and $a^{-1}(K)\subseteq K$, so $a(K)=K$. Likewise $b(K)=K$.
2. **The singular set.** Let $V$ be the set of points of $K$ near which $K$ is not a single open arc. $V$ lies in the finite set of arc endpoints and pairwise intersections of the carrying circles.
3. **$a(V)=V$.** Let $x\in V$.
   - If $x\notin D_1$, then $a=\mathrm{id}$ near $x$.
   - If $x\in\operatorname{int}D_1$, then $a=A$ near $x$ and $A(K\cap D_1)=K\cap D_1$, so the local picture is carried to $A(x)$.
   - If $x\in\partial D_1$, some arc of $K$ on a circle $C\neq\partial D_1$ contains $x$. By (C3) it is transversal to $\partial D_1$. If $x$ is interior to it, the arc enters $\operatorname{int}D_1$. If $x$ is an endpoint, (C4) supplies a maximal arc entering $\operatorname{int}D_1$ at $x$. The image under $A$ of the part inside $D_1$ is an arc of $K$ on $A(C)\neq\partial D_1$ through $A(x)\in\partial D_1$. So $A(x)\in V$.
   - Hence $a(V)\subseteq V$. The same holds for $a^{-1},b^{\pm1}$, and $V$ is finite, so $a(V)=V$ and $b(V)=V$.
4. **Cells.** The points of $V$, the components of $K\setminus V$ (open arcs) and the components of $\mathbb C\setminus K$ are finitely many cells partitioning $\mathbb C$.
   - By (C1), a face lies in $\operatorname{int}D_1$ or outside $D_1$.
   - An edge not on $\partial D_1$ cannot meet $\partial D_1$, because a meeting point would be in $V$.
   - So each generator acts on each cell by a single isometry and maps it onto a cell.
5. **Finiteness.** By induction along words, every $g\in GG_8(r)$ acts on each cell $X$ by a single map $x\mapsto\zeta^jx+t$ carrying $X$ onto a cell: the letter applied at each step is the single isometry by which that generator acts on the current cell. This covers the singleton cells of $V$ as well.
   - For a bounded cell and a given target cell there are at most $8$ such maps, one for each $j$: a non-trivial translation cannot preserve a bounded set.
   - The unbounded face is fixed pointwise by every generator.
   - So $g$ is one of finitely many maps on each of finitely many cells, and $GG_8(r)$ is finite. $\square$

### 3.3 The computation

**Program.** `cut/cut.py` (closure) and `cut/verify.py` (certificate check), with the exact field module `cut/field.py`, in the scratch directory `t4_8/`. They were written independently of the $n=5$ programs, following the same design, with one change: all ordering decisions are exact here, not interval-arithmetic. During the closure the covered part of each circle is kept as a list of disjoint maximal arcs (a new piece is joined to stored arcs it touches), and only float angles are cached; exact data of an endpoint are recomputed on demand. This keeps memory near $1$–$2$ GB at the largest radii certified. Input: a rational $\delta$, with $r^2=\rho=(10-\delta)-5\sqrt2$.

**Closure.**
1. Start from the full circles $\partial D_1,\partial D_2$.
2. Repeatedly clip each new arc by $D_1$ and $D_2$, rotate the clipped parts by $A^{\pm1}$, respectively $B^{\pm1}$, and add the parts of the images not yet covered.
3. Stop when nothing new appears.

**Representation.**
- A circle is its centre $c\in\mathbb Z[\zeta]$.
- An arc endpoint is a symbol $(e,s)$, $e\in\mathbb Z[\zeta]$, $s=\pm1$, meaning the point $c+\tfrac d2(1+ish)$ with $d=e-c$ and $h=\sqrt{4\rho/|d|^2-1}$.
- A rotation $R$ about $p$ maps the symbol $(e,s)$ on circle $c$ to $(Re,s)$ on circle $Rc$.

**Exact decisions.**
- *Does a circle meet $\operatorname{int}D_p$?* That is $0<|c-p|^2<4\rho$, a sign in $\mathbb Q(\sqrt2)$. Tangency, i.e. equality, would abort the run. It cannot occur when $4\delta\notin\mathbb Z$, because $|c-p|^2\in\mathbb Z[\sqrt2]$ and $4\rho=(40-4\delta)-20\sqrt2$.
- *Order of points on a circle.* For $n=8$, $\operatorname{Re}d$ and $\operatorname{Im}d$ lie in $\mathbb Q(\sqrt2)$. So the vector from $c$ to an endpoint is $X+iY$ with $X,Y\in\mathbb Q(\sqrt2)+\mathbb Q(\sqrt2)\sqrt H$.
  - The angular order of two endpoints is decided by the half-plane of each vector, and then by the sign of the cross product.
  - That cross product has the form $\alpha+\beta\sqrt{H_1}+\gamma\sqrt{H_2}+\delta'\sqrt{H_1H_2}$, and its sign is decided exactly by two squarings.
  - Equality of endpoints given by different symbols is decided by the same test.
- *Float filter.* During the closure only, comparisons whose float angles differ by more than $10^{-9}$ are decided by floats, to save time. The closure output is then re-verified with no float decision at all:
  - **`verify.py`** merges the stored pieces into maximal arcs by exact endpoint equality;
  - checks (C1);
  - recomputes every clipped image of every maximal arc and checks exactly that it lies inside a single maximal arc of the target circle, which is (C2);
  - checks (C4) exactly, requiring the maximal arc *itself* to enter $D_p$;
  - checks (C3) through the tangency test.
  - Floats are used there only to propose which target arc to test first.

### 3.4 Results

**Table 3.1.** Cut set $K(r)$ at $r^2=r_c^2-\delta$. Circles, maximal arcs and (C4) endpoints are invariants of the minimal cut set $K(r)$. "Max $|\sigma(c)|$" is the largest internal-space modulus of a circle centre, with $\sigma:\zeta\mapsto\zeta^3$. Every listed certificate was checked by the exact verifier, with (C4) failures $0$ and no tangency.

| $\delta$ | $r$ | $r_c-r$ | circles | maximal arcs | (C2) image arcs checked | (C4) endpoints | max $\lvert\sigma(c)\rvert$ | exact verification |
|---|---|---|---|---|---|---|---|---|
| $1$ | 1.3889 | 0.3226 | 52 | 84 | 196 | 80 | 6.2 | **valid** |
| $1/2$ | 1.5585 | 0.1529 | 726 | 1 920 | 4 548 | 676 | 20.7 | **valid** |
| $1/3$ | 1.6111 | 0.1003 | 3 648 | 10 824 | 25 540 | 1 420 | 46.1 | **valid** |
| $1/5$ | 1.6519 | 0.0595 | 4 222 | 18 780 | 44 548 | 2 920 | 47.6 | **valid** |
| $1/6$ | 1.6620 | 0.0494 | 5 024 | 22 258 | 52 772 | 3 176 | 51.1 | **valid** |
| $1/7$ | 1.6692 | 0.0423 | 24 150 | 122 762 | 290 660 | 5 692 | 110.4 | **valid** |
| $1/10$ | 1.6819 | 0.0295 | 30 490 | 213 418 | 506 084 | 10 328 | 122.8 | **valid** (not yet refereed) |
| $1/12$ | 1.6869 | 0.0245 | 31 366 | 229 058 | 543 460 | 11 252 | 124.6 | **valid** (not yet refereed) |
| $1/13$ | 1.6888 | 0.0226 | 33 690 | 259 266 | 615 076 | 11 824 | 138.1 | **valid** (not yet refereed) |
| $1/14$ | 1.6904 | 0.0210 | 36 024 | 291 418 | 691 684 | 13 320 | 138.1 | **valid** (not yet refereed) |
| $1/16$ | 1.6931 | 0.0184 | not finished: stopped at the run's cap with 124 752 circles and 3.5 GB in use | | | | 262.5 | — |

The "(C2) image arcs checked" column counts the four images of the two boundary circles about their own centres, which the repository engine's checker skips; its counts are 4 lower. The engine closes $\delta=1/16$ and deeper radii, down to $\delta=1/36$ ([`../certificates.md`](../certificates.md) §5).

$\delta=1$ and $\delta=1/2$ have $4\delta\in\mathbb Z$, so tangency was possible in principle; the run would have aborted on one, and none occurred.

**Growth of the computation.** With the storage above, closure time / peak memory / exact-verification time were: $\delta=1/10$: 201 s / 1.1 GB / 795 s; $1/12$: 250 s / 1.25 GB / 856 s; $1/13$: 262 s / 1.5 GB / 977 s; $1/14$: 329 s / 1.7 GB / 1084 s. Between $1/7$ and $1/14$ the cut set grows slowly (circles $\times1.5$); between $1/14$ and $1/16$ it jumps by more than a factor of 3 in circles and in internal extent. The growth is in steps rather than smooth; the two observed jumps (between $1/6$ and $1/7$, and between $1/14$ and $1/16$) are a factor of about $2.3$ apart in $\delta$, consistent with one step per factor $1+\sqrt2$, i.e. one per level of §4.

**Theorem B (proved modulo the computation of Table 3.1).** $GG_8(r)$ is finite for every $r\le r_\ast$, where $r_\ast^2=10-5\sqrt2-\delta_\ast$ with $\delta_\ast=1/14$, i.e. $r_\ast\approx1.690415$. The certificates at $\delta\le1/10$ were produced after the referee's pass and are not yet refereed; the refereed certificate is $\delta=1/7$ ($r\approx1.669154$). The open window left by this table is $(r_\ast,r_c)$, of length about $0.0210$; the engine certificates of `../certificates.md` narrow it to about $0.008135$.

*Proof.* The certificate for $\delta_\ast$ satisfies (C1)–(C4), checked exactly. Theorem 3.1 gives finiteness at $r_\ast$, and group monotonicity extends it to all $r\le r_\ast$. $\square$

### 3.5 Why the computation does not reach $r_c$

- The size of $K(r)$ grows in steps, one per level, with an overall rate like a power of $\delta^{-1}$ (Table 3.1 and the growth paragraph). The limit reached here ($\delta=1/16$ did not finish) is a resource limit of this implementation, not an intrinsic one; the repository engine reaches $\delta=1/36$, and each further level costs roughly a constant factor more.
- The internal extent of the circle centres grows like $\delta^{-1}$, matching the orbit data: $R\cdot\delta$ stays bounded (`arithmetic.md` §3.2).
- So no single computation reaches $r_c$. A proof of (B) on all of $(r_\ast,r_c)$ needs an induction along the renormalization, discussed in §4.

---

## 4. Renormalization data

1. **Scale unit.** $\varepsilon=\sqrt2-1$, the fundamental unit. Multiplication by $\varepsilon$ contracts the physical coordinate by $\varepsilon$ and expands the internal one by $1+\sqrt2$.
2. **Critical point and chord.** $p^\ast=-1+(2+i)(1-\zeta)\in\partial D_1(r_c)$. The chord is $J=\ell\cap D_2$, $\ell=p^\ast+i\mathbb R$.
3. **Exact one-dimensional renormalization at $r_c$.** The family of Appendix A is closed under $t\mapsto\varepsilon t$ (Lemma 2.3). This is the precise sense in which the critical configuration is self-similar with ratio $\varepsilon$ about $p^\ast$.
4. **Threshold data** (exact sweep, `notes/engine.md`). The gaps $\delta_k=r_c^2-t_k$ at the large jumps have successive ratios $2.4065, 2.4110, 2.4129\to1+\sqrt2$, from below. No gap is exactly a unit multiple of an earlier one.
5. **Approach points.** The thresholds $t=3117-2202\sqrt2$ and $112761-79732\sqrt2$ are $|q+1|^2$ for $q=p^\ast+i\varepsilon^5$ and $q=p^\ast+i\varepsilon^7$. The orbit of $0$ reaches these points at exactly the radius where they enter $D_1$.
6. **Why the renormalization is exact only at $r_c$.** At $r<r_c$ the family's domains shrink: several of their endpoints are tight disk tests at $r_c$, among them letters applied at critical points on $\partial D_1(r_c)$ (§2.5, Remark 1), which leave $D_1$ for $r<r_c$. More generally, a similarity of ratio $\varepsilon$ maps circles of radius $r$ to circles of radius $\varepsilon r$. So off criticality the renormalization can only be asymptotic, as for $n=5$ (`critical-radius-n5.md` §6.4).

**Levels.** For $m\ge1$ put $q_m=p^\ast+i\varepsilon^m$ and $\delta_m=r_c^2-|q_m+1|^2>0$. So $q_m$ enters $D_1$ exactly at $r^2=r_c^2-\delta_m$; $\delta_m$ decreases to $0$ with $\delta_{m}/\delta_{m+1}\to1+\sqrt2$. For example $r_c^2-\delta_5=3117-2202\sqrt2$ and $r_c^2-\delta_7=112761-79732\sqrt2$, both thresholds of the orbit of $0$ (item 5). Say that $r^2=r_c^2-\delta$ is at **level $m$** if $\delta\in[\delta_{m+1},\delta_m)$. The **type of $K(r)$ at scale $\varepsilon^m$** means: the set of circles of $K(r)$ meeting the disk of radius $C\varepsilon^m$ about $p^\ast$ (for a fixed constant $C$), as centres taken modulo the map $z\mapsto p^\ast+\varepsilon^{-m}(z-p^\ast)$, together with the cyclic order of arc endpoints on each of them inside that disk.

**Conjecture R₈.** There are $C$ and $m_0$ such that for every $m\ge m_0$, the type of $K(r)$ at scale $\varepsilon^{m+1}$ for $r$ at level $m+1$ is the image under $z\mapsto p^\ast+\varepsilon(z-p^\ast)$ of the type at scale $\varepsilon^m$ for $r$ at level $m$, and the same holds at the symmetric images of $p^\ast$.

Conjecture R₈ alone does **not** imply (B). It describes $K(r)$ only in shrinking neighbourhoods of the critical points. To deduce finiteness one would also need: (i) that outside those neighbourhoods $K(r)$ has a fixed combinatorial type at each level, (ii) that (C1)–(C4) persist from one level to the next, and (iii) control of the curvature mismatch of item 6. Conjecture R₈ would reduce (B) to these statements and one certificate at level $m_0$.

**Conjecture F₈.** $GG_8(r)$ is finite for every $r<r_c$. Equivalently, $r_c$ is exactly the infimum of the radii with infinite group.

---

## 5. Is the closed form exactly the critical radius?

- **Proved:** $\inf\{r:GG_8(r)\text{ infinite}\}\in[r_\ast,r_c]$ with $r_\ast^2=r_c^2-1/14$ (refereed part: $r_c^2-1/7$), modulo the computation of §3; and with $r_\ast^2=r_c^2-1/36$ modulo the certificate of `../certificates.md`. The upper bound is proved in Lean.
- **Proved:** $r_c$ is exactly the radius at which the point $p^\ast$ starts to be moved by $a$. Above it, the orbit of $p^\ast$ is infinite.
- **Not proved:** that no point has an infinite orbit for $r\in(r_\ast,r_c)$. Possible failure modes would be another critical lattice point entering a disk at a smaller radius, or an infinite orbit at some radius in this window with no lattice point on a boundary circle.
- **Evidence against such failure:**
  - the exact threshold sweep of the orbit of $0$ (331 thresholds up to the cap) has gaps that decrease geometrically to $0$ at ratio $\to1+\sqrt2$, with $r_c$ as the only accumulation point;
  - exact orbit searches at $r^2=r_c^2-\delta$ terminate. For example, the orbit of $0$ has 468 071 points at $\delta=1/100$, and the orbit of $p^\ast$ has 290 810 points at $\delta=1/100$;
  - the cut-set closure terminates at every $\delta\ge1/14$ tried here, and in the repository engine at every $\delta\ge1/36$ tried.
  - This is evidence, not proof.

---

## 6. Status and gaps

Verdicts are those of the independent referee report (`referee-report-critical-radius-n8-n12.md`) unless marked otherwise.

| claim | status |
|---|---|
| Convexity lemma, renormalization Lemma 2.1, Corollary 2.2 | proved; refereed: correct |
| Lemma 2.3 (31-word family closed under $\varepsilon$) | proved by exact computation; refereed: correct, independently reproduced in full in exact arithmetic |
| Theorem A: $GG_8(r)$ infinite for all $r\ge r_c$; explicit infinite orbit of $p^\ast$ | **proved**; refereed: correct. **Proved in Lean** (`TDCSG.CriticalRadius.infinite_GG_eight`) |
| Theorem 3.1 (cut-set certificate) | proved; refereed: correct (re-proved by the referee) |
| Theorem B at $\delta=1/7$ | **proved modulo the computation of §3**, all decisions exact; refereed: correct as stated, certificate reproduced in floating point with matching invariants |
| Theorem B at $\delta_\ast=1/14$ (and $1/10$, $1/12$, $1/13$) | **proved modulo the computation of §3**, all decisions exact; **not yet refereed** |
| Finiteness for $r^2\le r_c^2-1/36$ | **proved modulo the engine certificate** of `../certificates.md` (generator and independent checker; not refereed) |
| finite for $r_\ast<r<r_c$ (Conjecture F₈) | **open**; numerical evidence in §5 |
| Conjecture R₈ | conjecture; it would reduce (B) to further statements (§4), not prove it |

**Gaps and caveats.**
1. *Independent checks.* Part A has been re-implemented and re-checked exactly by the referee. The exact cut-set verification behind Theorem B (`cut/verify.py`) is single-author: the referee did not read or run it, and its own reproduction of the certificates used floating-point comparisons (with margins far above rounding error). The certificates at $\delta\le1/10$ were produced after the referee's pass; the repository engine, a separate exact implementation with its own checker, reproduces them with the same invariants (`../certificates.md` §§4–5).
2. Lemma 2.3 uses exact arithmetic throughout. The only inputs taken from the search are the words, the piece decompositions and the composition sequences. Each is re-checked, never trusted.
3. In `verify.py` the merging of stored pieces into maximal arcs uses exact endpoint equality. Overlapping (not just touching) pieces would not be merged. That can only make (C2) and (C4) harder to satisfy, never easier, so it is safe.
4. Theorem A proves an infinite orbit of one explicit point. It does not prove that the orbit of $0$ is infinite at $r_c$; §2.5 Remark 3 is computational evidence only.
5. The relation to the paper's path (§2.6) is an identification of the limit point and the scale. The paper's figures could not be rendered, so its "angles of $\pi/8$" statement is neither confirmed nor refuted.

**Not checked by the referee:** the author's programs (`verify_closure_n.py`, `exactn.py`, `cut/cut.py`, `cut/verify.py`); the numerical evidence of §5 and of §2.5 Remarks 2–3 (orbit sizes, threshold sweeps, orbit-of-0 observations); the "how the family was found" description; `notes/engine.md` and companion notes; the paper's figures; §7.

---

## 7. Lean formalization: what is done and what is not

**Formalized** (`TDCSG/CriticalRadius/`; statements in `Statements.lean`):
1. **Arithmetic.** $\mathbb Z[\zeta_8]$ as integer vectors with the map to $\mathbb C$ (`CyclotomicModel.lean`, with `TDCSG.Eight.isRoot_zeta` for the actual $e^{2\pi i/8}$), and exact sign decisions in $\mathbb Q(\sqrt2)$ and its quadratic extensions (`QuadraticSigns.lean`).
2. **Generators and words.** The generators as `Equiv.Perm ℂ` (`TDCSG.permA`, `TDCSG.permB`), words acting on segments, and the convexity lemma (`CriticalRadius/Basic.lean`).
3. **Part A in full.** The 31 words of Appendix A with their domains, validity at both endpoints, and the closure data (`TDCSG.Eight.family`, `TDCSG.Eight.pieces`), checked by `decide +kernel` (`realizeOK_family`, `closureOK_family` in `Eight.lean`) and linked to the real generators by proved soundness lemmas; Lemma 2.1 as `TDCSG.Renormalization.renormalize` (`Renormalization.lean`); Theorem A as `TDCSG.CriticalRadius.mem_orbit_pStar_eight_pow`, `infinite_orbit_pStar_eight` and `infinite_GG_eight`, hence `criticalRadius_eight_le`.
**Not formalized:**
1. Theorem 3.1, the certificate theorem: it is a refereed written result with no Lean counterpart, and the library has no certificate predicate. Its main cost is the cell decomposition of a finite arc arrangement.
2. The link between a certificate file and the hypotheses (C1)–(C4): the engine's checker is a tested program, not a kernel-checked proof (see [`../certificates.md`](../certificates.md) §7 for what a verified checker would need). Hence Theorem B is proved modulo the computation, not in Lean.
3. **Part B, full.** Conjecture R₈ and the additional statements (i)–(iii) of §4 first, then an induction on the level $m$; the reduction of `sharp-lower-bound-n8.md` (Conjecture S) is an alternative route.

---

## Appendix A. The renormalization family for $n=8$

Coordinates: $t$ on the line $p^\ast+it$, with $p^\ast=1-2\zeta+\zeta^2-\zeta^3$. Each word acts on its domain as $t\mapsto t+c$ (sign $+$) or $t\mapsto c-t$ (sign $-$). In the exact endpoints, $3/2\sqrt2$ means $\tfrac32\sqrt2$. The domains are the maximal intervals, inside $J$, on which the word is valid with image in $J$.

| # | word | sign | shift c | domain (decimal) | domain endpoints (exact) |
|---|---|---|---|---|---|
| 1 | `bbab` | − | −4 + 4√2 | [-0.437183, 0.679824] | −1 + 3/2√2 − √(19/2 − 5√2) ; −3 + 3/2√2 + √(19/2 − 5√2) |
| 2 | `bABABA` | − | −4 + 4√2 | [-0.437183, 0.828427] | −1 + 3/2√2 − √(19/2 − 5√2) ; −2 + 2√2 |
| 3 | `bbaababa` | + | 4 − 2√2 | [-0.437183, 0.242641] | −1 + 3/2√2 − √(19/2 − 5√2) ; −4 + 3√2 |
| 4 | `bAbaba` | − | 0 | [-0.437183, 0.000000] | −1 + 3/2√2 − √(19/2 − 5√2) ; 0 |
| 5 | `bbaBABababaB` | − | −8 + 6√2 | [-0.343146, 0.094037] | −6 + 4√2 ; −5 + 5/2√2 + √(19/2 − 5√2) |
| 6 | `bbaababaBABB` | − | −8 + 6√2 | [-0.194542, 0.242641] | −5 + 9/2√2 − √(19/2 − 5√2) ; −4 + 3√2 |
| 7 | `bbaBABBABB` | − | −8 + 6√2 | [-0.194542, 0.094037] | −5 + 9/2√2 − √(19/2 − 5√2) ; −5 + 5/2√2 + √(19/2 − 5√2) |
| 8 | `ABABBABABBAB` | − | 4 − 2√2 | [0.000000, 0.585786] | 0 ; 2 − √2 |
| 9 | `bbaabbaBABaB` | − | 0 | [0.000000, 0.242641] | 0 ; −4 + 3√2 |
| 10 | `ABABBABA` | + | −4 + 4√2 | [0.000000, 0.585786] | 0 ; 2 − √2 |
| 11 | `babaBABABBAB` | − | 4 − 2√2 | [0.148604, 0.585786] | 1 + 1/2√2 − √(19/2 − 5√2) ; 2 − √2 |
| 12 | `babb` | − | 2√2 | [0.148604, 1.265610] | 1 + 1/2√2 − √(19/2 − 5√2) ; −1 + 1/2√2 + √(19/2 − 5√2) |
| 13 | `babaBABA` | + | −4 + 4√2 | [0.148604, 0.585786] | 1 + 1/2√2 − √(19/2 − 5√2) ; 2 − √2 |
| 14 | `bbabABABAABB` | − | −8 + 6√2 | [0.242641, 0.679824] | −4 + 3√2 ; −3 + 3/2√2 + √(19/2 − 5√2) |
| 15 | `babaBABabABA` | + | −8 + 6√2 | [0.343146, 0.585786] | 6 − 4√2 ; 2 − √2 |
| 16 | `bbabbabABB` | − | −8 + 6√2 | [0.391244, 0.679824] | −3 + 7/2√2 − √(19/2 − 5√2) ; −3 + 3/2√2 + √(19/2 − 5√2) |
| 17 | `bABBAbABBAba` | − | 4 − 2√2 | [0.585786, 0.828427] | 2 − √2 ; −2 + 2√2 |
| 18 | `babbabABBAba` | − | 4 − 2√2 | [0.585786, 1.171573] | 2 − √2 ; 4 − 2√2 |
| 19 | `bABBAA` | − | 2√2 | [0.585786, 0.828427] | 2 − √2 ; −2 + 2√2 |
| 20 | `abaBAbABBAba` | + | 8 − 6√2 | [0.828427, 1.071068] | −2 + 2√2 ; −6 + 5√2 |
| 21 | `BABB` | − | −4 + 4√2 | [0.977031, 2.094037] | −1 + 5/2√2 − √(19/2 − 5√2) ; −3 + 5/2√2 + √(19/2 − 5√2) |
| 22 | `ABAbaBABBABA` | + | −8 + 6√2 | [1.171573, 1.414214] | 4 − 2√2 ; √2 |
| 23 | `ABAbaBABaB` | − | 4 − 2√2 | [1.171573, 1.414214] | 4 − 2√2 ; √2 |
| 24 | `babABBABABaB` | − | 4 − 2√2 | [1.171573, 1.265610] | 4 − 2√2 ; −1 + 1/2√2 + √(19/2 − 5√2) |
| 25 | `BABBABABaB` | + | 4 − 4√2 | [1.219671, 1.656854] | −5 + 11/2√2 − √(19/2 − 5√2) ; −4 + 4√2 |
| 26 | `BBABBABB` | + | −4 + 2√2 | [1.562817, 1.851396] | 1 + 3/2√2 − √(19/2 − 5√2) ; 1 − 1/2√2 + √(19/2 − 5√2) |
| 27 | `BBAB` | − | 2√2 | [1.562817, 2.679824] | 1 + 3/2√2 − √(19/2 − 5√2) ; −1 + 3/2√2 + √(19/2 − 5√2) |
| 28 | `BABAbaba` | + | 4 − 4√2 | [1.656854, 2.094037] | −4 + 4√2 ; −3 + 5/2√2 + √(19/2 − 5√2) |
| 29 | `ababAb` | − | −4 + 6√2 | [1.805458, 2.242641] | −3 + 9/2√2 − √(19/2 − 5√2) ; −2 + 3√2 |
| 30 | `BBAABABA` | + | −4 + 2√2 | [2.000000, 2.679824] | 2 ; −1 + 3/2√2 + √(19/2 − 5√2) |
| 31 | `BBAbab` | + | −4 + 2√2 | [2.148604, 2.679824] | 3 + 1/2√2 − √(19/2 − 5√2) ; −1 + 3/2√2 + √(19/2 − 5√2) |

**Closure data.** For each family member, $\varepsilon D_f$ is covered by consecutive closed pieces. Each piece starts where the previous one ends, beginning at the left end of $\varepsilon D_f$. Each piece ends at the largest point up to which its composition sequence is valid. Each piece is realized by the listed sequence of family members, given by their row numbers and applied left to right. A semicolon separates consecutive pieces.

| # | pieces of ε·D: composition (indices, applied left to right) |
|---|---|
| 1 | [1, 28, 6, 11] ; [3, 22, 26, 11] ; [1, 21, 8, 20] |
| 2 | [1, 28, 6, 11] ; [3, 22, 26, 11] ; [1, 25, 5, 17] |
| 3 | [1, 28, 6] ; [1, 21, 8, 21] |
| 4 | [1, 28] |
| 5 | [4, 6, 15, 18] ; [8, 21, 15, 18] |
| 6 | [4, 6, 15, 18] ; [8, 21, 15, 18] |
| 7 | [4, 6, 15, 18] ; [8, 21, 15, 18] |
| 8 | [10, 27, 18, 6] |
| 9 | [1, 21, 1, 25] |
| 10 | [1, 21, 6, 11] ; [1, 22, 28, 11] |
| 11 | [10, 27, 18, 6] |
| 12 | [1, 21, 8] |
| 13 | [1, 21, 6, 11] ; [1, 22, 28, 11] |
| 14 | [8, 20, 1, 18] ; [11, 20, 1, 23] |
| 15 | [6, 11, 20] ; [1, 23, 3, 20] |
| 16 | [11, 20, 1, 18] ; [11, 20, 1, 23] |
| 17 | [1, 22, 28] |
| 18 | [1, 21, 14] |
| 19 | [1, 21, 11] |
| 20 | [11, 2, 18, 14] |
| 21 | [1, 21, 15, 18] ; [2, 20, 1, 18] ; [12, 29, 31, 23] |
| 22 | [1, 18, 6, 11] |
| 23 | [1, 21, 14] |
| 24 | [1, 21, 14] |
| 25 | [1, 21, 11, 14] ; [2, 20, 14] |
| 26 | [2, 20, 15, 18] |
| 27 | [12, 27, 18] |
| 28 | [12, 27, 18, 14] |
| 29 | [12, 28, 14, 8] |
| 30 | [12, 21, 5, 17] ; [21, 1, 21, 11] |
| 31 | [12, 28, 8, 20] ; [21, 1, 21, 11] |
