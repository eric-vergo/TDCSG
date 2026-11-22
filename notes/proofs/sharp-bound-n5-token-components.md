# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: a fence for the two-family token walk, and the cut-off of every token component at scale $1/\delta$

Authors: Eric Vergo, Claude

**Review.** Independently refereed: [`referee-report-sharp-bound-n5-token-components.md`](referee-report-sharp-bound-n5-token-components.md). Verdict: correct after minor fixes. Lemmas 1–2 and Theorems 3–4 are correct as written, so (T) is proved; Corollary 5(2) was clarified (the range of $D(r)$, and the case $\delta>\tfrac25$), and a notational clash in §1 was removed. Computation 4.1 was re-derived exactly, and Computation 4.3 reproduced with an independent exact program (263 750 components at 19 radii, lattice and non-lattice, no fence crossing), together with exact tests of Lemma 2 on $5\cdot10^6$ points of the fence lines down to $\delta=10^{-6}$. The note continues [`sharp-bound-n5-chaining.md`](sharp-bound-n5-chaining.md) (refereed; cited as "the chaining note") and proves part (T) of its Conjecture B$^\sharp$. From the chaining note it uses: the definitions of its §1 (tokens, the token graph $\mathcal T(r)$, token components, internal diameter, connectors, component graph), the three-distance theorem in the form stated in the proof of its Theorem 1, the statement of Conjecture B$^\sharp$, and Proposition 6 (B$^\sharp\Rightarrow$ (B)), whose two-line proof is re-checked in §3.5. It does not use Theorem 1, Lemma 1.1 or Computation 1.2 of that note: the argument below is independent of them. The exact values at the corner $-F$ (the points $P,P'$, the vector $u$, and the norm formula for $|x|^2$) are those of Lemma 5 of [`sharp-bound-n5-invariant.md`](sharp-bound-n5-invariant.md) (refereed), recomputed here.

**What is established and what is not.** Let $r_c=\sqrt{3+\varphi}$ and $\delta=r_c^2-r^2$.

- **Not established: (B).** Finiteness of $GG_5(r)$ for every $r<r_c$ is **not** proved here. It now reduces to part (K) of Conjecture B$^\sharp$ (bounded chaining of token components by connector letters), which remains open.
- **Proved: Conjecture (T)** (Theorem 4). For $0<\delta\le\tfrac25$, every token component of $\mathcal T(r)$, of any point of the plane, has internal diameter less than $72.07/\delta+41.82\le88.8/\delta$. For $\delta>\tfrac25$ it is less than $222.1$. Along a component, each of the two token indices (the number of steps along $E$, resp. along $\bar E$) takes fewer than $2\varphi^2/\delta+2.45=5.236/\delta+2.45$ values (Theorem 3).
- **Proved: the mechanism, a fence** (Lemma 2). The line through the corner $-F=-\varphi^{-1}E$ in the direction $\bar E$ carries no forward step along $E$ at any radius $r<r_c$, and neither does any parallel line within oblique distance $\kappa_0\delta$ of it, $\kappa_0=(5+\sqrt5)/20=0.3618$, except on its two translates by $\pm2E$, where every crossing step has an endpoint with no other edge (an endpoint on the line $s=-\varphi^2$ or $s=\varphi^2$, up to $\kappa_0\delta$). So the column of the token walk at that position is a wall that no token path crosses. The golden rotation brings every walk to such a column within $2\varphi^2/\delta$ steps. The inputs are exact two-disk identities at the corners $-F$ and $X^\ast=-\varphi^2E+2\bar E$ (Lemma 1), single-disk ranges, and eight disk inequalities with margins at least $0.173$ against a required $0.145$ (Computation 4.1).
- **Computed (exact orbits of the token walk):** over $75\,500$ random token components at 12 radii, from $\delta=\tfrac25$ to $\delta=\varepsilon^3/10=0.00132$, no component crosses a fence column; the largest index range observed is $3.00/\delta$, against the proved bound $5.24/\delta$. The width $\kappa_0\delta$ of the fence is sharp at first order: for $|\eta|$ slightly above $\kappa_0\delta$ the fence leaks, and with $0.45\delta$ in place of $\kappa_0\delta$ about 4 components in 1 000 cross it (Computation 4.3).
- **Consequences, proved:** Conjecture B$^\sharp$ is now equivalent to (K) for small $\delta$, and (K) gives $M(r)\le(K_0+1)(72.07/\delta+41.82)+1.903K_0$, hence Conjecture A and (B) (Corollary 5). At each fixed $r<r_c$, $GG_5(r)$ is finite if and only if the component graphs of its orbits have bounded diameter.
- **Not proved: (K).** §2.4 states it as a bound on the diameter of the lifted component graph, explains why the fence argument does not carry over to connector letters, and records a conjectured finite-type form.

**The remaining gap.** (K): a uniform bound $K_0$ on the number of connector letters needed to realize every word map (equivalently, on the diameter of the component graph of every orbit), for $0<\delta\le\delta_0$. Nothing in this note bounds it.

Labels: **proved** (argument written here, finite computations stated and reproducible), **computed** (exact arithmetic in $\mathbb Z[\zeta]$, or 50-digit arithmetic with stated margins; method in §7), **conjecture**.

---

## 1. Setting

As in the chaining note §1: $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$, $\varphi=(1+\sqrt5)/2$, $\sigma\colon\zeta\mapsto\zeta^2$, $\varepsilon=\varphi^{-3}$, $H(x)=\sigma(x)-x$ on $\mathbb Q(\varphi)$, $E=\zeta-\zeta^2=(0,1,-1,0)$, $\bar E=(-1,-1,-1,-2)$, $F=\varphi^{-1}E=(1,-1,1,-1)$, $b^\ast=-\varphi^{-1}$, $r^2=r_c^2-\delta$, and $|\sigma E|=2\sin72^\circ=1.902113$.

- **Tokens and their domains.** $w_1=AABAB$, $w_2=ababb$, $w_3=abaBAB$ translate by $\tau_iE$ with $\tau_1=\tau_2=2\varphi^{-1}$, $\tau_3=-2\varphi^{-2}$ on their domains $U_i=U_i(r)=\bigcap_jD(c_{ij},r)$, with the test centres $c_{ij}$ of Table 1.1. The twelve tokens are $g\cdot w_i$, $g\in\{\mathrm{id},\nu,\iota,\iota\nu\}$; $g\cdot w_i$ acts at $g(X)$ exactly when $w_i$ acts at $X$, as $g\circ w_i\circ g^{-1}$. So their domains and translations are:
  - *family 1, forward* (class $\mathrm{id}$): $U_i$, translation $\tau_iE$;
  - *family 1, backward* (class $\nu$): $-U_i$, translation $-\tau_iE$;
  - *family 2, forward* (class $\iota$): $\overline{U_i}$, translation $\tau_i\bar E$;
  - *family 2, backward* (class $\iota\nu$): $-\overline{U_i}$, translation $-\tau_i\bar E$.

  Each domain is an intersection of closed disks of radius $r$, with centres independent of $r$, so $U(r)\subseteq U(r_c)$ for $r\le r_c$. A word $w^{-1}$ acts at $w(X)$ exactly when $w$ acts at $X$ (each disk is invariant under its rotation), so the backward family-1 tokens are the reverses of the forward ones ($\nu\cdot w_1=w_2^{-1}$, $\nu\cdot w_2=w_1^{-1}$, $\nu\cdot w_3=w_3^{-1}$ as words), and likewise for family 2. The family-1 edges of $\mathcal T(r)$ are therefore exactly the pairs $\{X,X+\tau_iE\}$ with $X\in U_i$.

**Table 1.1.** Test centres (chaining note §1; `sharp-bound-n5-critical-orbits.md` Table 2.1, refereed). Write $U_i[j]$ for the disk of the $j$-th letter.

| word | $c_{i1},\dots,c_{i6}$ |
|---|---|
| $w_1$ | $(-1,0,0,0)$, $(-1,0,0,0)$, $(-1,0,0,2)$, $(-1,0,-2,2)$, $(-1,2,-2,2)$ |
| $w_2$ | $(-1,0,0,0)$, $(-1,2,0,0)$, $(-1,2,-2,0)$, $(-1,2,-2,2)$, $(-1,2,-2,2)$ |
| $w_3$ | $(-1,0,0,0)$, $(-1,2,0,0)$, $(-1,2,-2,0)$, $(-1,2,-2,2)$, $(-1,2,-4,2)$, $(-1,4,-4,2)$ |

- **Oblique coordinates.** Every $X\in\mathbb C$ is $X=s(X)E+t(X)\bar E$ with real $s,t$, namely $s(X)=\operatorname{Im}(XE)/\operatorname{Im}(E^2)$ and $t(X)=\operatorname{Im}(X\bar E)/\operatorname{Im}(\bar E^2)$. Complex conjugation exchanges $s$ and $t$, and $z\mapsto-z$ negates both. Since $\operatorname{Im}(E^2)=|E|^2\sin36^\circ$ and $|E|\sin36^\circ=\sqrt5/(2\varphi)$, $|s(X)|\le\tfrac{2\varphi}{\sqrt5}|X|=1.447214\,|X|$, so the disk $D(c,R)$ has $s$-range $[s(c)-1.447214R,\ s(c)+1.447214R]$. The line $\mathcal L(p)=\{pE+t\bar E:t\in\mathbb R\}$ is the $\bar E$-line at oblique position $p$. Family-1 tokens change $s$ and keep $t$; family-2 tokens do the opposite. The corner $-F=b^\ast E$ has $s=b^\ast$, $t=0$.
- **The token translation module.** The translations of token paths are the elements of $\Lambda_T=2\mathbb Z[\varphi]E\oplus2\mathbb Z[\varphi]\bar E$, a lattice of rank 4 in $\mathbb C$, since $\{2\varphi^{-1},2\varphi^{-2}\}$ is a $\mathbb Z$-basis of $2\mathbb Z[\varphi]$. Its index in $\Lambda$ is $80$ ($\mathbb Z[\varphi]E\oplus\mathbb Z[\varphi]\bar E$ has index 5, by a $4\times4$ determinant). It is contained in $2(1-\zeta)\Lambda$ (because $E=\zeta(1-\zeta)$ and $\bar E=-\zeta^3(1-\zeta)$), which also has index 80 (`sharp-bound-n5-invariant.md` Proposition 2), so $\Lambda_T=2(1-\zeta)\Lambda$: the token translations generate exactly the translation subgroup of the full-plane group $\langle A,B\rangle$. Physical boundedness constrains no direction of $\Lambda_T$ by itself, since $\Lambda_T$ is dense in $\mathbb C$.
- **Indices.** Let $K$ be a token component and $X_0\in K$. Every $X\in K$ has $s(X)-s(X_0)\in2\mathbb Z[\varphi]$ and $t(X)-t(X_0)\in2\mathbb Z[\varphi]$. For $\xi=2n\varphi^{-1}-2m\in2\mathbb Z[\varphi]$ put $n(\xi)=n=-H(\xi)/(2\sqrt5)$. The **indices** of $X$ are $n_1(X)=n(s(X)-s(X_0))$ and $n_2(X)=n(t(X)-t(X_0))$. A forward family-1 edge raises $n_1$ by 1 and keeps $n_2$ (both $\tau_i$ have $n(\tau_i)=1$); a backward one lowers $n_1$ by 1; family-2 edges act likewise on $n_2$. So the values of $n_1$ on $K$ form an interval of integers, and
$$s(X)\equiv s(X_0)+2n_1(X)\varphi^{-1}\pmod 2 .$$
  The **column** $c$ of $K$ is $\{X\in K:n_1(X)=c\}$. Define $\eta_c\in[-1,1)$ by $s(X_0)+2c\varphi^{-1}-b^\ast\equiv\eta_c\pmod 2$. Every point of column $c$ lies on one of the lines $\mathcal L(b^\ast+\eta_c+2k)$, $k\in\mathbb Z$ (its *lift*). Column $c$ is a **fence column** if $|\eta_c|<\kappa_0\delta$, where
$$\kappa_0=\frac{5+\sqrt5}{20}=\frac1{5-\sqrt5}=0.361803\ldots$$
- **Internal displacement.** For $X,Y\in K$ every token path from $X$ to $Y$ has word map $x\mapsto x+(Y-X)$ with $Y-X\in\Lambda_T$, so the internal diameter of $K$ (chaining note §1) is $\sup_{X,Y\in K}|\sigma(Y-X)|$. If $Y-X=\Delta s\,E+\Delta t\,\bar E$ with $n_1(Y)-n_1(X)=n$, then $\sigma(\Delta s)=\Delta s-2\sqrt5\,n$. So (T) is the statement that both index ranges are $O(1/\delta)$ on every component.
- **The second corner.** $X^\ast=-\varphi^2E+2\bar E=(-3,-3,-1,-3)$, a lattice point with $s(X^\ast)=-\varphi^2=b^\ast-2$.

## 2. Statements

### 2.1 Two exact identities at the corners

**Lemma 1 (two-disk certificates).** Let $X_0,c,c'\in\Lambda$ with $|X_0-c|^2=|X_0-c'|^2=r_c^2$, and put $\ell(Z)=2\operatorname{Re}\bigl(\overline{(X_0-c)}Z\bigr)$, $\ell'(Z)=2\operatorname{Re}\bigl(\overline{(X_0-c')}Z\bigr)$. Suppose $\ell(\bar E)\,\ell'(\bar E)<0$, and put $\lambda=|\ell'(\bar E)|/(|\ell(\bar E)|+|\ell'(\bar E)|)$ and $B=\lambda\ell(E)+(1-\lambda)\ell'(E)$. Then for every $\delta>0$ and every real $\eta$ with $\delta+B\eta>0$, no point of the line $\mathcal L(s(X_0)+\eta)$ lies in $D(c,r)\cap D(c',r)$.

Applied to the corners (exact values in $\mathbb Z[\varphi]$, §3.1):

| | $X_0$ | $c$ (letter) | $\ell(E)$, $\ell(\bar E)$ | $c'$ (letter) | $\ell'(E)$, $\ell'(\bar E)$ | $\lambda$ | $B$ |
|---|---|---|---|---|---|---|---|
| (a) | $-F$ | $(-1,0,0,2)$ ($U_1[3]$) | $5$, $\ 2+\varphi$ | $(-1,0,-2,2)=P$ ($U_1[4]$) | $\sqrt5$, $\ 4-3\varphi$ | $\frac{3-\sqrt5}4$ | $5-\sqrt5$ |
| (b) | $-F$ | $(-1,2,-2,0)$ ($U_2[3]$, $U_3[3]$) | $-5$, $\ -2-\varphi$ | $(-1,2,0,0)=P'$ ($U_2[2]$, $U_3[2]$) | $-\sqrt5$, $\ 3\varphi-4$ | $\frac{3-\sqrt5}4$ | $-(5-\sqrt5)$ |
| (c) | $X^\ast$ | $(-3,-2,-2,-4)$ ($\overline{U_2}[3]$, $\overline{U_3}[3]$) | $-5$, $\ -2-\varphi$ | $(-3,-2,0,-4)$ ($\overline{U_2}[4]$, $\overline{U_3}[4]$) | $-\sqrt5$, $\ 3\varphi-4$ | $\frac{3-\sqrt5}4$ | $-(5-\sqrt5)$ |

Consequently, for every $\delta>0$ and $|\eta|<\kappa_0\delta$: $U_1(r)$, $U_2(r)$ and $U_3(r)$ miss $\mathcal L(b^\ast+\eta)$, and $\overline{U_2}(r)$, $\overline{U_3}(r)$ miss $\mathcal L(-\varphi^2+\eta)$. **[proved]**

Here $2+\varphi=\sqrt5\varphi$, $4-3\varphi=-\sqrt5\varphi^{-2}$ and $3\varphi-4=\sqrt5\varphi^{-2}$.

### 2.2 The fence

**Lemma 2 (fence lemma).** Let $0<\delta\le\tfrac25$ and $|\eta|<\kappa_0\delta$. Put $\mathcal L_k=\mathcal L(b^\ast+\eta+2k)$ for $k\in\mathbb Z$, and $\mathcal M=\mathcal L(\varphi^2+\eta)$.
1. No forward family-1 token acts at any point of $\mathcal L_k$ for $k\notin\{-1,1\}$.
2. On $\mathcal L_{-1}$ (the line $s=-\varphi^2+\eta$) the only forward family-1 token that can act is $w_1$, and at a point of $\mathcal L_{-1}$ where $w_1$ acts, no other of the twelve tokens acts.
3. On $\mathcal L_1$ (the line $s=2-\varphi^{-1}+\eta$) the only forward family-1 token that can act is $w_2$.
4. At a point of $\mathcal M$ where a backward family-1 token acts, no forward family-1 token and no family-2 token acts.

**[proved, using Computation 4.1]**

In words: at oblique position $s\equiv b^\ast$ (mod 2), up to $\kappa_0\delta$, forward steps along $E$ exist only on the lifts $s=b^\ast\pm2$; on the lift $b^\ast-2=-\varphi^2$ the starting point of such a step has no other edge, and on the lift $b^\ast+2$ the step lands on the line $s=\varphi^2$, where its endpoint has no other edge. Geometrically (double-precision pictures, not used in the proofs): near $-F$ at $r_c$, $U_1$ and $U_2$ are two curvilinear sectors with common corner $-F$, which contain the directions $-E$ and $+E$ respectively, and the directions $\pm\bar E$ lie in the complementary pair of sectors. So at $r_c$ the line $\mathcal L(b^\ast)$ meets the forward family-1 domains only at $-F$, and Lemma 1 measures how far the line can be moved below $r_c$ before it meets them.

### 2.3 The cut-off

**Theorem 3 (index cut-off for token components).** Let $0<\delta\le\tfrac25$ and let $j$ be the least integer with $\varphi^{-(j-2)}<\kappa_0\delta$. For every token component $K$ of $\mathcal T(r)$ and every fence column $c$ of $K$, either $n_1\le c+1$ on all of $K$ or $n_1\ge c$ on all of $K$. Consequently $n_1$ takes at most $F_j+2$ values on $K$, and
$$F_j+2<\frac{2\varphi^2}{\delta}+2+\frac1{\sqrt5}=\frac{5.23607}{\delta}+2.44722 .$$
The same holds for $n_2$. **[proved]**

**Theorem 4 (Conjecture (T)).** For $0<\delta\le\tfrac25$ and every token component $K$ of $\mathcal T(r)$, of any point of $\mathbb C$,
$$\sup_{X,Y\in K}|\sigma(Y-X)|<\frac{72.069}{\delta}+41.82\ \le\ \frac{88.8}{\delta}.$$
For $\delta>\tfrac25$ the internal diameter is less than $222.1$. So (T) of the chaining note holds with $\delta_0=\tfrac25$ and $C_T=88.8$. **[proved]**

The leading constant is $72.069=2\times36.034$, twice the single-line constant of the chaining note's Theorem 1: the fence arc $\kappa_0\delta$ is shorter than that theorem's window $2\delta/\sqrt5$ by the factor $2\varphi^{-1}$, and two directions combine with the factor $\varphi$ (§3.4).

### 2.4 What remains: (K)

**Corollary 5 (reduction of B$^\sharp$ to (K)).**
1. For $0<\delta\le\tfrac25$, (K) with constant $K_0$ implies $M(r)\le(K_0+1)(72.07/\delta+41.82)+1.903K_0$, hence Conjecture A of `sharp-bound-n5-conjugate.md` for these radii, hence (B) (by the chaining note's Proposition 6).
2. At each fixed $r<r_c$: a lattice point has a finite orbit if and only if its orbit meets finitely many token components; and $GG_5(r)$ is finite if and only if $D(r)<\infty$, where $D(r)$ is the supremum, over the orbits of all points of $\mathbb C$, of the diameter of the lifted component graph (vertices: token components of lifted states $(y,j)$; edges: connector letters).

**[proved]**

(K) in this form says $D(r)\le K_0$ for $0<\delta\le\delta_0$. On the orbits computed in the chaining note (with its referee's exact values) the diameter is 6 to 9. **[conjecture]**

*Why the fence does not give (K).* The fence uses that token moves are translations in two fixed directions, so that the index $n_1$ is a well-defined coordinate on a component and the golden rotation of $s\bmod2$ is driven by it. A connector letter rotates by $\zeta^{\mp1}$ about $\mp1$. It moves the internal coordinate by only $|\sigma(1-\zeta^{\mp1})|=1.902$, but it changes the lifted rotation index $j$, so the next token component lives in a frame rotated by $\zeta^{\mp2}$ in internal space, and there is no common index in which a fence column could separate the two. The fence columns of different components are unrelated.

*A finite-type form (conjecture).* By Theorem 3 each token component lies in one box $[c_i,c_{i+1}+1]\times[d_k,d_{k+1}+1]$ of the grid of fence columns and fence rows of its seed. The gaps $c_{i+1}-c_i$ are return times of the golden rotation to an arc of length $\kappa_0\delta$, so they take at most three values (three-gap theorem), which are Fibonacci numbers, and in the zoomed coordinate $\eta/\delta$ the return map is exactly the one-line window map of the chaining note's Proposition 2 with $W=(-\kappa_0,\kappa_0)$, invariant under $\delta\mapsto\varepsilon^2\delta$. A renormalization proof of (K) would have to show that the connectors between boxes induce, in these zoomed coordinates, a graph on finitely many box types that is invariant under $\delta\mapsto\varepsilon^2\delta$ up to $O(\delta)$ corrections, with bounded diameter. This is stated as a direction, not tested.

---

## 3. Proofs

### 3.1 Lemma 1

Write $X=X_0+\eta E+\tau\bar E$. Since $|X_0-c|^2=r_c^2$ and $r^2=r_c^2-\delta$,
$$q(\tau):=|X-c|^2-r^2=\delta+\ell(E)\eta+\ell(\bar E)\tau+|\eta E+\tau\bar E|^2,$$
and likewise $q'(\tau)$ with $\ell'$, with the same quadratic part. By the choice of $\lambda\in(0,1)$, $\lambda\ell(\bar E)+(1-\lambda)\ell'(\bar E)=0$, so
$$\lambda q(\tau)+(1-\lambda)q'(\tau)=\delta+B\eta+|\eta E+\tau\bar E|^2\ \ge\ \delta+B\eta>0$$
for every $\tau$. A point of the line in both disks would have $q\le0$ and $q'\le0$, hence a non-positive convex combination. $\square$

*The exact values.* For $v,w\in\Lambda$, $2\operatorname{Re}(\bar vw)=|v+w|^2-|v|^2-|w|^2$, and $|x|^2=(S_0-P_1)+(P_1-P_2-P_3)\varphi$ with $S_0=\sum x_i^2$, $P_d=\sum_ix_ix_{i+d}$ (`sharp-bound-n5-invariant.md` §3.5). This gives, exactly:
- (a) $X_0-c=(0,1,-1,-1)$ and $X_0-c'=(0,1,1,-1)=u$, both of squared modulus $3+\varphi$; $\ell(E)=5$, $\ell(\bar E)=2+\varphi=\sqrt5\varphi$, $\ell'(E)=2\varphi-1=\sqrt5$, $\ell'(\bar E)=4-3\varphi=-\sqrt5\varphi^{-2}$. Hence $\lambda=\varphi^{-2}/(\varphi+\varphi^{-2})=1/(1+\varphi^3)=(3-\sqrt5)/4$ and $B=(5+\sqrt5\varphi^3)/(1+\varphi^3)=(10+2\sqrt5)/(3+\sqrt5)=5-\sqrt5$.
- (b) $\ell(E)=-5$, $\ell(\bar E)=-2-\varphi=-\sqrt5\varphi$ for $c=(-1,2,-2,0)$, and $\ell'(E)=1-2\varphi=-\sqrt5$, $\ell'(\bar E)=3\varphi-4=\sqrt5\varphi^{-2}$ for $c'=P'$. Hence $\lambda=(3-\sqrt5)/4$ and $B=-(5-\sqrt5)$. (This is (a) under $X\mapsto-2F-X$, which exchanges $P$ and $P'$, Lemma 5 of the invariant note.)
- (c) The centres are $\overline{(-1,2,-2,0)}=(-3,-2,-2,-4)$ and $\overline{(-1,2,-2,2)}=(-3,-2,0,-4)$, both at squared distance $3+\varphi$ from $X^\ast=(-3,-3,-1,-3)$, with $\ell(E)=-5$, $\ell(\bar E)=-\sqrt5\varphi$, $\ell'(E)=-\sqrt5$, $\ell'(\bar E)=\sqrt5\varphi^{-2}$: the values of (b). So $B=-(5-\sqrt5)$.

*The consequences.* $1/(5-\sqrt5)=\kappa_0$. By (a), $U_1(r)\subseteq D(c,r)\cap D(c',r)$ misses $\mathcal L(b^\ast+\eta)$ when $\delta+(5-\sqrt5)\eta>0$, i.e. $\eta>-\kappa_0\delta$. By (b), $U_2(r)$ and $U_3(r)$ (whose second and third letters have the centres $P'$ and $(-1,2,-2,0)$) miss it when $\eta<\kappa_0\delta$. By (c), $\overline{U_2}(r)$ and $\overline{U_3}(r)$ miss $\mathcal L(-\varphi^2+\eta)$ when $\eta<\kappa_0\delta$. All four hold for $|\eta|<\kappa_0\delta$, for every $\delta>0$. $\square$

### 3.2 Lemma 2

Let $|\eta|<\kappa_0\delta\le\kappa_0\cdot\tfrac25=0.144721$. We use the $s$-ranges of the domains at $r_c$, which contain those at $r$ (Computation 4.1(1)):
$$s(U_1)\subseteq[-3.55722,-0.57328],\quad s(U_2)\subseteq[-0.66280,2.32115],\quad s(U_3)\subseteq[-0.66280,1.42672].$$

*Item 1.* $k=0$ is Lemma 1. For $k\ge2$ the line $\mathcal L_k$ has $s\ge b^\ast+4-0.1448>3.23>2.32115$; for $k\le-2$ it has $s\le b^\ast-4+0.1448<-4.47<-3.55722$. No $U_i$ reaches these values.

*Item 2.* On $\mathcal L_{-1}$, $s\in(-2.763,-2.473)$, below the $s$-ranges of $U_2$ and $U_3$, so only $w_1$ can act. Let $w_1$ act at $X\in\mathcal L_{-1}$, so $X\in U_1(r)$. We show that $X$ lies in none of the other nine token domains:
- $\overline{U_2}(r)$ and $\overline{U_3}(r)$ miss $\mathcal L_{-1}$ by Lemma 1(c);
- $-U_1$, $-U_2$, $-U_3$, $\overline{U_1}$, $-\overline{U_2}$, $-\overline{U_3}$ each contain one disk of radius $r\le r_c$ whose $s$-range misses $[-\varphi^2-0.1448,\ -\varphi^2+0.1448]$, by margins between $0.297$ and $3.19$ (Computation 4.1(2)). So they miss $\mathcal L_{-1}$;
- $U_1\cap(-\overline{U_1})\subseteq D(c_{13},r)\cap D(-\overline{c_{13}},r)$, and these two disks are disjoint, since their centres are $2\varphi^2>2r_c$ apart (Computation 4.1(2)).

*Item 3.* On $\mathcal L_1$, $s\in(1.237,1.527)$, above the $s$-range of $U_1$. The disk constraint $\tfrac14U_3[1]+\tfrac34U_3[5]$ (a convex combination of the first and fifth disks of $U_3$, which is a disk of radius at most $1.78484$, Computation 4.1(3)) has an $s$-range that misses $[2-\varphi^{-1}-0.1448,\ 2-\varphi^{-1}+0.1448]$ by $0.173$. So $U_3$ misses $\mathcal L_1$, and only $w_2$ can act there.

*Item 4.* $\nu(z)=-z$ maps $\mathcal M=\mathcal L(\varphi^2+\eta)$ onto $\mathcal L(-\varphi^2-\eta)$, which is $\mathcal L_{-1}$ for the parameter $-\eta$ (since $b^\ast-2=-\varphi^2$), and $|-\eta|<\kappa_0\delta$. It maps the forward family-1 domains $U_i$ onto the backward ones $-U_i$ and conversely, and permutes the family-2 domains. If a backward family-1 token acts at $X\in\mathcal M$, then a forward family-1 token acts at $-X\in\mathcal L_{-1}(-\eta)$; by item 2 for $-\eta$ it is $w_1$ and no other token acts at $-X$, so no backward family-1 token and no family-2 token acts at $-X$, i.e. no forward family-1 token and no family-2 token acts at $X$. $\square$

### 3.3 Theorem 3

Fix a fence column $c$ of $K$ and put $\eta=\eta_c$. Let $L_0=\{X\in K:n_1(X)\le c\}$ and $R_0=\{X\in K:n_1(X)\ge c+1\}$. An edge of $K$ joins $L_0$ to $R_0$ only if it is a family-1 edge $\{X,X+\tau_iE\}$ with $X$ in column $c$ and $X\in U_i$ (§1). Every point of column $c$ lies on some $\mathcal L_k$, and by Lemma 2(1) a crossing edge starts on $\mathcal L_{-1}$ or $\mathcal L_1$. Let
- $\mathcal X$ be the set of points of column $c$ on $\mathcal L_{-1}$ at which a forward family-1 token acts. By Lemma 2(2) every edge at such a point is a forward family-1 edge, so all neighbours of a point of $\mathcal X$ lie in column $c+1$; they lie on $\mathcal L(-\varphi^2+\eta+2\varphi^{-1})$ or $\mathcal L(-\varphi^2+\eta-2\varphi^{-2})$, i.e. at $s=-1.382+\eta$ or $s=-3.382+\eta$.
- $\mathcal Y$ be the set of points of column $c+1$ on $\mathcal M$ at which a backward family-1 token acts. By Lemma 2(4) every edge at such a point is a backward family-1 edge, so all neighbours of a point of $\mathcal Y$ lie in column $c$, at $s=\varphi^2+\eta-2\varphi^{-1}=1.382+\eta$ or $s=\varphi^2+\eta+2\varphi^{-2}=3.382+\eta$.

Put $L=(L_0\setminus\mathcal X)\cup\mathcal Y$ and $R=(R_0\setminus\mathcal Y)\cup\mathcal X$. No edge of $K$ joins $L$ to $R$:
- an edge between $L_0\setminus\mathcal X$ and $R_0\setminus\mathcal Y$ would be a crossing edge from $X\in\mathcal L_{\pm1}$ not in $\mathcal X$. If $X\in\mathcal L_{-1}$, a forward family-1 token acts at $X$, so $X\in\mathcal X$; if $X\in\mathcal L_1$, the token is $w_2$ (Lemma 2(3)) and its endpoint $X+2\varphi^{-1}E$ lies on $\mathcal L(b^\ast+2+2\varphi^{-1}+\eta)=\mathcal M$ and carries the backward edge to $X$, so it lies in $\mathcal Y$. Both are excluded;
- the neighbours of a point of $\mathcal X$ are in column $c+1$ at $s\in\{-1.382+\eta,-3.382+\eta\}$, so not on $\mathcal M$, hence not in $\mathcal Y$; they lie in $R_0\setminus\mathcal Y\subseteq R$;
- the neighbours of a point of $\mathcal Y$ are in column $c$ at $s\in\{1.382+\eta,3.382+\eta\}$, so not on $\mathcal L_{-1}$, hence not in $\mathcal X$; they lie in $L_0\setminus\mathcal X\subseteq L$.

$K$ is connected, so $K\subseteq L$ or $K\subseteq R$. On $L$, $n_1\le c+1$; on $R$, $n_1\ge c$.

*Counting.* The $n_1$-values of $K$ form an interval $[a,b]$. In the coordinate $x=(s-b^\ast)/2\in\mathbb R/\mathbb Z$, column $c$ sits at $x_c=x_a+(c-a)\varphi^{-1}$, and it is a fence column when $x_c$ lies in the open arc of length $\kappa_0\delta$ centred at $0$. By the three-distance theorem (V. T. Sós, 1958; as used in the proof of the chaining note's Theorem 1), for $j\ge3$ the points $x+k\varphi^{-1}$, $0\le k<F_j$, cut the circle into arcs of lengths $\varphi^{-(j-1)}$ and $\varphi^{-(j-2)}$, so an open arc longer than $\varphi^{-(j-2)}$ contains one of any $F_j$ consecutive positions. Here $\kappa_0\delta\le0.145<1$, so the least $j$ with $\varphi^{-(j-2)}<\kappa_0\delta$ is at least 7. Suppose $b-a\ge F_j+2$. Among the $F_j$ consecutive columns $a+1,\dots,a+F_j$ there is a fence column $c$. Then $n_1=a\le c-1$ and $n_1=b\ge c+2$ both occur on $K$, which contradicts the dichotomy. So $b-a\le F_j+1$: at most $F_j+2$ values.

*The numerical form.* By minimality, $\varphi^{-(j-3)}\ge\kappa_0\delta$, so $\varphi^j\le\varphi^3/(\kappa_0\delta)$, and by Binet $F_j\le(\varphi^j+\varphi^{-j})/\sqrt5<\varphi^3/(\sqrt5\kappa_0\delta)+1/\sqrt5$. Since $\sqrt5\kappa_0=(\sqrt5+1)/4=\varphi/2$, $\varphi^3/(\sqrt5\kappa_0)=2\varphi^2=5.236068$.

*Family 2.* Complex conjugation maps $\mathcal T(r)$ onto itself (it conjugates $a,b$ to $a^{-1},b^{-1}$ and fixes the disks, `sharp-bound-n5-invariant.md` Proposition 3), exchanges the two families and the coordinates $s,t$, hence $n_1$ and $n_2$. $\square$

### 3.4 Theorem 4

Let $X,Y\in K$ with $Y-X=\Delta s\,E+\Delta t\,\bar E$, $n=n_1(Y)-n_1(X)$, $n'=n_2(Y)-n_2(X)$. By Theorem 3, $|n|,|n'|\le F_j+1$. If $K$ has more than one point, every point of $K$ has an edge, so it lies in one of the twelve token domains. By Computation 4.1(1) all twelve have $|s|\le3.55722$ and $|t|\le3.55722$ (the family-2 domains have $s$-ranges equal to the $t$-ranges of the $U_i$, at most $2.66280$ in modulus). So $|\Delta s|,|\Delta t|\le7.11444$ and
$$|\sigma(\Delta s)|=|\Delta s-2\sqrt5n|\le7.11444+2\sqrt5(F_j+1)<7.11444+6.47214+\frac{23.41641}{\delta}=:\mathcal M_\delta,$$
using $2\sqrt5F_j<4\sqrt5\varphi^2/\delta+2$; the same for $\sigma(\Delta t)$. Now $\sigma(Y-X)=a\,w+b\,\bar w$ with $a=\sigma(\Delta s)$, $b=\sigma(\Delta t)$, $w=\sigma E=2\sin72^\circ\,e^{126^\circ i}$, because $\sigma$ commutes with complex conjugation. Then
$$|aw+b\bar w|^2=(a^2+b^2)|w|^2+2ab\,|w|^2\cos252^\circ\le|w|^2\max(|a|,|b|)^2\,(2+2\cos72^\circ)=\varphi^2|w|^2\max(|a|,|b|)^2,$$
since $2+2\cos72^\circ=2+\varphi^{-1}=\varphi^2$. So $|\sigma(Y-X)|\le\varphi|\sigma E|\,\mathcal M_\delta$ with $\varphi|\sigma E|=\sqrt{5+2\sqrt5}=3.077684$, which gives $72.0682/\delta+41.8152$. For $\delta\le\tfrac25$, $41.82\le16.73/\delta$.

For $\delta>\tfrac25$: the token domains at $r$ are contained in those at $r'$ with $r'^2=r_c^2-\tfrac25$, so every token component at $r$ lies in one at $r'$, whose internal diameter is less than $72.0682\cdot\tfrac52+41.8152<222.1$. $\square$

### 3.5 Corollary 5

*Item 1* is the chaining note's Proposition 6 with $C_T/\delta$ replaced by the bound of Theorem 4 for each of the $K_0+1$ token paths. Its proof, re-checked: under composition of the affine word maps the translation parts add after rotation, so $|\sigma t|$ is subadditive; a token path inside one component contributes at most the internal diameter of that component; a connector $x\mapsto p+\zeta^{\mp1}(x-p)$, $p=\pm1$, contributes $|\sigma(p(1-\zeta^{\mp1}))|=|1-\zeta^{\mp2}|=1.90211$. Finiteness for $0<\delta\le\tfrac25$ then follows from `critical-radius-n5.md` Lemma 4.1, and for smaller $r$ by group monotonicity (`boundary-contact.md` Theorem 3.4), as in the chaining note.

*Item 2.* A token component of a lattice point is a set of lattice points with bounded physical coordinates (it lies in $D_1\cup D_2$) and, by Theorem 4, bounded internal coordinates; so it is finite. An orbit is the union of the token components of its points, so it is finite iff it meets finitely many. If $D(r)<\infty$, every word map at every point is realized by a word with at most $D(r)$ connectors (follow a shortest path in the lifted component graph; the end state determines the word map), so the argument of item 1 with $K_0=D(r)$, and with the bound $222.1$ of Theorem 4 in place of $72.07/\delta+41.82$ when $\delta>\tfrac25$, gives $M(r)<\infty$, and $GG_5(r)$ is finite by Lemma 4.1 of `critical-radius-n5.md`. Conversely, if $GG_5(r)$ is finite, each lifted orbit has at most $5|GG_5(r)|$ states, so each lifted component graph has at most that many vertices and $D(r)\le5|GG_5(r)|$. $\square$

---

## 4. Computations

### 4.1 The finite inputs of Lemma 2 (rigorous)

All centres are exact lattice points. Weights are exact rationals. The quantities below are evaluated in 50-digit arithmetic; every decision has a margin of at least $0.028$ beyond the required $0.144721$, so rounding cannot affect it.

1. *Single-disk $s$-ranges.* For each domain, $s(U)\subseteq[\max_js(c_j)-1.447214\,r_c,\ \min_js(c_j)+1.447214\,r_c]$, with $1.447214\,r_c=3.110017$. This gives the ranges quoted in §3.2 for $U_1,U_2,U_3$, their negatives for $-U_i$, and for the family-2 domains $s(\overline{U_i})=t(U_i)$: $[-0.32115,2.66280]$, $[-2.66280,0.32115]$, $[-0.32115,0.32115]$ for $i=1,2,3$, and negatives for $-\overline{U_i}$. All lie in $[-3.55722,3.55722]$.
2. *The line $s=-\varphi^2+\eta$, $|\eta|\le0.144721$.* A disk $D(c,r)$, $r\le r_c$, misses the band if $|s(c)+\varphi^2|-1.447214\,r_c>0.144721$.

| domain | disk used | $s(c)$ | margin |
|---|---|---|---|
| $-U_1$ | $-U_1[4]$, $c=(1,0,2,-2)$ | $3.68328$ | $3.1913$ |
| $-U_2$ | $-U_2[4]$, $c=(1,-2,2,-2)$ | $0.78885$ | $0.29688$ |
| $-U_3$ | $-U_3[5]$, $c=(1,-2,4,-2)$ | $1.68328$ | $1.1913$ |
| $\overline{U_1}$ | $\overline{U_1}[4]$ | $2.78885$ | $2.2969$ |
| $-\overline{U_2}$ | $-\overline{U_2}[2]$ | $2.78885$ | $2.2969$ |
| $-\overline{U_3}$ | $-\overline{U_3}[2]$ | $2.78885$ | $2.2969$ |

  ($\overline{U_3}$ also misses the band through its fifth disk, margin $2.2969$; Lemma 1(c) covers it anyway.) For $U_1\cap(-\overline{U_1})$: the centres $c_{13}=(-1,0,0,2)$ and $-\overline{c_{13}}=(1,0,-2,0)$ differ by $(-2,0,2,2)$, of squared modulus $4(2+3\varphi)=4\varphi^4$ exactly, so they are $2\varphi^2=5.236>2r_c=4.298$ apart and the two disks are disjoint. (Equivalently, the combination $\tfrac12q+\tfrac12q'$ has squared radius $r^2-(2+3\varphi)\le1-2\varphi<0$.)
3. *The line $s=2-\varphi^{-1}+\eta$.* The combination $\tfrac14q_{31}+\tfrac34q_{35}$ of the first and fifth disk constraints of $U_3$ is the disk constraint with centre $\bar c=\tfrac14(-1,0,0,0)+\tfrac34(-1,2,-4,2)$ and squared radius $r^2-\tfrac3{16}|c_{31}-c_{35}|^2\le r_c^2-\tfrac3{16}(40-20\varphi)=3.18565$, i.e. radius at most $1.78484$; $s(\bar c)=-1.37426$, and the margin is $|{-1.37426}-1.38197|-1.447214\cdot1.78484=0.17318$.

Minimum margin: $0.17318>0.144721$. **[computed, rigorous]**

### 4.2 The geometric fence at the critical width (double precision)

For $\delta\in\{0.3,0.2,0.1,10^{-2},10^{-3},10^{-4},10^{-5}\}$ the four conditions of Lemma 2 were tested on a grid of $\eta$ by intersecting each line with each disk exactly (quadratic in $t$) in double precision. The largest $\kappa$ with all four conditions for $|\eta|\le\kappa\delta$ is $0.369631$, $0.366947$, $0.364339$, $0.362054$, $0.361828$, $0.361806$, $0.361804$, decreasing to $\kappa_0=0.3618034$. The first condition to fail is item 1 at $k=0$ (the line meets $U_2$ for $\eta>0$, $U_1$ for $\eta<0$) together with item 2 (the line meets $\overline{U_2}$ near $X^\ast$) for $\eta>0$ and item 4 for $\eta<0$, all at the same $\kappa$ to six digits at every $\delta$ tested. Random checks at $20\,000$ pairs $(\delta,\eta)$ with $\delta\in(10^{-7},\tfrac25]$, $|\eta|<\kappa_0\delta$ found no failure. **[computed, double precision; not used in the proofs]**

### 4.3 Token components (exact)

Breadth-first search over the twelve tokens from random lattice seeds (a uniform physical point of $D_1\cup D_2$ and a uniform internal point of modulus at most $25/\delta$, rounded to $\Lambda$), exact disk tests in $\mathbb Z[\varphi]$, recording $n_1,n_2$ along the search. For each component: the ranges of $n_1,n_2$, the bounding-box diagonal of $\{\sigma y\}$, and the number of fence columns $c$ with $a+1\le c\le b-2$ (a component "straddles" such a column if this number is positive; Theorem 3 says it is zero).

| $\delta$ | comps | straddles | $\max\delta\cdot(n_1\text{-range})$ | $\max\delta\cdot$extent |
|---|---|---|---|---|
| $2/5$ | 5 000 | 0 | 2.400 | 20.91 |
| $1/10$ | 10 000 | 0 | 2.400 | 25.50 |
| $1/20$ | 10 000 | 0 | 2.250 | 25.82 |
| $1/30$ | 10 000 | 0 | 3.000 | 34.15 |
| $\varepsilon/10$ | 10 000 | 0 | 2.361 | 26.51 |
| $1/55$ | 10 000 | 0 | 1.818 | 24.33 |
| $1/80$ | 6 000 | 0 | 2.363 | 27.59 |
| $\varphi^{-3}/30$ | 6 000 | 0 | 2.974 | 34.28 |
| $\varepsilon^2/10$ | 3 000 | 0 | 2.352 | 27.54 |
| $\varphi^{-3}/55$ | 3 000 | 0 | 1.811 | 24.42 |
| $\varphi^{-6}/30$ | 1 500 | 0 | 2.968 | 33.51 |
| $\varepsilon^3/10$ | 1 000 | 0 | 2.350 | 27.57 |

The maximal extents reproduce Computation 4′ of the chaining note with an independent program ($34.15$ at $1/30$, $34.28$ at $\varphi^{-3}/30$, $33.51$ at $\varphi^{-6}/30$). The $n_1$- and $n_2$-ranges are at most $3.00/\delta$, against the proved $5.24/\delta+1.45$, and the extents at most $34.3/\delta$, against the proved $72.07/\delta+41.82$.

*Sharpness of the fence.* With the fence width $0.45\,\delta$ in place of $\kappa_0\delta$, 3 to 5 components in 1 000 straddle a column (radii $1/10$ to $\varepsilon/10$); with $\delta$, about 85 in 1 000.

*The leaks are used.* Forward family-1 steps from fence columns do occur in large components, on exactly the two lifted lines of Lemma 2: for example a component at $\delta=1/55$ with $9\,137$ states has 7 such steps from points with $s=-2.6213=-\varphi^2-0.18\delta$ (each point carrying only the edge of $w_1$, a dead end), and 7 from points with $s=1.3887$ whose images lie on $s=\varphi^2+0.37\delta$ (dead ends on the other side). As Theorem 3 requires, these fence columns are at the ends of the component's $n_1$-range (here $-63$, its first column, and $26$, its last but one).

*Shape.* In index space a large component is a lacunary, self-similar-looking set (at $\delta=1/55$: $7\,206$ states on $3\,171$ index pairs in a $101\times101$ box; several states share an index pair, differing by lifts $2E$ or $2\bar E$). The longest single-line run of a component spans its whole $n_1$-range in most large components, but not always: the excess of the $n_1$-range over the index range of the longest run reaches about $1.1/\delta$ (at $\varphi^{-3}/30$ and $1/80$), so components are genuinely two-dimensional and Theorem 1 of the chaining note alone does not bound them.

**[computed, exact]**

## 5. What the result says, in plain terms

The tokens move a point along two fixed directions, $E$ and $\bar E$, by translations. So along a token walk the number of net steps in each direction (the index) is a well-defined coordinate, and the internal coordinate grows linearly with it. The question was whether a walk that mixes the two directions can make its indices large by going around the small blocked windows that stop each one-directional run.

It cannot, because of a wall that is orthogonal to the runs. Take the straight line through the corner $-F$ in the direction $\bar E$. Below the critical radius, no forward step along $E$ starts on it, except on two far-away translates where every such step is a dead end. The same holds for all parallel lines within $0.36\,\delta$ of it. A walk that wants to advance its $E$-index must, every $5.2/\delta$ steps or sooner, cross a column of states lying on such a line, and it cannot. The same applies to the $\bar E$-index by mirror symmetry. So every token component is confined to a box of index size $5.2/\delta$ on each side, and its internal diameter is at most about $72/\delta$. The data show about half of that.

What is left for finiteness is to bound how many token components an orbit chains together with single letters. Those letters are rotations, and the wall argument does not apply to them.

## 6. Assessment

- **(T): closed**, with explicit constants (Theorem 4), for every point of the plane, not only lattice points. Its proof needs exact two-disk identities at two corners (Lemma 1), single-disk ranges, and eight disk inequalities with margins at least $0.173$ against $0.145$. It is independent of the one-line Theorem 1 of the chaining note.
- **B$^\sharp$ reduces to (K)** (Corollary 5). (K) is a bound on the diameter of the lifted component graph of every orbit. It is well supported (6 to 9 in the data) and **open**. The fence method does not apply to connectors as it stands.
- **Overall: (B) is repairable, not closed.** The remaining difficulty is entirely in (K).

## 7. Reproduction

All programs are throwaway scratch code, not part of the repository; they are described here so that they can be re-implemented. No engine run is needed: the token walk is not an orbit of $GG_5(r)$ and the engine does not compute it.

- **Exact lattice arithmetic** as in the chaining note §6: points are integer 4-vectors in the basis $1,\zeta,\zeta^2,\zeta^3$; multiplication by $\zeta^{\pm1}$; the disk test is the sign of $\rho-|y\mp1|^2\in\mathbb Z[\varphi]$, decided with 128-bit integers. Complex conjugation is $(a_0,a_1,a_2,a_3)\mapsto(a_0-a_1,-a_1,a_3-a_1,a_2-a_1)$. Radii: $\delta=1/q$ is $\rho=(3q-1+q\varphi)/q$; $\delta=\tfrac25$ is $(13+5\varphi)/5$; the levels and the $\varphi^{-3},\varphi^{-6}$ radii are listed in the chaining note §6.
- **Lemma 1 values** (`fence_rig.py`): $|X_0-c|^2$ by the norm formula, and $\ell(Z)=|v+Z|^2-|v|^2-|Z|^2$ for $v=X_0-c$, $Z\in\{E,\bar E\}$, all exact in $\mathbb Z[\varphi]$; then $\lambda$ and $B$.
- **Computation 4.1** (`fence_rig.py`, `cert_final.py`, mpmath, 50 digits). $s(X)=\operatorname{Im}(XE)/\operatorname{Im}(E^2)$ for the exact centres. Weights for the combined disks were found by mirror ascent on the concave function $\lambda\mapsto\min_t\sum_j\lambda_j(|pE+t\bar E-c_j|^2-r_c^2)$ (S-lemma: an intersection of equal-radius disks misses a line iff some convex combination of the disk constraints does), then rounded to the rationals shown and re-verified; the combined constraint is the disk with centre $\sum\lambda_jc_j$ and squared radius $r^2-\sum\lambda_j|c_j-\bar c|^2$.
- **Computation 4.2** (`fence.py`, `fence2.py`, double precision): each line $\{pE+t\bar E\}$ is intersected with each disk by solving the quadratic in $t$; a domain's trace is the intersection of its disks' intervals; the four conditions are tested on these intervals, and the critical $\kappa$ is found by bisection.
- **Computation 4.3** (`tc.c`). Breadth-first search over the twelve token words, letter by letter with exact disk tests, with hash table on the 4-vector; $n_1$ ($n_2$) is incremented by forward and decremented by backward family-1 (family-2) tokens. Seeds from a xorshift generator (seed 41): physical point uniform in $D_1\cup D_2$, internal point uniform in the disk of radius $25/\delta$, rounded to $\Lambda$ through the inverse Minkowski matrix. For the straddle count, $\eta_c=(s-b^\ast)\bmod2\in[-1,1)$ is read from any state of column $c$, in double precision from the exact point (the straddle count is a check of Theorem 3, not an input to it). Union-find over family-1 edges gives the longest single-line run. Cross-check: the largest extents agree with the chaining note's `tokcomp` at $1/30$, $\varphi^{-3}/30$ and $\varphi^{-6}/30$.
