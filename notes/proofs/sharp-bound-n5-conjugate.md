# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$ through the Galois-conjugate coordinate: the escape mechanism and its $1/\delta$ scale

Authors: Eric Vergo, Claude

**Review.** Independently refereed: [`referee-report-sharp-bound-n5-conjugate.md`](referee-report-sharp-bound-n5-conjugate.md). Verdict: Propositions 2, 3, 5 and Theorem 4 correct; Theorem 6 and Corollaries 7, 8 correct after minor fixes (rounded constants, a range remark, a hypothesis), which are applied below; Lemma 1 correct at non-norm radii, with the citation for its "only if" direction corrected (at norm radii that direction is unproved, and nothing depends on it); Corollary 8 is honestly conditional. The computed values of §4 were reproduced; the referee's exact-arithmetic run of the chord words confirms $K$ exactly at every radius of Table 4.1 and at levels 4 and 5.

**What is established and what is not.** Let $r_c=\sqrt{3+\varphi}$ and $\delta=r_c^2-r^2$. **(B), finiteness of $GG_5(r)$ for every $r<r_c$, is not proved here; it remains open.** This note studies (B) through the Galois-conjugate ("internal") coordinate $\sigma(z)$, $\sigma\colon\zeta\mapsto\zeta^2$, in which (B) is the statement that the conjugates of word-map translations stay bounded. What it establishes:

1. **Proved: the escape at $r_c$ in the conjugate coordinate is a linear drift.** Along the critical chord the conjugate coordinate of the $k$-th orbit point of $0$ is exactly $(t_k-2\sqrt5\,k)\,\sigma(E)$, so it escapes along the real line $\mathbb R\sigma(E)$ at a constant rate (Theorem 4).
2. **Proved: below $r_c$ that escape is cut off at the scale $1/\delta$, from both sides.** For $0<\delta\le1/20$ the orbit of $0$ follows the critical chord for $K(\delta)$ steps with $0.0590/\delta-1.18<K(\delta)<2.12/\delta$, and its conjugate coordinate reaches more than $0.502/\delta-11.87$ (Theorem 6). Hence every bound on the conjugates and every invariant region in $\mathbb C\times\mathbb C$ containing $(0,0)$ must grow at least like $1/\delta$ as $r\uparrow r_c$, and none can be chosen independently of $r$ (Corollary 7); modulo the certified tight-window relative certificate, the same holds for visits to a fixed window (Corollary 8).
3. **Proved: three structural facts that shape any proof along this line.** A function on the lifted state space that cannot increase under the generators is an orbit invariant (Proposition 2); no product region $X\times U$ is invariant (Proposition 3); on lattice points, the systems at radius $r$ and at $r_c$ differ only at the 38 critical points and at lattice points whose conjugate modulus exceeds $\delta^{-1/2}-1$ (Proposition 5).
4. **Computed (exact orbits with the repository engine):** the maximal conjugate modulus $M_0(\delta)$ of the orbit of $0$ satisfies $5.37\le\delta M_0(\delta)\le8.10$ on ten radii with $\delta$ from $1/10$ down to $1.3\cdot10^{-3}$; the chord mechanism alone accounts for $84.5\%$ to $99.75\%$ of it; at the level radii the chord exit happens exactly at the Fibonacci index $(F_{3k+7}-1)/2$, the upper bound of Theorem 6 (checked exactly for $k=0,1,2$, in double precision for $k=3,4,5$; §4).
5. **Conjectured:** the conjugate bound $M(r)\le C/\delta$ for all word maps (Conjecture A), which is a quantitative form of (B); and that the chord is the dominant escape route (Conjecture B).

**The remaining gap** (§5). The note controls the conjugate coordinate along the critical chord. It does not control what the orbit does after it leaves the chord, and that is where (B) lives. The line in its direct form (find a compact invariant region, or a function that cannot grow) is a reformulation of (B), not a reduction: Propositions 2, 3 and Corollary 7 show that the region must be fibred over physical space, depend on $r$, and have internal radius at least of order $1/\delta$; describing such a region is equivalent to proving (B). My assessment is in §5.3.

Labels: **proved** (argument written here), **computed** (exact engine run unless stated otherwise, with the command in §6), **conjecture**. Results of other notes are cited with their labels.

---

## 1. Setting and definitions

As in `critical-radius-n5.md` §1 and `sharp-lower-bound-n5.md` §1.

- $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$, $\varphi=(1+\sqrt5)/2$. Then $\varphi=-\zeta^2-\zeta^3$, $\zeta+\zeta^{-1}=\varphi-1$, $\zeta^2+\zeta^{-2}=-\varphi$.
- $D_1,D_2$ are the closed disks of radius $r$ about $-1,+1$; $A(z)=\zeta^{-1}(z+1)-1$, $B(z)=\zeta^{-1}(z-1)+1$; $a=A$ on $D_1$ and $a=\mathrm{id}$ elsewhere, likewise $b$; $GG_5(r)=\langle a,b\rangle$. Words are read left to right.
- $r_c^2=3+\varphi$. Throughout, $\rho=r^2$ and $\delta=r_c^2-\rho$. Since $\delta=(r_c-r)(r_c+r)$, $\delta\le2r_c(r_c-r)$ and $1/\delta\ge0.2326/(r_c-r)$.
- $\sigma$ is the automorphism $\zeta\mapsto\zeta^2$ of $\mathbb Q(\zeta)$. On $\mathbb Q(\varphi)$ it is $\sqrt5\mapsto-\sqrt5$, so $\sigma(\varphi)=1-\varphi=-\varphi^{-1}$; it commutes with complex conjugation. $N(x)=x\,\sigma(x)$ is the norm of $x\in\mathbb Z[\varphi]$; $N(x)\in\mathbb Z\setminus\{0\}$ for $x\ne0$.
- The *critical points* are the 38 lattice points on $\partial D_1(r_c)\cup\partial D_2(r_c)$ (`sharp-lower-bound-combined.md` Lemma 2.1, refereed). For a critical point $Q\in\partial D_p(r_c)$, $|\sigma(Q)-p|^2=\sigma(3+\varphi)=4-\varphi$.
- $E=\zeta-\zeta^2=(0,1,-1,0)$. $|E|^2=3-\varphi$, $\sigma(E)=\zeta^2-\zeta^4=(1,1,2,1)$, $|\sigma E|^2=\sigma(3-\varphi)=2+\varphi$, $|\sigma E|=1.902113$.
- **The critical chord** (`critical-radius-n5.md` §3, refereed, Lean-checked). Breakpoints $B=\{-1,-\varphi^{-1},-\varphi^{-3},1\}$ and intervals $I_1=[-1,-\varphi^{-1}]$, $I_2=[-\varphi^{-1},-\varphi^{-3}]$, $I_3=[-\varphi^{-3},1]$, of lengths $\varphi^{-2},\varphi^{-2},2\varphi^{-1}$. The words $w_1=a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}$, $w_2=abab\,b$, $w_3=aba\,b^{-1}a^{-1}b^{-1}$ act at $r_c$ on $\{sE:s\in I_i\}$ as the translations $s\mapsto s+2\varphi^{-1}$ ($i=1,2$) and $s\mapsto s-2\varphi^{-2}$ ($i=3$), every letter acting as the global rotation. $T\colon[-1,1)\to[-1,1)$ is the resulting rotation by $2\varphi^{-1}$ modulo 2, with $w_1$ on $[-1,-\varphi^{-1}]$, $w_2$ on $(-\varphi^{-1},-\varphi^{-3})$, $w_3$ on $[-\varphi^{-3},1)$. Put $t_0=0$, $t_{k+1}=T(t_k)$, and let $m_k$ be the number of $w_3$-steps among the first $k$. Then
$$t_k=2k\varphi^{-1}-2m_k=-2k-2m_k+2k\varphi\in\mathbb Z[\varphi].\tag{1.1}$$
- **Lifted dynamics.** On $\mathbb C\times\mathbb C$ let $\hat a(z,u)=(Az,\,A^\sigma u)$ if $z\in D_1$ and $(z,u)$ otherwise, where $A^\sigma(u)=\zeta^{-2}(u+1)-1$; likewise $\hat b$ with $B^\sigma(u)=\zeta^{-2}(u-1)+1$, and the inverses with $\zeta^{2}$. The gate is the physical coordinate only. For a word $w$ and a point $z$ with word map $\mu_w(z)=(x\mapsto\zeta^jx+t)$, the lift of $w$ sends $(z,u)$ to $(\zeta^jz+t,\ \zeta^{2j}u+\sigma(t))$, because $\sigma$ is a ring homomorphism. In particular $(z,0)\mapsto(w(z),\sigma(t))$, and for a lattice point $y$, $(y,\sigma y)\mapsto(w(y),\sigma(w(y)))$.
- **Conjugate reach.** $M(r)=\sup\{|\sigma(t)|\}$ over all word maps at all points of $\mathbb C$; $M_0(r)=\max\{|\sigma(y)|:y\in O_r(0)\}$. Since the word map carrying $0$ to $y$ has translation part $y$, $M_0(r)\le M(r)$.
- **Chord time.** $K(\delta)$ is the least $k\ge0$ such that the word $w_{i(t_k)}$ assigned to $t_k$ by $T$ does **not** act at $t_kE$ at radius $r$ as at $r_c$, that is, some letter's disk test fails. Then $t_0E,\dots,t_{K(\delta)}E\in O_r(0)$.

## 2. Statements

**Lemma 1 (conjugate criterion; cited).** $GG_5(r)$ is finite if and only if $M(r)<\infty$ ("if": `critical-radius-n5.md` Lemma 4.1, refereed; "only if": `sharp-lower-bound-n5.md` Theorem 4.1, refereed, at non-norm radii. At a norm radius the "only if" direction is not proved in the repository; by group monotonicity (B) needs only non-norm radii, so nothing below depends on it). At a non-norm radius this is equivalent to a bound on the conjugates of word maps at lattice points (`sharp-lower-bound-n5.md` Theorem 4.1, refereed). If $M(r)<\infty$, the set $W_r=\{(w(z),\sigma(t)):z\in D_1\cup D_2,\ w\text{ a word}\}$ is a bounded subset of $\mathbb C\times\mathbb C$ invariant under $\hat a^{\pm1},\hat b^{\pm1}$ and containing $(D_1\cup D_2)\times\{0\}$; conversely such a bounded invariant set forces $M(r)<\infty$ (`critical-radius-n5.md` §4.1). **[cited; the last sentence's first half is proved in §3.0]**

**Proposition 2 (functions that cannot grow are invariants).** Let $S\subseteq\mathbb C\times\mathbb C$ be invariant under $\hat a^{\pm1},\hat b^{\pm1}$ and $V\colon S\to\mathbb R$ satisfy $V(\hat sX)\le V(X)$ for all $X\in S$ and $s\in\{a^{\pm1},b^{\pm1}\}$. Then $V$ is constant on every lifted orbit in $S$. If moreover $S$ contains $(0,0)$, neither $S$ nor $V$ depends on $r$, and the hypotheses hold at every $r<r_c$, then $V$ is constant on the unbounded set $\{(t_kE,\sigma(t_kE)):k\ge0\}$, so no sublevel set of $V$ containing $(0,0)$ is bounded. **[proved]**

**Proposition 3 (no product region).** Let $r\ge1$, let $X\subseteq\mathbb C$ contain $0$ and $U\subseteq\mathbb C$ be non-empty and bounded. Then $X\times U$ is not mapped into itself by all of $\hat a^{\pm1},\hat b^{\pm1}$. **[proved]**

**Theorem 4 (the escape at $r_c$ in the conjugate coordinate).** At every $r\ge r_c$:
1. $\sigma(t_k)=t_k-2\sqrt5\,k$, so the lifted orbit of $(0,0)$ contains $\bigl(t_kE,\ (t_k-2\sqrt5k)\,\sigma(E)\bigr)$ for every $k\ge0$, and $|\sigma(t_kE)|\ge|\sigma E|(2\sqrt5k-1)$.
2. Each chord step changes the conjugate coordinate by $-2\varphi\,\sigma(E)$ (words $w_1,w_2$) or $-2\varphi^2\sigma(E)$ (word $w_3$): always in the direction $-\sigma(E)$. The lift of $T$ to the strip $\Pi=\{(sE,v\,\sigma E):s\in[-1,1),\ v\in\mathbb R\}$ is the skew product $(s,v)\mapsto(T(s),\,v+c(s))$ with $c=-2\varphi$ on $[-1,-\varphi^{-3})$ and $c=-2\varphi^2$ on $[-\varphi^{-3},1)$. The cocycle $c$ has mean $-2\sqrt5\ne0$ for the Lebesgue measure.
3. The average word length along the chord orbit is $4+\varphi$, so the conjugate modulus grows at the average rate $2\sqrt5\,|\sigma E|/(4+\varphi)=1.51414$ per letter.

**[proved]** (Item 3 uses the unique ergodicity of an irrational rotation.)

**Proposition 5 (the lune in conjugate form).** Let $0<\delta<1/(4-\varphi)$, $p=\pm1$, and let $y\in\Lambda$ lie in $D_p(r_c)\setminus D_p(r)$. Then either $y$ is a critical point, or
$$|\sigma(y)-p|^2>4-\varphi+\frac1\delta .$$
Consequently, at every lattice point $y$ that is not critical and satisfies $|\sigma y|\le\sqrt{4-\varphi+1/\delta}-1$, each generator acts at radius $r$ exactly as at $r_c$. In particular, if the orbit of a lattice point $x$ at $r_c$ is finite, contains no critical point and has $\max|\sigma|=m$, then $O_r(x)=O_{r_c}(x)$ for every $r<r_c$ with $(m+1)^2\le4-\varphi+1/\delta$ and $\delta<1/(4-\varphi)$. **[proved]**

**Theorem 6 (the chord is cut off at the scale $1/\delta$).** Let $0<\delta\le1/20$ and $\kappa=2\varphi^3/\sqrt5=3.78885$.
1. (Lower bound.) Let $K_0$ be the largest integer $k\ge0$ with $2\sqrt5\,k+1+\varphi^3\le1/(\kappa\delta)$. Then $K(\delta)\ge K_0+1$, so $t_0E,\dots,t_{K_0+1}E\in O_r(0)$. Numerically $K(\delta)>0.05901/\delta-1.171$.
2. (Conjugate reach.) $M(r)\ge M_0(r)>0.50202/\delta-11.862$, and $|O_r(0)|>0.05901/\delta-0.171$.
3. (Upper bound.) Let $j$ be the least integer $j\ge4$ with $j\equiv1\pmod3$ and $\sqrt5\,\varphi^{-j}\le\delta$. Then $t_{k_j}=-\varphi^{-1}+(-1)^{j-1}\varphi^{-j}$ for $k_j=(F_j-1)/2$ ($F_j$ the Fibonacci numbers, $F_1=F_2=1$), and $K(\delta)\le k_j<\varphi^3/(2\delta)<2.1181/\delta$. (The bound $K(\delta)\le k_j$ holds for every $\delta>0$ with this $j$; only the size estimate uses $\delta\le1/20$.) The conjugate coordinate along the chord part of the orbit stays below $|\sigma E|\bigl(\sqrt5\varphi^3/\delta+1\bigr)<18.02/\delta+1.91$.
4. At the level radii $\delta_k=\varphi^{-3k}/10$, $k\ge0$, the index in item 3 is $j=3k+7$, so $K(\delta_k)\le(F_{3k+7}-1)/2$ (for $k=0$, where $\delta_0>1/20$, by the remark in item 3).

**[proved]**

**Corollary 7 (no region independent of $r$).** For $0<\delta\le1/20$, every set $W\subseteq\mathbb C\times\mathbb C$ that contains $(0,0)$ and is invariant under the lifted generators at radius $r$ contains a point $(z,u)$ with $|u|>0.50202/\delta-11.862$. No bounded set containing $(0,0)$ is invariant at every $r<r_c$. **[proved]**

**Corollary 8 (window visits must grow).** Let $W^{\rm t}$ be the four tight windows $\pm E+W_0$, $\pm\bar E+W_0$ with $w=(0,2,-1,0)$ of `sharp-lower-bound-limit-system.md` Corollary 4.4, and $T_W<\infty$ the bound on the conjugates of the translation parts of its first-return germs (`sharp-lower-bound-combined.md` Proposition 4.4; finite, not computed). For $0<\delta\le1/20$,
$$|O_r(0)\cap W^{\rm t}|\ \ge\ \frac{0.50202/\delta-11.862}{T_W}-1 .$$
So no bound on window visits uniform in $r<r_c$ exists; any proof of (B) through Corollary 4.4 of that note needs a bound that grows at least like $1/\delta$. **[proved modulo the certified four-window relative certificate cited there]**

**Conjecture A (conjugate bound).** There is $C$ with $M(r)\le C/\delta$ for every $r<r_c$. By Lemma 1 it implies (B); it is (B) with a rate. Evidence: $\delta M_0\in[5.37,8.10]$ on the radii of Table 4.1; the internal extent of the cut-set centres satisfies $\delta\max|\sigma c|\approx19$ (`sharp-lower-bound-n5.md` Table 5.1). Theorem 6 shows the exponent $1$ cannot be lowered. **[conjecture]**

**Conjecture B (the chord dominates).** $M_0(r)\le C'\cdot\max_{k\le K(\delta)}|\sigma(t_kE)|$ for one constant $C'$. On the radii of Table 4.1 the ratio $M_0/\max_{k\le K}|\sigma(t_kE)|$ is at most $1.19$. **[conjecture]**

---

## 3. Proofs

### 3.0 Lemma 1, the invariant set

If $M(r)<\infty$, $W_r$ is bounded: its physical coordinates lie in $D_1\cup D_2$ and its internal ones have modulus at most $M(r)$. It is invariant: applying a generator to $(w(z),\sigma(t))$ gives the lift of the longer word at $z$, by the formula for lifted words in §1. It contains $(z,0)$ for the empty word. $\square$

### 3.1 Proposition 2

Each $\hat s$ is a bijection of $\mathbb C\times\mathbb C$ with inverse $\widehat{s^{-1}}$, and $S$ is invariant under both. For $X\in S$, $V(X)=V(\widehat{s^{-1}}(\hat sX))\le V(\hat sX)\le V(X)$. So $V(\hat sX)=V(X)$ for every generator, and $V$ is constant on lifted orbits. For the second claim: by Theorem 6(1) applied with $\delta\to0$, for every $k$ there is $r<r_c$ at which $(t_kE,\sigma(t_kE))$ lies in the lifted orbit of $(0,0)$; at that $r$, $V(t_kE,\sigma(t_kE))=V(0,0)$. By Theorem 4(1) these points are unbounded. $\square$

### 3.2 Proposition 3

Suppose $X\times U$ is mapped into itself by the four lifted generators. Since $0\in D_1\cap D_2$ for $r\ge1$, the lifts of $a^{\pm1}$ and $b^{\pm1}$ at the points $(0,u)$, $u\in U$, give $(A^\sigma)^{\pm1}(U)\subseteq U$ and $(B^\sigma)^{\pm1}(U)\subseteq U$. Hence $\tau(U)\subseteq U$ for $\tau=(A^\sigma)^{-1}\circ B^\sigma$. Here $\tau(u)=\zeta^2\bigl(\zeta^{-2}(u-1)+1+1\bigr)-1=u+2\zeta^2-2$, a translation by a non-zero vector. Then $U$ contains $u+n(2\zeta^2-2)$ for every $u\in U$ and $n\ge0$, so it is unbounded. $\square$

### 3.3 Theorem 4

1. From (1.1), $\sigma(t_k)=-2k-2m_k+2k(1-\varphi)=-2m_k-2k\varphi$, so $\sigma(t_k)-t_k=2k-4k\varphi=-2\sqrt5\,k$. The points $t_kE$ lie in $O_r(0)$ for $r\ge r_c$ (Theorem A of `critical-radius-n5.md`); their lifts are $(t_kE,\sigma(t_k)\sigma(E))$. Since $|t_k|\le1$, $|\sigma t_k|\ge2\sqrt5k-1$.
2. The translations are $2\varphi^{-1}E$ and $-2\varphi^{-2}E$. With $\sigma(\varphi^{-1})=\sigma(\varphi-1)=-\varphi$ and $\sigma(\varphi^{-2})=\sigma(2-\varphi)=1+\varphi=\varphi^2$ their conjugates are $-2\varphi\,\sigma E$ and $-2\varphi^2\sigma E$. The two pieces have lengths $1-\varphi^{-3}=2\varphi^{-2}$ and $1+\varphi^{-3}=2\varphi^{-1}$ on a circle of length 2, so the mean of $c$ is $\tfrac12\bigl(2\varphi^{-2}(-2\varphi)+2\varphi^{-1}(-2\varphi^2)\bigr)=-2(\varphi^{-1}+\varphi)=-2\sqrt5$.
3. By unique ergodicity of the rotation by $\varphi^{-1}$ (in units of the circle of length 2), $m_k/k\to|I_3|/2=\varphi^{-1}$. The words have lengths 5, 5, 6, so the total length after $k$ steps is $5k+m_k\sim(5+\varphi^{-1})k=(4+\varphi)k$. By item 1 the conjugate modulus after $k$ steps is $|\sigma E|\,(2\sqrt5k+O(1))$. $\square$

### 3.4 Proposition 5

Write $\alpha=|y-p|^2\in\mathbb Z[\varphi]$ and $\beta=r_c^2-\alpha\in\mathbb Z[\varphi]$. Since $y\in D_p(r_c)\setminus D_p(r)$, $0\le\beta<\delta$. If $\beta=0$, $y$ is critical. Otherwise $|N(\beta)|\ge1$, so $|\sigma\beta|>1/\delta$. Also $\sigma(\alpha)=|\sigma(y)-p|^2\ge0$, because $\sigma$ commutes with complex conjugation, and $\sigma(r_c^2)=4-\varphi$; so $\sigma\beta=4-\varphi-\sigma\alpha\le4-\varphi<1/\delta$. Hence $\sigma\beta<-1/\delta$ and $\sigma\alpha=4-\varphi-\sigma\beta>4-\varphi+1/\delta$.

For the consequence: if $y$ is not critical and $|\sigma y|\le\sqrt{4-\varphi+1/\delta}-1$, then $|\sigma y-p|^2\le4-\varphi+1/\delta$, so $y$ is not in $D_p(r_c)\setminus D_p(r)$: $y\in D_p(r)\iff y\in D_p(r_c)$, for both $p$. For the last statement: every point of the finite orbit $O_{r_c}(x)$ has $|\sigma y|\le m$, hence $|\sigma y-p|^2\le(m+1)^2\le4-\varphi+1/\delta$, and is not critical. So the breadth-first search from $x$ makes the same decisions at $r$ and at $r_c$ and produces the same set. $\square$

### 3.5 Theorem 6

**Step 1 (curvature along a chord segment).** Fix $i$ and a test of $w_i$: before its $m$-th letter, with centre $p_m$, the prefix acts on $\{sE:s\in I_i\}$ at $r_c$ as an isometry $h_m(x)=\zeta^{j}x+c$. Put $f_m(s)=|h_m(sE)-p_m|^2$, a real quadratic polynomial with leading coefficient $|\zeta^jE|^2=|E|^2=3-\varphi$. Write $I_i=[b,b']$. At $r_c$ every test passes on all of $I_i$ (`critical-radius-n5.md` Lemma 3.1), so $f_m(b),f_m(b')\le r_c^2$. A quadratic with leading coefficient $3-\varphi$ equals its linear interpolation between $b$ and $b'$ minus $(3-\varphi)(s-b)(b'-s)$. The interpolation is at most $r_c^2$, so
$$f_m(s)\le r_c^2-(3-\varphi)(s-b)(b'-s)\qquad(s\in I_i).\tag{3.1}$$
If $(3-\varphi)(s-b)(b'-s)\ge\delta$, all tests of $w_i$ at $sE$ pass at radius $r$; by induction over the letters, each letter then acts at radius $r$ as at $r_c$, and $w_i(sE)=T(s)E$ at radius $r$.

**Step 2 (a safe set).** Let $d=\min(s-b,b'-s)$. Then $(s-b)(b'-s)=d(|I_i|-d)\ge d|I_i|/2\ge d\varphi^{-2}/2$, since $d\le|I_i|/2$ and $|I_i|\ge\varphi^{-2}$. With $3-\varphi=\sqrt5/\varphi$, the condition of Step 1 holds once $d\ge2\varphi^2\delta/(3-\varphi)=\kappa\delta$. If $\operatorname{dist}(s,B)\ge\kappa\delta>0$, then $s$ lies in the interior of exactly one $I_i$, at distance at least $\kappa\delta$ from its ends, and the word assigned by $T$ is $w_i$.

**Step 3 (Diophantine distance to the breakpoints).** For $b\in B$ write $b=b_0+b_1\varphi$: $\pm1=(\pm1,0)$, $-\varphi^{-1}=1-\varphi=(1,-1)$, $-\varphi^{-3}=3-2\varphi=(3,-2)$. By (1.1), $t_k-b=(-2k-2m_k-b_0)+(2k-b_1)\varphi$. For $b=\pm1$ and $b=3-2\varphi$ the rational part is odd, and for $b=1-\varphi$ the $\varphi$-part is odd; so $t_k\ne b$ for all $k$, and $|t_k-b|\ge1/|\sigma(t_k-b)|$. Now $\sigma(b)\in\{\pm1,\varphi,\varphi^3\}$ (using $\sigma(-\varphi^{-3})=\sigma(3-2\varphi)=1+2\varphi=\varphi^3$), and by Theorem 4(1), $|\sigma t_k|\le2\sqrt5k+1$. Hence
$$\operatorname{dist}(t_k,B)\ \ge\ \frac1{2\sqrt5\,k+1+\varphi^3}.\tag{3.2}$$

**Item 1.** The hypothesis $\delta\le1/20$ gives $1/(\kappa\delta)\ge20/3.789>1+\varphi^3=5.236$, so $K_0\ge0$ exists. For $0\le k\le K_0$, (3.2) gives $\operatorname{dist}(t_k,B)\ge\kappa\delta$, so by Steps 1–2 the word assigned to $t_k$ acts at radius $r$ as at $r_c$. By induction $t_0E,\dots,t_{K_0+1}E\in O_r(0)$ and $K(\delta)\ge K_0+1$. By maximality of $K_0$, $2\sqrt5(K_0+1)>1/(\kappa\delta)-1-\varphi^3$, which gives the numerical form with $1/(2\sqrt5\kappa)=1/(4\varphi^3)=0.0590169\ldots$ and $(1+\varphi^3)/(2\sqrt5)=1.17082$.

**Item 2.** $|\sigma(t_{K_0+1}E)|=|\sigma E|\,|t_{K_0+1}-2\sqrt5(K_0+1)|\ge|\sigma E|\,(2\sqrt5(K_0+1)-1)>|\sigma E|\bigl(1/(\kappa\delta)-2-\varphi^3\bigr)$. The constants are $|\sigma E|/\kappa=\sqrt{2+\varphi}\,\sqrt5/(2\varphi^3)=0.5020285\ldots$ and $|\sigma E|(2+\varphi^3)=11.8617\ldots$. The points $t_0E,\dots,t_{K_0+1}E$ are distinct (Theorem A of `critical-radius-n5.md`), so $|O_r(0)|\ge K_0+2$.

**Item 3.** *The point $t_{k_j}$.* By Binet's formula with $\psi=-\varphi^{-1}$, $F_j\varphi^{-1}-F_{j-1}=\psi^{j-1}(1-\psi\varphi^{-1})/\sqrt5=\psi^{j-1}\varphi^{-1}=(-1)^{j-1}\varphi^{-j}$, using $1+\varphi^{-2}=\sqrt5/\varphi$. For $j\equiv1\pmod3$, $F_j$ is odd and $F_{j-1}$ is even (a Fibonacci number $F_i$ is even exactly when $3\mid i$). With $k_j=(F_j-1)/2$, $t_{k_j}+\varphi^{-1}\equiv(2k_j+1)\varphi^{-1}=F_j\varphi^{-1}\equiv(-1)^{j-1}\varphi^{-j}\pmod 2$. Both sides lie in $[-1+\varphi^{-1},1+\varphi^{-1})$, an interval of length 2, for $j\ge4$; so they are equal.

*Exit at $t_{k_j}$.* Put $b^\ast=-\varphi^{-1}$ and $d=\varphi^{-j}$. Two tests are tight at $b^\ast$, one on each side.
- Left side, $s=b^\ast-d\in I_1$, word $w_1$. The first three letters $a^{-1},a^{-1},b^{-1}$ multiply the linear part by $\zeta^3$ and carry $F'=b^\ast E$ to $-(\zeta-\zeta^{-1})=(-1,-2,-1,-1)$ (table of `critical-radius-n5.md` §3.2). The fourth letter is $a^{-1}$, centre $-1$. So $f(s)=|\zeta^3sE+c+1|^2$ with $f(b^\ast)=|1-(\zeta-\zeta^{-1})|^2=1+(2+\varphi)=r_c^2$, because $\zeta-\zeta^{-1}$ is purely imaginary with $|\zeta-\zeta^{-1}|^2=2+\varphi$. Its derivative at $b^\ast$ is $2\operatorname{Re}(u\bar v)$ with $u=1-\zeta+\zeta^{-1}$, $v=\zeta^3E=\zeta^{-1}-1$: $u\bar v=(1-\zeta+\zeta^{-1})(\zeta-1)=2\zeta-\zeta^2-\zeta^{-1}$, so $2\operatorname{Re}(u\bar v)=(\zeta+\zeta^{-1})-(\zeta^2+\zeta^{-2})=(\varphi-1)+\varphi=\sqrt5$. Hence $f(b^\ast-d)=r_c^2-\sqrt5d+(3-\varphi)d^2>r_c^2-\sqrt5d$.
- Right side, $s=b^\ast+d\in I_2$, word $w_2$. The first letter $a$ multiplies the linear part by $\zeta^{-1}$ and carries $F'$ to $E'=-E$; the second letter is $b$, centre $+1$, and $|E'-1|^2=|E+1|^2=r_c^2$. With $u=E'-1=-(1+\zeta-\zeta^2)$, $v=\zeta^{-1}E=1-\zeta$: $u\bar v=-(1+\zeta-\zeta^2)(1-\zeta^{-1})=-(2\zeta-\zeta^2-\zeta^{-1})$, derivative $-\sqrt5$. Hence $f(b^\ast+d)=r_c^2-\sqrt5d+(3-\varphi)d^2>r_c^2-\sqrt5d$.

If $\sqrt5d\le\delta$, the tight test gives $f>r_c^2-\delta=r^2$ at $t_{k_j}$, whichever side it lies on: that letter does not act (unless an earlier test of the word already failed). Either way $K(\delta)\le k_j$.

*Size of $k_j$.* Since $\delta\le1/20<\sqrt5\varphi^{-4}=0.326$, $j\ge7$, and $j-3\ge4$ lies in the same residue class and is not admissible: $\sqrt5\varphi^{-(j-3)}>\delta$, so $\varphi^j<\sqrt5\varphi^3/\delta$. By Binet, $F_j\le(\varphi^j+\varphi^{-j})/\sqrt5$, so $k_j=(F_j-1)/2\le(\varphi^j+\varphi^{-j}-\sqrt5)/(2\sqrt5)<\varphi^j/(2\sqrt5)<\varphi^3/(2\delta)$. For the conjugate: $|\sigma(t_kE)|\le|\sigma E|(2\sqrt5k+1)$ and $2\sqrt5k_j<\sqrt5\varphi^3/\delta$; the constants are $|\sigma E|\sqrt5\varphi^3=18.017$ and $|\sigma E|=1.902$.

**Item 4.** $\sqrt5\varphi^{-(3k+4)}=0.3262\,\varphi^{-3k}>\delta_k=0.1\,\varphi^{-3k}$ and $\sqrt5\varphi^{-(3k+7)}=0.0770\,\varphi^{-3k}\le\delta_k$. $\square$

### 3.6 Corollaries 7 and 8

*Corollary 7.* The lifted orbit of $(0,0)$ is $\{(y,\sigma y):y\in O_r(0)\}$ (§1) and lies in $W$. Apply Theorem 6(2). A bounded set invariant at every $r<r_c$ would contain these points for all $\delta$, which are unbounded.

*Corollary 8.* Let $y^\ast=t_{K_0+1}E\in O_r(0)$, so $|\sigma y^\ast|>0.50202/\delta-11.862$ (Theorem 6(2)), and take a shortest chain $0=z_0,\dots,z_L=y^\ast$; its points are distinct. Let $z_{i_1},\dots,z_{i_m}$ be its points in $W^{\rm t}$ ($0\notin W^{\rm t}$). Between consecutive cuts, and from $0$ to $z_{i_1}$ and from $z_{i_m}$ to $y^\ast$, the sub-chains have intermediate points outside $W^{\rm t}$, so each cut point is the image of the previous one under a germ $g(x)=\zeta^jx+t$ with $|\sigma t|\le T_W$ (`sharp-lower-bound-combined.md` Proposition 4.4, which holds for every starting point). For lattice points $\sigma(g(x))=\zeta^{2j}\sigma(x)+\sigma(t)$, so the conjugate modulus grows by at most $T_W$ per sub-chain: $|\sigma y^\ast|\le(m+1)T_W$, and $m\le|O_r(0)\cap W^{\rm t}|$. $\square$

---

## 4. Computations

All orbit data are exact breadth-first searches of `tdcsg-orbit orbit` (exact membership, exact points); conjugate moduli are double-precision evaluations of exact points, which is ample here. Commands are in §6.

**Table 4.1.** The orbit of $0$ at $r^2=3+\varphi-\delta$. $M_0$ is its largest conjugate modulus. $K$ is the chord time; "chord reach" is $\max_{k\le K}|\sigma(t_kE)|$.

| $\delta$ | $|O_r(0)|$ | $M_0$ | $\delta M_0$ | $K$ | chord reach | reach$/M_0$ | Theorem 6 bounds on $K$ |
|---|---|---|---|---|---|---|---|
| $1/10$ (level 0) | 1 433 | 53.75 | 5.37 | 6 | 52.1 | 0.970 | — ($\delta>1/20$) |
| $1/20$ | 9 513 | 143.07 | 7.15 | 16 | 136.5 | 0.954 | $[1,\,27]$ |
| $\varepsilon/10$ (level 1) | 30 165 | 273.21 | 6.45 | 27 | 230.9 | 0.845 | $[2,\,27]$ |
| $1/40$ | 30 153 | 273.21 | 6.83 | 27 | 230.9 | 0.845 | $[2,\,27]$ |
| $1/80$ | 112 567 | 612.11 | 7.65 | 72 | 610.6 | 0.998 | $[4,\,116]$ |
| $\varepsilon^2/10$ (level 2) | 400 519 | 1 165.00 | 6.49 | 116 | 987.9 | 0.848 | $[10,\,116]$ |
| $1/160$ | 400 467 | 1 165.00 | 7.28 | 116 | 987.9 | 0.848 | $[9,\,116]$ |
| $1/320$ | 1 504 173 | 2 592.95 | 8.10 | 304 | 2 586.4 | 0.9975 | $[18,\,493]$ |
| $\varepsilon^3/10$ (level 3) | 5 673 561 | 4 933.19 | 6.49 | 493 | 4 194.9 | 0.850 | $[44,\,493]$ |
| $1/640$ | 5 253 049 | 4 933.19 | 7.71 | 493 | 4 194.9 | 0.850 | $[37,\,493]$ |

($\varepsilon=\varphi^{-3}$. Sizes and $M_0$ at the four levels agree with `sharp-lower-bound-n5.md` §7. The last column is $[K_0+1,\,k_j]$ of Theorem 6(1), (3).)

What is exact and what is not in the table:
- $|O_r(0)|$ and $M_0$: exact engine runs.
- $K$: found by a double-precision scratch script that applies $w_1,w_2,w_3$ letter by letter to $t_kE$ with disk tests at radius $r$; the decisions it makes are far from ties. For $\delta=1/10,\ 1/20,\ \varepsilon/10,\ 1/40,\ 1/80,\ \varepsilon^2/10,\ 1/160,\ 1/320$ it was checked against the engine's `point` records: $t_kE\in O_r(0)$ for $k\le K$ and $t_{K+1}E\notin O_r(0)$, with $t_kE$ computed exactly from (1.1) and $\varphi=-\zeta^2-\zeta^3$. This lookup proves $K(\delta)\le K$ exactly (some word must fail before $t_{K+1}E$); it does not by itself prove $K(\delta)\ge K$. The referee's run of the chord words with exact disk tests gives $K$ exactly at all ten radii (§4 of the report).
- Chord reach: $|\sigma E|\,\max_{k\le K}|t_k-2\sqrt5k|$, from $K$.
- The chord exits next to the breakpoint $-\varphi^{-1}$ at levels 0–3 and at $\delta=1/40,\ 1/160,\ 1/640$; at $-\varphi^{-3}$ at $1/20$, $1/320$; at $1$ at $1/80$. All three breakpoints that can bind do bind somewhere, so the lower bound of Theorem 6 cannot be restricted to $b^\ast$.

**Observations (computed).**
1. *Fibonacci exits at the levels.* $K(\delta_k)=6,27,116,493$ for $k=0,1,2,3$ ($k=3$ in double precision only) equals $(F_{3k+7}-1)/2$ ($F_7=13$, $F_{10}=55$, $F_{13}=233$, $F_{16}=987$): the upper bound of Theorem 6(4) is attained. The same script gives $2090=(F_{19}-1)/2$ and $8855=(F_{22}-1)/2$ at levels 4 and 5 (double precision only), with $\delta_kK(\delta_k)\to\varphi^7/(20\sqrt5)=0.649$ and $\delta_k\cdot$chord reach $\to5.52$.
2. *Conjugate growth per generation is the chord rate.* In the orbit of $0$ at $r_c$ (cap $4\cdot10^6$ points, 2 432 generations) the largest conjugate modulus in breadth-first generation $g$, divided by $g$, lies in $[1.507,1.523]$ for every $g$ from $132$ to $2\,432$ and in $[1.513,1.516]$ for $g\ge1\,000$; Theorem 4(3) gives $1.51414$ for the chord. At level 2 the ratio lies in $[1.507,1.527]$ for $100\le g\le640$; the linear growth stops near $g\approx650$, which is $116$ chord steps of average length $4+\varphi$, and the maximum then grows more slowly, from $984$ to $M_0=1\,165$ at $g=892$. So no escape faster than the chord appears in these orbits.
3. *Where the extremes sit.* At levels 1, 2 and 3 the maximum $M_0$ is attained at points $y=P+\lambda$ next to a critical point $P$ (the tight class at levels 1 and 3; the lens corners and the points of another class at level 2) with $|\lambda|\,|\sigma\lambda|=5$, i.e. $N_{\mathbb Q(\zeta)/\mathbb Q}(\lambda)=25$, so $\lambda\in(1-\zeta)^2\Lambda^\times$; $|\lambda|=0.0182,0.00429,0.00101$ shrinks by $\varphi^3$ per level. This is not general: at $\delta=1/320$ the maximum sits at distance $0.449$ from every critical point. Near-maximal conjugates are spread over the whole lens and disks: of the 1 288 points of the level-2 orbit with $|\sigma y|\ge0.97M_0$, 1 036 are at distance more than $0.2$ from every critical point.
4. *Round internal hull.* At level 2 the largest conjugate modulus in each of twenty angular sectors of internal space lies between $1\,163$ and $1\,165$ (as found in `sharp-lower-bound-n5.md` §7 with other code).
5. *Window visits.* The orbit of $0$ meets the four tight windows $W^{\rm t}$ in 84, 1 496, 5 512, 19 408 points at $\delta=1/10,\ \varepsilon/10,\ 1/80,\ \varepsilon^2/10$: about $5\%$ of the orbit, growing like the orbit itself, far faster than the $1/\delta$ that Corollary 8 forces. (Window membership was tested in double precision from the exact points.)

---

## 5. What the line gives, the remaining gap, and an assessment

### 5.1 What happens in the conjugate coordinate, in plain terms

At $r_c$ the conjugate coordinate escapes by a drift: every pass along the critical chord adds a fixed vector, $-2\varphi\sigma E$ or $-2\varphi^2\sigma E$, so the conjugate coordinate runs off along a straight line at $1.514$ per letter (Theorem 4). Below $r_c$ the chord words fail once the chord point comes within $\delta/\sqrt5$ of the breakpoint $-\varphi^{-1}$ (where the words pass through the tight points $\pm E$ and the lens corners), and they keep acting as long as the point stays $\kappa\delta$ away from all four breakpoints. The golden rotation first comes that close after a number of steps proportional to $1/\delta$ (at the levels computed, exactly at a Fibonacci index), so the drift stops at conjugate modulus of order $1/\delta$ (Theorem 6). That is the $1/\delta$ law observed for the internal extent of orbits and cut sets, now with a proof for the chord part: the order is $\Theta(1/\delta)$ for the chord, and at least $1/\delta$ for the orbit.

Proposition 5 says where the two systems differ at all: only at the 38 critical points and at lattice points whose conjugate modulus exceeds $\sqrt{4-\varphi+1/\delta}-1>\delta^{-1/2}-1$. The chord is cut much later, at conjugate of order $1/\delta$, so the relevant lune points are those with conjugate between about $\delta^{-1/2}$ and $C/\delta$, near the tight points.

### 5.2 The remaining gap

(B) is equivalent to $M(r)<\infty$ for every $r<r_c$ (Lemma 1). This note proves $M(r)\ge0.502/\delta-11.9$ and bounds the conjugate along the chord part of one orbit by $18.02/\delta+1.91$. What is missing is an upper bound for everything else:

> **Gap.** Show that for every $r<r_c$ no orbit of $GG_5(r)$ has unbounded conjugate coordinate, i.e. that after the chord exit, and for orbits that never shadow the chord, no other mechanism produces unbounded drift. Conjecture A asks for this with the rate $C/\delta$.

In the language of the earlier notes: the chord exit is the first visit of the orbit to the tight window at the level scale; what happens afterwards is the first-return dynamics at the tight points (`sharp-lower-bound-limit-system.md` §5), whose renormalization is the open problem. Nothing here controls it.

### 5.3 Assessment

- **As a proof strategy for (B), the line in its direct form is equivalent to (B), not a reduction of it.** A bounded invariant region containing $(D_1\cup D_2)\times\{0\}$ exists if and only if the group is finite (Lemma 1; at non-norm radii, which suffice for (B)); a function that cannot grow is an orbit invariant (Proposition 2); the region cannot be a product (Proposition 3), cannot be chosen independently of $r$ (Corollary 7), and must have internal radius at least of order $1/\delta$. Describing it amounts to describing the closure of all lifted orbits, which is the cut-set problem again. I do not see a way to obtain it from the conjugate coordinate alone, so in that form I consider the line **dead**.
- **What survives is quantitative and is useful to the other lines.** The sharp order $1/\delta$ (Theorem 6) is a constraint any proof must meet: in particular a uniform bound on visits to fixed windows is false (Corollary 8, modulo its certificate), so every inductive statement must be at the level scale, as (R-core-t) is. Theorem 6 gives a proved two-sided description of the first approach of the orbit of $0$ to the tight points, for every $\delta\le1/20$ (exact at the Fibonacci indices on the computed levels), which could serve as the base case of an induction on the level.
- **A repairable variant.** Conjecture A, with Proposition 5, suggests an induction on $\delta$ in which the conjugate coordinate is the induction variable: the radius-$r$ system coincides with the $r_c$ system on all non-critical lattice points of conjugate modulus up to $\delta^{-1/2}-1$, and the chord shows that the $r_c$ escape is cut between $0.5/\delta$ and $18/\delta$. Closing this would need the missing renormalization at the tight points, in conjugate terms: a proof that the first-return dynamics at the tight points adds at most $C/\delta$ to the conjugate coordinate. That is not easier than (R-core-t), but it is a single scalar statement and can be tested with the `--conj-points` output.

---

## 6. Reproduction

Engine: `tdcsg-orbit` built from this repository (`lake build tdcsg-orbit`); the per-point conjugate output is `orbit --format lines --conj-points` ([`../engine.md`](../engine.md)). Radii: `closed-1/D` for $\delta=1/D$; the levels are `re:39/10,1`, `re:41/10,4/5`, `re:7/2,9/5`, `re:61/10,-12/5` for $k=0,1,2,3$.

```sh
B=.lake/build/bin/tdcsg-orbit
$B orbit -n 5 --r2 closed-1/320 --cap 30000000 --format lines            # |O|, conj 2 = M_0
$B orbit -n 5 --r2 re:7/2,9/5 --cap 3000000 --format lines --conj-points  # all points, level 2
$B orbit -n 5 --r2 re:61/10,-12/5 --cap 30000000 --format lines --conj-points --conj-min 4900
$B orbit -n 5 --r2 closed --cap 4000000 --format lines --conj-points --conj-min 200   # at r_c
```

- $M_0$ is the `conj 2` record; the extremes and their positions are the `point` records with the largest last field.
- The chord points: $t_k=A_k+B_k\varphi$ with $(A_0,B_0)=(0,0)$ and $(A,B)\mapsto(A-2,B+2)$ if $t<-\varphi^{-3}$, $(A-4,B+2)$ otherwise; $t_kE=A_kE+B_k\varphi E$ with $E=(0,1,-1,0)$ and $\varphi=(0,0,-1,-1)$. Membership in $O_r(0)$ is a lookup of these coefficient vectors in field 4 of the `point` records.
- Per-generation maxima: field 3 of the `point` records is the generation.
- The scripts used for these lookups and for the double-precision chord simulation are throwaway analysis code and are not part of the repository; every exact claim above reduces to the engine output and the formulas of this section.
