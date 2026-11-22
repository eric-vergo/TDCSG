# The system $GG_5(r_c)$ at the tight point $E$: the long-segment rotation, offset lines, and a one-sided renormalization by $-\varphi^{-3}$

Authors: Eric Vergo, Claude

**What this note establishes, and what it does not.** Let $r_c=\sqrt{3+\varphi}$ and $\delta=r_c^2-r^2$.

- **Not established: (B).** Finiteness of $GG_5(r)$ for every $r<r_c$ is **not** proved here. Neither is an exact renormalization of the system at $r_c$.
- **Proved** (§3):
  1. **The long segment carries a rotation (Conjecture K4 of `sharp-bound-n5-critical-orbits.md`, now Theorem 1).** At $r_c$ three words of length 4, $u_1=a^{-1}a^{-1}bb$, $u_2=aba^{-1}a^{-1}$, $u_3=bba^{-1}b^{-1}$, act on the segment $[-\varphi^2E,\varphi^2E]$, whose ends are critical points, as the rotation by $2\varphi$ of the circle $\mathbb R/2\varphi^2\mathbb Z$. Its first-return map to the chord $[-E,E]$ is the chord rotation $T$ of Theorem A, and the three critical words of Theorem A are the first-return words: $w_1=u_1u_3$, $w_2=u_2u_1$, $w_3=u_2u_1u_3$, letter for letter. For $t$ outside a countable set the orbit of $tE$ at $r_c$ meets the line $\mathbb RE$ exactly in $(t+2\mathbb Z[\varphi])E\cap[-\varphi^2E,\varphi^2E]$ (Corollary 1.1).
  2. **Theorem 2 on every chord-parallel line (Theorem 2).** For every radius $r\le r_c$ and every offset $s$, the set of parameters at which each of $u_1,u_2,u_3,w_1,w_2,w_3$ applies on the line at offset $s$ is an explicit intersection of intervals, $\bigcap_j[t_j-L_j,t_j+L_j]$ with $L_j=\sqrt{r^2-(s-s_j)^2}/|E|$ and centres $(t_j,s_j)$ in Table 2.1. The holes of $T$ have first-order widths $\max\bigl(\tfrac{2}{\sqrt5}\delta,\ \tfrac85|s|+(\tfrac15+\tfrac1{\sqrt5})\delta\bigr)$ at $-\varphi^{-1}$, and $\max(0,\pm\alpha s+\delta/\sqrt5,\pm\beta s+\delta/5)$ at $-\varphi^{-3}$ and at $1$, with $\alpha=(15+\sqrt5)/10$, $\beta=(\sqrt5-1)/10$ (Corollary 2.1). At $r_c$ the hole at $-\varphi^{-1}$ is $\tfrac85|s|$ **on both sides of the chord** (§3.2 explains a sign discrepancy with the referee report). The hole at $-\varphi^{-1}$ is at least $\max(\tfrac2{\sqrt5}\delta,\tfrac85|s|)$ exactly, so every chord run on the line at offset $s$ has length at most $\min(5.86/\delta,3.28/|s|)$, also at $r_c$ (Corollary 2.2).
  3. **K3 is false, as a theorem (Theorem 3),** and its corrected form: every lattice point $y$ off $\mathbb RE$ has offset $|s(y)|\ge1/(4|\sigma y|)$ (Proposition 4). So an orbit whose internal coordinates stay below $M$ meets no chord-parallel line at offset in $(0,1/(4M))$, and Conjecture A of `sharp-bound-n5-conjugate.md` implies the corrected K3 (Corollary 4.1).
  4. Two local facts at the tight points at $r_c$: lattice points with $|\eta|^2|\sigma\eta|<0.3239$ are not lune points (Lemma 5), and on such points a fixed word acts on a cone, so every fixed word commutes with the positive zooms and is reflected by the negative ones (Lemma 6). The negative unit $-\varepsilon$, $\varepsilon=\varphi^{-3}$, is therefore never a letter-by-letter conjugacy.
- **Computed** (exact arithmetic; §4, with the method of each program):
  1. **The self-similarity unit at $r_c$ is $-\varepsilon$, with period one.** Let $\Psi(z)=E-\varepsilon(z-E)$. On the orbit of $E$ at $r_c$ (cap $4\cdot10^7$ points), $\Psi$ maps all $166\,077$ tested orbit points within distance $1$ of $E$ into the orbit. The units $\varepsilon$, $\pm\varphi^{-1}$, $\pm\varphi^{-2}$ and $-\varepsilon^2$ fail, each with exact non-members (Table 4.1). $\varepsilon^2=(-\varepsilon)^2$ passes, as found earlier.
  2. **The renormalization is one-sided.** $\Psi^{-1}$ does not map the orbit of $E$ near $E$ into itself (exact non-members), and the sets $\Psi^{-k}\bigl(O(\Psi^kx)\cap B(E,0.8\,\varepsilon^k)\bigr)$ *grow* with $k$ before they stabilize (Table 4.3).
  3. **Renormalization inclusion (RI), at $r_c$ and at the levels.** For lattice points $y,y'$ within $0.7$ of $E$: if $y,y'$ lie in one orbit at defect $\delta$, then $\Psi y,\Psi y'$ lie in one orbit at defect $\varepsilon\delta$. No exact failure in 592 + 302 starts at $r_c$ (over $1.7\cdot10^6$ checks) and in 300, 600, 120 starts for the level pairs $0\to1$, $1\to2$, $2\to3$. The defect $\varepsilon\delta$ is sharp: at $\delta=1/10$, the defect $0.025$ (just above $\varepsilon/10=0.02361$) fails on 30 of 300 starts. RI fails, exactly, for pairs at distance $0.775$ from $E$ (§4.3, §4.4).
  4. **The reverse inclusion fails at every defect tested**, including at $r_c$ and above it (§4.5).
  5. **$\Psi$ permutes the large orbits.** $\Psi$ maps the orbits of $0$ and of $E$ near $E$ into themselves, and the orbit of $-\zeta^2$ near $E$ into the orbit of $(-2,-2,-1,-2)$ ($102\,108$ of $102\,108$ points). The $\Gamma$-classes of the chord-free orbits form a 4-cycle under $\Psi$ (§4.6).
- **Conjectured.** Conjecture RI (§2.4). With it, the orbit of $-\zeta^2$ at $r_c$ is infinite, from one computed period: a point $x$ of that orbit with $\Psi^4x$ in the orbit (Proposition 7, conditional). And at the levels, RI gives the monotonicity hypothesis of the period-two note's Proposition 4.5 with period one (Proposition 8, conditional).

**Honest assessment.** Task by task:
- *Task 1 (exact self-similarity at $r_c$):* a precise statement is identified and tested exactly (RI, unit $-\varepsilon$, period one), but it is not proved. It is an inclusion, not a conjugacy, and Lemma 6 shows it cannot hold letter by letter.
- *Task 2:* K4 is **closed** (Theorem 1). Infinitude of $O(-\zeta^2)$ is reduced to RI.
- *Task 3:* **closed** (Theorems 2, 3, Proposition 4).
- *Task 4 (the bridge to $r<r_c$):* the defect transforms as hoped, depth $\eta$ at scale $k$ corresponding to depth $\eta/\varepsilon$ at scale $k-1$. But only in the direction that gives *lower* bounds on orbits. The direction a finiteness proof needs, deep connections contained in coarse ones at a larger defect, fails exactly at every defect tested (§4.5). So the descent argument "a depth-$\delta$ orbit sees only $\log(1/\delta)/\log\varphi^3$ scales" is **dead in that form**. What survives is a monotone form (Proposition 8): (R-core-t) at $E$ becomes the boundedness of the classes of one limit relation. That is a restatement, not a reduction to a finite computation. §6 states the gap.

Status labels: **proved**, **computed** (exact, with the method), **conjectured**. Everything concerns $n=5$.

---

## 1. Setting

Notation as in `sharp-bound-n5-critical-orbits.md` §1:
- $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$, $\varphi=(1+\sqrt5)/2$, $\sigma\colon\zeta\mapsto\zeta^2$;
- $D_1,D_2$ are the closed disks of radius $r$ about $-1,+1$; $a,b$ rotate by $\zeta^{-1}$ about $-1,+1$ on their disks and are the identity elsewhere; words are read left to right, and $A,B$ inside a word stand for $a^{-1},b^{-1}$;
- $r_c^2=3+\varphi$, $\delta=r_c^2-r^2$, the levels are $r_k^2=r_c^2-\varepsilon^k/10$ with $\varepsilon=\varphi^{-3}$;
- $E=\zeta-\zeta^2=(0,1,-1,0)$, $|E|^2=3-\varphi$, $N=iE/|E|$. Every $X\in\mathbb C$ is $X=tE+sN$ with $t,s$ real; $s$ is the offset (D9 of the critical-orbits note);
- $T$ is the chord rotation $t\mapsto t+2\varphi^{-1}\pmod 2$ on $[-1,1)$, realized by $w_1=AABAB$ on $[-1,-\varphi^{-1}]$, $w_2=ababb$ on $[-\varphi^{-1},-\varphi^{-3}]$, $w_3=abaBAB$ on $[-\varphi^{-3},1]$; $X=(1+2\mathbb Z[\varphi])\cup(\varphi^2+2\mathbb Z[\varphi])$;
- a word *applies* at a point if each of its letters, applied in turn, finds the current point in its closed disk. Then the word acts there as the composite of the global rotations;
- $\Psi(z)=E-\varepsilon(z-E)$. Since $-\varepsilon$ is a unit of $\mathbb Z[\varphi]$, $\Psi$ is a bijection of $\Lambda$; it contracts by $\varepsilon$ about $E$ combined with the point reflection, and on internal coordinates it is $\sigma(\Psi z)-\sigma E=\varphi^3(\sigma z-\sigma E)$;
- $y\sim_\delta y'$: $y,y'\in\Lambda$ lie in one orbit of $GG_5(r)$ with $r^2=r_c^2-\delta$ ($\delta<0$ allowed).

---

## 2. Statements

### 2.1 The long segment

**Theorem 1 (rotation of the long segment; K4).** At $r=r_c$:
1. $u_1=AAbb$ applies on $\{tE:-\varphi^2\le t\le-\varphi^{-1}\}$ and acts there as $t\mapsto t+2\varphi$; $u_2=abAA$ applies on $-\varphi^{-1}\le t\le1$ and $u_3=bbAB$ on $1\le t\le\varphi^2$, and both act as $t\mapsto t-2$.
2. Hence $M$, defined as $u_1$ on $[-\varphi^2,-\varphi^{-1})$, $u_2$ on $[-\varphi^{-1},1]$ and $u_3$ on $(1,\varphi^2)$, is the rotation by $2\varphi$ of $\mathbb R/2\varphi^2\mathbb Z$, the ends $\pm\varphi^2$ identified.
3. The first-return map of $M$ to $[-1,1)$ is $T$. The return words are $u_1u_3$ on $[-1,-\varphi^{-1})$, $u_2u_1$ on $[-\varphi^{-1},-\varphi^{-3})$, $u_2u_1u_3$ on $[-\varphi^{-3},1)$. On these segments, letter for letter, they act as $w_1$, $w_2$, $w_3$: $u_1u_3=AAb^4AB$, $u_2u_1=abA^4bb$, $u_2u_1u_3=abA^4b^4AB$, and $b^4=b^{-1}$, $A^4=a$ wherever the four letters act as the global rotation.
4. (Strictness.) The tight tests of $u_1,u_2,u_3$ occur only at the segment ends (Table 4.2). For $t\in[-\varphi^2,\varphi^2)\setminus X$ the $M$-orbit of $t$ is $(t+2\mathbb Z[\varphi])\cap[-\varphi^2,\varphi^2)$, avoids the segment ends, and every step is a strict chain.

[proved]

**Corollary 1.1 (the orbit relation on the chord line).** For every $t\in[-\varphi^2,\varphi^2]\setminus X$,
$$O_{r_c}(tE)\cap\mathbb RE\ \supseteq\ (t+2\mathbb Z[\varphi])E\cap[-\varphi^2E,\varphi^2E],$$
with equality for $t$ outside a countable set, and the same lower bound holds for the strict orbit $O^\circ(tE)$. In particular the points of $O_{r_c}(0)$ on $\mathbb RE$ are dense in $[-\varphi^2E,\varphi^2E]$, and the fraction of them outside $[-E,E]$ tends to $1-\varphi^{-2}=\varphi^{-1}$ along the rotation. [proved]

(The referee of the critical-orbits note counted $2\,806$ of $4\,541$ such points outside $[-E,E]$ at cap $4\cdot10^6$, a fraction $0.618$.)

### 2.2 Chord-parallel lines

**Table 2.1.** Pull-back centres $c_j=t_jE+s_jN$ of the letters (the centre of letter $j$ pulled back by the global rotations of letters $1,\dots,j-1$). Here $\sigma_1=(\sqrt5-1)/4=0.309017$ and $\sigma_2=(1+3\sqrt5)/4=1.927051$. A letter with $|s_j|=\sigma_1$ has $L_j(0)=(5+\sqrt5)/4$ at $r_c$, and one with $|s_j|=\sigma_2$ has $L_j(0)=\varphi/2$.

| word | letters $j$: $(t_j,\ s_j)$ |
|---|---|
| $u_1=AAbb$ | 1, 2: $(-\varphi/2,\ \sigma_1)$; 3, 4: $(-3\varphi/2,\ -\sigma_1)$ |
| $u_2=abAA$ | 1: $(-\varphi/2,\ \sigma_1)$; 2: $(\tfrac{3-\sqrt5}4,\ \sigma_2)$; 3, 4: $(\tfrac{7-\sqrt5}4,\ \sigma_1)$ |
| $u_3=bbAB$ | 1, 2: $(\varphi/2,\ -\sigma_1)$; 3: $(\tfrac{5+\sqrt5}4,\ -\sigma_2)$; 4: $(\tfrac{9+\sqrt5}4,\ -\sigma_1)$ |
| $w_1=AABAB$ | 1, 2: $(-\varphi/2,\ \sigma_1)$; 3: $(-3\varphi/2,\ -\sigma_1)$; 4: $(\tfrac{1-3\sqrt5}4,\ -\sigma_2)$; 5: $(\tfrac{5-3\sqrt5}4,\ -\sigma_1)$ |
| $w_2=ababb$ | 1: $(-\varphi/2,\ \sigma_1)$; 2: $(\tfrac{3-\sqrt5}4,\ \sigma_2)$; 3: $(\tfrac{7-\sqrt5}4,\ \sigma_1)$; 4, 5: $(\tfrac{5-3\sqrt5}4,\ -\sigma_1)$ |
| $w_3=abaBAB$ | 1: $(-\varphi/2,\ \sigma_1)$; 2: $(\tfrac{3-\sqrt5}4,\ \sigma_2)$; 3: $(\tfrac{7-\sqrt5}4,\ \sigma_1)$; 4: $(\tfrac{5-3\sqrt5}4,\ -\sigma_1)$; 5: $(\tfrac{9-3\sqrt5}4,\ -\sigma_2)$; 6: $(\tfrac{13-3\sqrt5}4,\ -\sigma_1)$ |

The $w$-centres are the lattice points of Table 2.1 of the critical-orbits note.

**Theorem 2 (exact domains on every chord-parallel line).** Let $0\le\delta<r_c^2$, $r^2=r_c^2-\delta$, $s\in\mathbb R$, and let $w$ be one of the six words of Table 2.1. The set of $t$ at which $w$ applies at $tE+sN$ at radius $r$ is
$$\bigcap_j\ \bigl[t_j-L_j(s,\delta),\ t_j+L_j(s,\delta)\bigr],\qquad L_j(s,\delta)=\frac{\sqrt{r_c^2-\delta-(s-s_j)^2}}{|E|},$$
which is empty if some radicand is negative. On it $w$ is the translation by $\tau_wE$, with $\tau=2\varphi,-2,-2$ for $u_1,u_2,u_3$ and $2\varphi^{-1},2\varphi^{-1},-2\varphi^{-2}$ for $w_1,w_2,w_3$, so it preserves the line. At $s=\delta=0$ the domains are $[-\varphi^2,-\varphi^{-1}]$, $[-\varphi^{-1},1]$, $[1,\varphi^2]$, $[-\sqrt5,-\varphi^{-1}]$, $[-\varphi^{-1},1]$ and $[-\varphi^{-3},1]$. [proved]

**Corollary 2.1 (the holes of $T$ and of $M$ on the line at offset $s$).** Put $\alpha=(15+\sqrt5)/10=1.723607$, $\beta=(\sqrt5-1)/10=0.123607$, so that $\alpha-\beta=8/5$. On the line at offset $s$, at defect $\delta\ge0$, call the *holes of $T$* the sets of $t$ in the segment of $w_i$ at which $w_i$ does not apply: next to $-\varphi^{-1}$ (from $w_1$ and $w_2$), right of $-\varphi^{-3}$ and left of $1$ (from $w_3$). Their widths are, up to $O\bigl((|s|+\delta)^2\bigr)$:
$$H_{-\varphi^{-1}}=\max\Bigl(\tfrac{2}{\sqrt5}\delta,\ \tfrac85|s|+\bigl(\tfrac15+\tfrac1{\sqrt5}\bigr)\delta\Bigr),\quad H_{-\varphi^{-3}}=\max\bigl(0,\ \alpha s+\tfrac{\delta}{\sqrt5},\ \beta s+\tfrac{\delta}5\bigr),\quad H_1=\max\bigl(0,\ -\alpha s+\tfrac{\delta}{\sqrt5},\ -\beta s+\tfrac{\delta}5\bigr).$$
For $M$ the holes are $\max\bigl(\tfrac25\delta,\ (\tfrac15+\tfrac1{\sqrt5})\delta-\tfrac85s\bigr)$ at $-\varphi^{-1}$, $\max\bigl(\tfrac2{\sqrt5}\delta,\ \tfrac85|s|+(\tfrac15+\tfrac1{\sqrt5})\delta\bigr)$ at $1$, and $\max\bigl(\tfrac25\delta,\ \tfrac85s+(\tfrac15+\tfrac1{\sqrt5})\delta\bigr)$ at $\pm\varphi^2$.

In particular:
- at $s=0$ this is Theorem 2 of the critical-orbits note, $H=2h,h,h$ with $h=\delta/\sqrt5+O(\delta^2)$;
- at $r_c$ the holes of $T$ are $\tfrac85|s|$ at $-\varphi^{-1}$ on both sides of the chord, and $\alpha|s|$ at $-\varphi^{-3}$ for $s>0$ or at $1$ for $s<0$. Their total is $\tfrac{31+\sqrt5}{10}|s|=3.3236|s|$, and that of $M$ is $\tfrac{16}5|s|$. This is the first-order claim of K2, now a theorem;
- for $|s|\le\tfrac{\sqrt5-1}8\delta=0.1545\,\delta$ the hole at $-\varphi^{-1}$ does not depend on $s$ to first order.

[proved; the exact widths are the min/max expressions of Theorem 2, checked against the expansion to 50 digits in §4.7]

**Corollary 2.2 (chord runs on every offset line, at $r_c$ and below).** Let $0\le\delta\le1/10$ and $|s|\le1/10$, not both $0$. On the line at offset $s$, the bad set of the chord rotation (the $t\in[-1,1)$ at which the word assigned by $T$ fails, as in `sharp-bound-n5-invariant.md` §1) contains an open interval of length at least
$$H^\ast(s,\delta)=\max\Bigl(\tfrac2{\sqrt5}\delta,\ \tfrac85|s|+\bigl(\tfrac15+\tfrac1{\sqrt5}\bigr)\delta\Bigr)$$
next to $-\varphi^{-1}$. This is an exact lower bound, not only to first order. Consequently every chord run on that line has length at most $5.24/H^\ast\le\min(5.86/\delta,\ 3.28/|s|)$. In particular, at $r_c$ every chord run off the line $\mathbb RE$ is finite, of length at most $3.28/|s|$. [proved; this is the linear gap asked for in the Remark after Theorem 1 of `sharp-bound-n5-chaining.md` (not refereed), which then gives runs of length $O(1/\max(\delta,|s|))$ there]

**Theorem 3 (K3 is false).** Let $0<\delta\le1/100$, and let $\ell$ be a chord-parallel line at offset $s$ with $0<|s|\le\delta/10$ that contains a lattice point. Then there is a lattice point $x\in\ell$ such that $O_r(x)$ contains more than $0.99/\delta$ points of $\ell$. Such lines exist for every $\delta$ and inside every interval of offsets $(0,c_1\delta)$, $c_1>0$. So no $c_1>0$ makes Conjecture K3 of the critical-orbits note true. [proved]

**Proposition 4 (offset against internal coordinate).** Every $y\in\Lambda\setminus\mathbb RE$ satisfies $|s(y)|\ge1/(4|\sigma y|)$. [proved]

**Corollary 4.1 (corrected K3).** If every point of $O_r(x)$ has $|\sigma|\le M$, then $O_r(x)$ has no point on a chord-parallel line with offset in $(0,1/(4M))$. Consequently Conjecture A of `sharp-bound-n5-conjugate.md`, $M(r)\le C/\delta$, implies the corrected K3: *the orbit of $x$ meets no chord-parallel line at offset in $(0,\delta/(4C'))$*, with $C'=C+\delta|\sigma x|$; equivalently, with $c_1=1/(4\max(C,1))$, no point at offset in $(0,c_1\delta/(1+\delta|\sigma x|))$. The counterexamples of Theorem 3 start at internal radius at least $1/(4|s|)\ge2.5/\delta$, so the internal coordinate of the starting point cannot be dropped from a correct K3. [proved; the statement after "consequently" is conditional on Conjecture A]

The data agree with the inequality: in the orbit of $0$ at level $k$, $s_{\min}=0.385\,\delta_k$ and $M_0\approx6.5/\delta_k$, so $s_{\min}M_0\approx2.5>1/4$.

### 2.3 Tight tests at $r_c$

Let $Q$ be a critical point on $\partial D_p$, $w=Q-p$ (so $|w|^2=3+\varphi$, $|\sigma w|^2=4-\varphi$), and for $\eta\in\Lambda$ put $\ell_Q(\eta)=2\operatorname{Re}(\eta\bar w)\in\mathbb Z[\varphi]$. At $r_c$, $Q+\eta\in D_p$ iff $\ell_Q(\eta)+|\eta|^2\le0$. Call $Q+\eta$ a *lune point* if this test and the open tangent half-plane test $\ell_Q(\eta)<0$ disagree.

**Lemma 5 (no lunes at $r_c$ below a norm bound).** $Q+\eta$ is a lune point iff $-|\eta|^2<\ell_Q(\eta)<0$. If $|\eta|^2|\sigma\eta|<1/(2\sqrt{4-\varphi})=0.32396$, it is not a lune point. The set $\{\eta:|\eta|\le\rho,\ |\eta||\sigma\eta|\le K\}$ with $\rho K<0.32396$ consists of non-lune points and is mapped into itself by $\eta\mapsto u\eta$ for every unit $u=\pm\varepsilon^m$, $m\ge0$. [proved]

**Lemma 6 (fixed words near a tight point).** Let $w$ be a word and $Q$ a critical point. Suppose the prefixes of $w$ carry $Q$ to the points $h_j(Q)$, and let $J$ be the set of tests $j$ with $h_j(Q)$ on the circle of letter $j$. There is $\rho_w>0$ such that for every $\eta\in\Lambda$ with $|\eta|\le\rho_w$ that is not a lune point at any of the critical points $h_j(Q)$, $j\in J$: $w$ applies at $Q+\eta$ iff $\eta$ lies in the open cone $C_w=\{\eta:\ell_j(\zeta^{m_j}\eta)<0,\ j\in J\}$ (and, when $J=\emptyset$, iff $w$ applies at $Q$). Hence for $u=\varepsilon^m$, $m\ge0$ (which keeps $|u\eta|\le\rho_w$ and, since the lune condition $-u|\eta|^2<\ell<0$ only shrinks, keeps $u\eta$ a non-lune point), $w$ applies at $Q+\eta$ iff it applies at $Q+u\eta$; and for $u=-\varepsilon^m$ the cone $C_w$ goes to $-C_w$, which is disjoint from $C_w$ unless $J=\emptyset$. [proved]

So $\Psi$ cannot conjugate the system near $E$ word by word. Any self-similarity under $-\varepsilon$ must match the returns of one word with those of another.

### 2.4 Renormalization at the tight point: the conjecture

**Conjecture RI (renormalization inclusion).** There is $\rho_0\ge0.7$ such that for every $\delta\ge0$ and all $y,y'\in\Lambda$ with $|y-E|,|y'-E|\le\rho_0$:
$$y\sim_\delta y'\ \Longrightarrow\ \Psi y\sim_{\varepsilon\delta}\Psi y'.$$
At $\delta=0$ this says that $\Psi$ maps the orbit relation of $GG_5(r_c)$ on $B(E,\rho_0)$ into itself. At $\delta=\delta_k$ it says that the level-$k$ relation is carried by $\Psi$ into the level-$(k+1)$ relation. The images under $z\mapsto-z$, $\bar z$, $-\bar z$ give the same statement at $-E$, $\bar E$, $-\bar E$. [conjectured; evidence §4.3–4.4: no exact failure for $\rho\le0.76$ at $r_c$ and $\rho=0.7$ at the levels; exact failures at distance $0.775$; the defect $\varepsilon\delta$ cannot be raised]

What RI is not:
- It is not a conjugacy: $\Psi^{-1}$ does not preserve the relation. At every defect tested, including $\delta'\le0$, the relation at defect $\varepsilon\delta$ on $\Psi B$ is not contained in the $\Psi$-image of the relation at defect $\delta'$ on $B$ (§4.5).
- The unit is $-\varepsilon$, period one. At the levels this is consistent with the period two of `sharp-bound-n5-period-two.md`: there the zoom was $+\varepsilon$ and the object was equality of first-return sets, and both fail with period one. At $\eta=0$ that note observed $R_{k+1}=-R_k$, which is the unit $-\varepsilon$. On a single line, the first return of the golden rotation to a window at $-\varphi^{-1}$ satisfies $R_{\varepsilon\delta}=R_\delta^{-1}$ exactly (`sharp-bound-n5-chaining.md` Proposition 2, not refereed): period one for the return relation, with a reversal. That is the one-dimensional shadow of the same sign.

### 2.5 Consequences of RI

**Proposition 7 (infinitude from one period; conditional).** Assume RI at $\delta=0$. If $x\in\Lambda$, $0<|x-E|\le\rho_0$, and $\Psi^mx\in O_{r_c}(x)$ for some $m\ge1$, then $O_{r_c}(x)$ is infinite. For the orbit of $-\zeta^2$ such a point exists with $m=4$ (computed, §4.6): $x=(-14,-20,3,-30)\in O_{r_c}(-\zeta^2)$, $|x-E|=0.545$, and $\Psi^4x=(-4558,-6764,1363,-9582)\in O_{r_c}(-\zeta^2)$. So RI implies that $O_{r_c}(-\zeta^2)$ is infinite, and likewise the orbit of $(-2,-2,-1,-2)$. [proved, given RI and the computed memberships]

($m=4$ is forced: $\Psi$ acts on the 20 $\Gamma$-classes, and the class of $-\zeta^2$ has period 4, §4.6.)

**Proposition 8 (monotone renormalization at the levels; conditional).** Assume RI at $\delta=\delta_k$ for all $k\ge k_0$. For $x\in\Lambda$ with $|x-E|\le\rho_0$ put
$$S_j(x)=\Psi^{-j}\bigl(O_{r_{k_0+j}}(\Psi^jx)\cap B(E,\rho_0\varepsilon^j)\bigr).$$
1. $S_0(x)\subseteq S_1(x)\subseteq S_2(x)\subseteq\cdots$, and every $S_j(x)$ is finite when $GG_5(r_{k_0+j})$ is.
2. The following are equivalent: (i) $\sup_{k\ge k_0}\sup_{x'}|O_{r_k}(x')\cap B(E,\rho_0\varepsilon^{k-k_0})|<\infty$ (that is (R-core-t) at $E$, with core radius $\rho_0\varepsilon^{k-k_0}$); (ii) the limit sets $S_\infty(x)=\bigcup_jS_j(x)$ are bounded in size uniformly in $x$.

[proved, given RI]

So under RI, (R-core-t) at $E$ is the boundedness of the classes of one monotone limit relation. Proposition 4.5 of the period-two note needed this monotonicity (M$_5$) with period two, and it was not supported there for first-return sets with the zoom $+\varepsilon^2$. With orbit relations and the zoom $-\varepsilon$ it holds on every computed case.

---

## 3. Proofs

### 3.1 Theorem 1 and Corollary 1.1

*Item 1.* All six segment ends are lattice points $tE$, $t\in\{-\varphi^2,-\varphi^{-1},1,\varphi^2\}\subset\mathbb Z[\varphi]$. Each letter of each $u_i$ was applied to both ends of its segment with exact arithmetic in $\Lambda$, testing $|z\mp1|^2\le3+\varphi$ as the sign of an element of $\mathbb Z[\varphi]$ (Table 4.2). Every test passes, with slack $0$ or $-2+4\varphi=2\sqrt5$. A disk is convex, the current images of a segment under the global rotations are segments, and the test of letter $j$ at an interior point is the test at a convex combination of the two ends. So each letter applies on the whole closed segment, and the word acts as the composite of the global rotations. In each $u_i$ the rotation exponents of the letters ($-1$ for $a,b$, $+1$ for $A,B$) sum to $0$, so the composite is a translation. Exactly: $u_1(z)=z+(2,0,0,-2)$ with $(2,0,0,-2)=2\varphi E$, and $u_2(z)=u_3(z)=z+(0,-2,2,0)=z-2E$.

*Item 2.* $u_1$ maps $[-\varphi^2,-\varphi^{-1})$ onto $[\varphi^{-1},\varphi^2)$, since $-\varphi^2+2\varphi=\varphi-1=\varphi^{-1}$ and $-\varphi^{-1}+2\varphi=\varphi^2$. $u_2,u_3$ map $[-\varphi^{-1},\varphi^2)$ onto $[-\varphi^2,\varphi^{-1})$. These are the two pieces of the rotation $t\mapsto t+2\varphi\pmod{2\varphi^2}$ on $[-\varphi^2,\varphi^2)$, since $\varphi^2-2\varphi=-\varphi^{-1}$ and $2\varphi-2\varphi^2=-2$. At $t=1$ both $u_2$ and $u_3$ give $-1$.

*Item 3.* By cases, using $2\varphi-2=2\varphi^{-1}$, $2-2\varphi^{-1}=2\varphi^{-2}$ and $\sqrt5=2\varphi-1$:
- $t\in[-1,-\varphi^{-1})$: $M(t)=t+2\varphi\in[\sqrt5,\varphi^2)$, outside $[-1,1)$ and in the domain of $u_3$; $M^2(t)=t+2\varphi-2=t+2\varphi^{-1}\in[\varphi^{-3},\varphi^{-1})\subset[-1,1)$.
- $t\in[-\varphi^{-1},-\varphi^{-3})$: $M(t)=t-2\in[-\varphi^2,-\sqrt5)$, in the domain of $u_1$; $M^2(t)=t+2\varphi^{-1}\in[\varphi^{-1},1)$.
- $t\in[-\varphi^{-3},1)$: $M(t)=t-2\in[-\sqrt5,-1)$; $M^2(t)=t+2\varphi^{-1}\in[1,\sqrt5)$, outside $[-1,1)$ and in the domain of $u_3$; $M^3(t)=t+2\varphi^{-1}-2=t-2\varphi^{-2}\in[-1,\varphi^{-3})$.

In each case the first return is $T(t)$. The concatenated words are $u_1u_3=AAbb\,bbAB$, $u_2u_1=abAA\,AAbb$ and $u_2u_1u_3$. Where four consecutive letters $b$ (or $A$) all act as the global rotation $B$ (or $A^{-1}$), they act as $B^4=B^{-1}$ (or $A^{-4}=A$), and a rotation about $\pm1$ preserves the distance to $\pm1$. So the single test of $B^{-1}$ is equivalent to the four tests of $b^4$. Hence the words act as $w_1=AABAB$, $w_2=ababb$, $w_3=abaBAB$, with equivalent tests.

*Item 4.* By Table 4.2 the tight tests sit at the segment ends only. By strict convexity (`sharp-bound-n5-critical-orbits.md` §3.1) every interior point of every intermediate segment lies in the open disk. The breakpoints $-\varphi^{-1}=1-\varphi$, $1$ and $\pm\varphi^2=\pm(1+\varphi)$ all lie in $X$, since $1-\varphi\equiv1+\varphi\pmod 2$. $M$ moves $t$ by $2\varphi$ or $-2$, elements of $2\mathbb Z[\varphi]$. So for $t\notin X$ the $M$-orbit stays in $t+2\mathbb Z[\varphi]$, which is disjoint from $X$, and it avoids the breakpoints. $\{2\varphi,2\varphi^2\}$ is a $\mathbb Z$-basis of $2\mathbb Z[\varphi]$, so the orbit of the rotation is $(t+2\mathbb Z[\varphi])\cap[-\varphi^2,\varphi^2)$. Reverse chains of strict chains are strict. $\square$

*Corollary 1.1.* "$\supseteq$" is item 4. For "$\subseteq$": every $g\in GG_5(r_c)$ acts at a point as an element $z\mapsto\zeta^jz+c$ of $\Gamma=\langle A,B\rangle$, and the translations in $\Gamma$ form $L=2(1-\zeta)\Lambda$ (`sharp-bound-n5-invariant.md` Proposition 2). If $j=0$ and $tE+c\in\mathbb RE$, then $c\in L\cap\mathbb RE$. Lattice points of $\mathbb RE$ are $\mathbb Z[\varphi]E$, and $cE$ with $c\in\mathbb Z[\varphi]$, $E=\zeta(1-\zeta)$, lies in $2(1-\zeta)\Lambda$ iff $c\in2\Lambda\cap\mathbb Z[\varphi]=2\mathbb Z[\varphi]$. If $j\ne0$, then $\operatorname{Im}\bigl((\zeta^jtE+c)\bar E\bigr)=0$ forces $t=-\operatorname{Im}(c\bar E)/(|E|^2\sin(2\pi j/5))$, a countable set of values as $c$ ranges over $\Lambda$. Points $tE$ with $|t|>\varphi^2$ lie outside $D_1\cup D_2$: $|\varphi^2E-1|^2=3+\varphi$ (critical) and $\frac{d}{dt}|tE-1|^2=2(t|E|^2-\operatorname{Re}E)>0$ for $t>0.81$, and symmetrically. A point outside both disks is fixed by both generators, and each generator maps its disk onto itself, so such a point is in no orbit of a point inside. The density statement follows from the density of $2\mathbb Z[\varphi]$, and the fraction from unique ergodicity of the rotation. $\square$

### 3.2 Theorem 2 and Corollary 2.1

*Theorem 2.* If the first $j-1$ letters apply at $X$, the current point is $h_j(X)$, where $h_j$ is the composite global rotation, and letter $j$ applies iff $|h_j(X)-p_j|\le r$, iff $|X-c_j|\le r$ with $c_j=h_j^{-1}(p_j)$, because $h_j$ is an isometry. Write $c_j=t_jE+s_jN$. Since $E\perp N$ and $|N|=1$, $|tE+sN-c_j|^2=|E|^2(t-t_j)^2+(s-s_j)^2$. Induction over $j$ gives the intersection. The centres were computed exactly in $\Lambda$ and converted with $t_j=\operatorname{Re}(c_j\bar E)/|E|^2$, $s_j=\operatorname{Im}(c_j\bar E)/|E|$. Both lie in $\mathbb Q(\sqrt5)$ up to the factor $|E|$: $s_j^2=-\kappa(c_j)^2/(4|E|^2)$ with the key $\kappa$ of D9, and $\sigma_1^2=(3-\sqrt5)/8$, $\sigma_2^2=(23+3\sqrt5)/8$. The translations are those of Theorem 1 and of `critical-radius-n5.md` Lemma 3.1, and they are parallel to $E$. $\square$

*Corollary 2.1.* Near a tight end $b$ at $s=\delta=0$, the end $t_j\pm L_j$ of a tight letter equals $b$. With $\partial_sL_j=(s_j-s)/(|E|^2L_j)$ and $\partial_\delta L_j=-1/(2|E|^2L_j)$, its first-order displacement is $\pm\bigl(s_js/(|E|^2L_j(0))-\delta/(2|E|^2L_j(0))\bigr)$. With $|E|^2=(5-\sqrt5)/2$:
- for $|s_j|=\sigma_1$, $L_j(0)=(5+\sqrt5)/4$, this gives slope $\pm\beta$ and $\delta$-coefficient $1/5$;
- for $|s_j|=\sigma_2$, $L_j(0)=\varphi/2$, slope $\pm\alpha$ and coefficient $1/\sqrt5$.

The identities are exact: $\sigma_2/L_j(0)=(7-\sqrt5)/2$ and $(7-\sqrt5)/(5-\sqrt5)=(15+\sqrt5)/10$; $\sigma_1/L_j(0)=(3-\sqrt5)/(2\sqrt5)$, which divided by $|E|^2$ is $(\sqrt5-1)/10$; and $1/(2|E|^2\cdot\varphi/2)=1/\sqrt5$, $1/(2|E|^2(5+\sqrt5)/4)=1/5$.

The tight letters at each end, with their signs, are as follows (Table 2.1, and Table 2.1 of the critical-orbits note):
- at $-\varphi^{-1}$: $w_1$ letters 3 ($-\sigma_1$) and 4 ($-\sigma_2$) bound the right end of $w_1$, and $w_2$ letters 2 ($+\sigma_2$) and 3 ($+\sigma_1$) bound the left end of $w_2$;
- at $1$: $w_3$ letters 1 ($+\sigma_1$) and 2 ($+\sigma_2$);
- at $-\varphi^{-3}$: $w_3$ letters 5 ($-\sigma_2$) and 6 ($-\sigma_1$).

The right end of $w_1$ is the minimum of its letters' ends and the left end of $w_2$ the maximum. Taking the differences gives the stated maxima. For example, the right end of $w_1$ is $-\varphi^{-1}+\min(-\beta s-\delta/5,\ -\alpha s-\delta/\sqrt5)$ and the left end of $w_2$ is $-\varphi^{-1}+\max(-\alpha s+\delta/\sqrt5,\ -\beta s+\delta/5)$. The difference is $\max\bigl(2\delta/\sqrt5,\ (\alpha-\beta)|s|+(1/5+1/\sqrt5)\delta\bigr)$ after the four combinations are compared. For $M$ the tight letters are $u_1$: 3, 4 ($-\sigma_1$) at $-\varphi^{-1}$ and 1, 2 ($+\sigma_1$) at $-\varphi^2$; $u_2$: 2 ($+\sigma_2$), 3, 4 ($+\sigma_1$) at $-\varphi^{-1}$ and 1 ($+\sigma_1$), 2 ($+\sigma_2$) at $1$; $u_3$: 3 ($-\sigma_2$), 4 ($-\sigma_1$) at $1$ and 1, 2 ($-\sigma_1$), 3 ($-\sigma_2$) at $\varphi^2$. Non-tight letters keep slack at least $0.6525$ at $s=\delta=0$ and do not bind near the ends for small $(s,\delta)$. The remainder is $O((|s|+\delta)^2)$ because each $L_j$ is smooth near $(0,0)$ with $L_j(0)>0$. $\square$

*Corollary 2.2.* Each $L_j(s,\delta)=\sqrt{r_c^2-\delta-(s-s_j)^2}/|E|$ is concave in $(s,\delta)$ where it is defined: it is the square root, a concave non-decreasing function, of a concave function. So $L_j$ lies below its tangent plane at $(0,0)$. For the right end of $w_1$ this gives $\min_j(t_j+L_j)\le t_4+L_4\le-\varphi^{-1}-\alpha s-\delta/\sqrt5$, and with letter 3, $\le-\varphi^{-1}-\beta s-\delta/5$. For the left end of $w_2$ it gives $\max_k(t_k-L_k)\ge-\varphi^{-1}-\alpha s+\delta/\sqrt5$ (letter 2) and $\ge-\varphi^{-1}-\beta s+\delta/5$ (letter 3). So every $t$ strictly between the two ends lies in the bad set: in $I_1$ the word $w_1$ fails, in $I_2$ the word $w_2$ fails. The gap between the ends is at least the largest of the four differences of these bounds, which is $H^\ast$. The interval stays inside $I_1\cup I_2$, since its ends are within $\alpha|s|+\delta/\sqrt5<0.22<\varphi^{-2}$ of $-\varphi^{-1}$. The run bound is the argument of `sharp-bound-n5-invariant.md` Theorem 7(1), with its arc $\delta/\sqrt5$ replaced by $H^\ast/2$. By Lemma 6 there, $L\le F_m-1$ for the least $m\ge2$ with $1/F_m+\varphi^{-m}<H^\ast/2$, and the same Binet estimate gives $F_m-1\le\varphi\cdot1.6188\cdot2/H^\ast<5.24/H^\ast$. $\square$

*Remark (sign of the hole at $-\varphi^{-1}$).* The referee report on the critical-orbits note (its §4) describes, for $s<0$, an overlap of $w_1$ and $w_2$ by $1.6|s|$ at $-\varphi^{-1}$. With the convention of D9 ($s=\operatorname{Im}(X\bar E)/|E|$, the convention of Table 2.1), Theorem 2 gives a hole of $\tfrac85|s|$ for both signs. A direct check confirms it, applying $w_1,w_2$ letter by letter as complex maps at 40 digits: at $s=\pm0.01$, $w_1$ ends at $-0.6360$ and $-0.6170$, and $w_2$ starts at $-0.6190$ and $-0.6000$. A one-sided overlap of $\tfrac85|s|$ does occur at $-\varphi^{-1}$ for the factor words $u_1,u_2$ of $M$ (Corollary 2.1), which may be the source of the discrepancy.

### 3.3 Theorem 3, Proposition 4, Corollary 4.1

*Theorem 3.* Fix $\delta\le1/100$ and $0<|s|\le\delta/10$. *First order.* By Corollary 2.1 the hole at $-\varphi^{-1}$ is $2\delta/\sqrt5$ (since $|s|\le0.1545\delta$); for $s\ge0$, $H_{-\varphi^{-3}}=\alpha s+\delta/\sqrt5\le(\alpha/10+1/\sqrt5)\delta$ and $H_1\le\delta/\sqrt5$, and symmetrically for $s<0$. The first-order total is at most $(4/\sqrt5+\alpha/10)\delta=1.961\,\delta$. *Remainder.* Each hole width is $[L_k(0,0)-L_k(s,\delta)]+[L_j(0,0)-L_j(s,\delta)]$ for the binding letters $j,k$ (minimum and maximum over two letters each). Write $L_j=\sqrt{Q_j-x_j}/|E|$ with $Q_j=r_c^2-s_j^2\ge r_c^2-\sigma_2^2=0.9045$ and $x_j=\delta+s^2-2ss_j$, so $|x_j|\le1.39\,\delta\le Q_j/2$. Taylor's theorem for $x\mapsto\sqrt Q-\sqrt{Q-x}$, whose second derivative is at most $1/(\sqrt2\,Q^{3/2})$ on $|x|\le Q/2$, bounds the deviation from the linear term by $x_j^2/(2\sqrt2\,Q_j^{3/2}|E|)\le0.68\,\delta^2$ per letter end. Taking minima and maxima changes this by at most a factor 2 per hole, so $H_{\rm tot}\le1.961\,\delta+4.1\,\delta^2\le2.002\,\delta$. (On a grid of $\delta\in[10^{-4},10^{-2}]$, $|s|\le\delta/10$, the exact total is at most $1.795\,\delta$, §4.7.)

The non-tight letters still pass for $|s|\le0.1$ and $\delta<0.24$: if $|X_0-c|^2\le r_c^2-0.6525$ then $|X_0+sN-c|^2\le(\sqrt{r_c^2-0.6525}+0.1)^2<4.37<r_c^2-\delta$. So on the line the chord words realize $T$ in the $t$-coordinate outside the holes.

Let $N=\lfloor0.99/\delta\rfloor$. The set $G_N$ of $t\in[-1,1)$ whose first $N$ iterates under $T$ avoid the holes has measure at least $2-N\cdot2.002\,\delta>0$ ($T$ preserves Lebesgue measure), and it is a finite union of intervals, because the holes are intervals and $T$ is a piecewise translation. If $y_0\in\ell\cap\Lambda$, then $y_0+\mathbb Z[\varphi]E\subset\ell\cap\Lambda$ has dense $t$-coordinates $t_0+\mathbb Z[\varphi]$, so some lattice point $x\in\ell$ has $t(x)\in G_N$. Its chain realizes $T^0,\dots,T^N$ on $\ell$, with distinct points because $T$ is an irrational rotation. That is $N+1>0.99/\delta$ points.

Existence of the lines: $s(y)=\operatorname{Im}(y\bar E)/|E|$ is additive. On the basis it takes the values $\operatorname{Im}(\zeta^k\bar E)/|E|$, which generate a $\mathbb Z[\varphi]$-module of rank 1 in $\mathbb R$, of the form $\mathbb Z[\varphi]\cdot\sigma_0$, since all $\operatorname{Im}(\zeta^k\bar E)/|E|$ are $\mathbb Q(\sqrt5)$-multiples of one number. $\mathbb Z[\varphi]$ is dense in $\mathbb R$, so the offsets of lattice lines are dense. $\square$

*Proposition 4.* Put $\kappa=y\bar E-\bar yE=2i\,s|E|$. It lies in $\Lambda$, is non-zero for $y\notin\mathbb RE$, and lies in the ideal $(1-\zeta)$: $E=\zeta(1-\zeta)$ and $\bar E=-\zeta^{-2}(1-\zeta)$. So its absolute norm $|\kappa|^2|\sigma\kappa|^2$ is a positive integer divisible by $N(1-\zeta)=5$. Further $\sigma\kappa=\sigma y\,\overline{\sigma E}-\overline{\sigma y}\,\sigma E$, so $|\sigma\kappa|\le2|\sigma y||\sigma E|$. With $|E||\sigma E|=\sqrt{(3-\varphi)(2+\varphi)}=\sqrt5$:
$$5\le|\kappa|^2|\sigma\kappa|^2\le4s^2|E|^2\cdot4|\sigma y|^2|\sigma E|^2=80\,s^2|\sigma y|^2 .$$
Hence $|s|\,|\sigma y|\ge1/4$. $\square$

The bound is attained up to a factor by the Fibonacci keys of `sharp-bound-n5-critical-orbits.md` §4.3, which have norm exactly 5.

*Corollary 4.1.* Apply Proposition 4 to each orbit point. Under Conjecture A every orbit point has $|\sigma y|\le|\sigma x|+M(r)\le|\sigma x|+C/\delta=C'/\delta$, since $y=\zeta^jx+t$ with $|\sigma t|\le M(r)$ for the word map carrying $x$ to $y$. The last sentence of the corollary is Proposition 4 applied to the starting points of Theorem 3. $\square$

### 3.4 Lemmas 5, 6

*Lemma 5.* $|Q+\eta-p|^2-r_c^2=|w+\eta|^2-|w|^2=\ell_Q(\eta)+|\eta|^2$, and $\ell_Q(\eta)=\eta\bar w+\bar\eta w\in\Lambda\cap\mathbb R=\mathbb Z[\varphi]$. The disk test says $\ell\le-|\eta|^2$, the half-plane test $\ell<0$, and they disagree exactly when $-|\eta|^2<\ell<0$ (at $\ell=0$ both fail for $\eta\ne0$). A non-zero $\ell\in\mathbb Z[\varphi]$ has $|\ell||\sigma\ell|\ge1$, and $|\sigma\ell|=|2\operatorname{Re}(\sigma\eta\,\overline{\sigma w})|\le2|\sigma w||\sigma\eta|$. So a lune point has $|\eta|^2>|\ell|\ge1/(2|\sigma w||\sigma\eta|)$. For a unit $u=\pm\varepsilon^m$, $|u\eta|=\varepsilon^m|\eta|$ and $|\sigma(u\eta)|=\varphi^{3m}|\sigma\eta|$, so $|u\eta||\sigma(u\eta)|=|\eta||\sigma\eta|$ and $|u\eta|\le|\eta|$. $\square$

*Lemma 6.* For $j\notin J$, the point $h_j(Q)$ has $|h_j(Q)-p_j|\ne r_c$, so for $|\eta|$ below half the gap the test at $h_j(Q+\eta)=h_j(Q)+\zeta^{m_j}\eta$ has the outcome it has at $\eta=0$. Let $\rho_w$ be the least such radius over $j$; it is positive because there are finitely many $j$. For $j\in J$, $h_j(Q)$ is a critical point and Lemma 5 applies to $\zeta^{m_j}\eta$, which has the same $|\cdot|$ and $|\sigma\cdot|$ as $\eta$. Induction over the letters gives the cone, and $\ell_j(u\eta)=u\,\ell_j(\eta)$ for real $u$. $\square$

### 3.5 Propositions 7, 8

*Proposition 7.* Put $y=x$ and $y'=\Psi^mx$. Both lie within $\rho_0$ of $E$, since $\Psi$ contracts towards $E$, and they lie in one orbit. Applying RI $m$ times gives $\Psi^mx\sim_0\Psi^{2m}x$, and inductively $\Psi^{jm}x\sim_0x$ for every $j$. These points are distinct, since $\Psi^{jm}x-E=(-\varepsilon)^{jm}(x-E)\ne0$ has distinct moduli. For $-\zeta^2$, the memberships of $x$ and $\Psi^4x$ were found by an exact breadth-first search from $-\zeta^2$ (§4.6). The orbit of $(-2,-2,-1,-2)$ contains $\Psi x$ for $x$ in the orbit of $-\zeta^2$ near $E$ (§4.6, all $102\,108$ tested points), so it is infinite as well under RI. $\square$

*Proposition 8.* (1) If $z\in S_j(x)$, then $\Psi^jz\in O_{r_{k_0+j}}(\Psi^jx)$ with both points within $\rho_0\varepsilon^j$ of $E$. Apply RI at $\delta=\delta_{k_0+j}$ to the pair $(\Psi^jz,\Psi^jx)$, which lies within $\rho_0$ of $E$; then $\Psi^{j+1}z\sim_{\delta_{k_0+j+1}}\Psi^{j+1}x$ with $|\Psi^{j+1}z-E|\le\rho_0\varepsilon^{j+1}$, so $z\in S_{j+1}(x)$. (2) Every lattice point $x'$ within $\rho_0\varepsilon^{k-k_0}$ of $E$ is $\Psi^{k-k_0}x$ for a unique lattice $x$ within $\rho_0$, and $|O_{r_k}(x')\cap B(E,\rho_0\varepsilon^{k-k_0})|=|S_{k-k_0}(x)|$. By (1) the supremum over $k$ is the supremum of the increasing limits. $\square$

---

## 4. Computations

All orbit computations are exact breadth-first searches over $\Lambda$ (integer 4-vectors in the basis $1,\zeta,\zeta^2,\zeta^3$; multiplication by $\zeta^{\pm1}$ as in `sharp-bound-n5-period-two.md` §2; disk tests $|z\mp1|^2\le r^2$ as the exact sign of an element of $\mathbb Z[\varphi]$ in 128-bit integers; radii $r^2=(R_0+R_1\varphi)/R_D$ with $(R_0,R_1,R_D)=(3,1,1)$ for $r_c$, $(29,10,10)$, $(33,8,10)$, $(17,18,10)$, $(85,-24,10)$ for levels 0–3, and $(27,12,10)$ for $r^2=r_c^2+\varepsilon/10$). The C programs are throwaway code in the session scratch folder, described here so that they can be re-implemented. The arithmetic was validated against the repository engine: the orbits of $0$ at levels 0 and 1 have $1\,433$ and $30\,165$ points with $\max|\sigma|=53.7$ and $273.2$, as in `sharp-bound-n5-conjugate.md` Table 4.1. Distances and internal radii used only to *select* points (balls, guards) are double precision. Every membership decision is exact. A *capped* orbit claims nothing: a point not found in a capped orbit is not counted as a failure unless its own orbit is finite and does not contain the target ("exact non-member").

### 4.1 Which unit (orbit of $E$ at $r_c$)

`psim`: the orbit of $E$ at $r_c$ to $4\cdot10^7$ points ($\max|\sigma|=17\,443$). For every orbit point $y$ with $|y-E|\le1$ whose image $z=E+u(y-E)$ has $|\sigma z|\le0.6\cdot17\,443$ (so that the image lies in the explored part), test $z\in O(E)$.

**Table 4.1.**

| unit $u$ | found / tested | misses checked: exact non-members |
|---|---|---|
| $-\varepsilon=(3,0,2,2)$ | **166 077 / 166 077** | — |
| $\varepsilon$ | 130 162 / 166 069 | 8 of 8 |
| $\varepsilon^2=(13,0,8,8)$ | **12 428 / 12 428** | — |
| $-\varepsilon^2$ | 9 953 / 12 429 | 8 of 8 |
| $\varphi^{-1}$ | 45 800 / 1 031 574 | 2 of 8 (6 capped) |
| $-\varphi^{-1}$ | 41 080 / 1 031 576 | 2 of 8 (6 capped) |
| $\varphi^{-2}$ | 20 083 / 501 399 | 2 of 8 (6 capped) |
| $-\varphi^{-2}$ | 23 423 / 501 395 | 33 of 60 (27 capped) |

For $-\varepsilon$ with radius $1.3$, $1.6$, $2$, $3$ the counts are $226\,076/237\,055$, $292\,484/359\,163$, $450\,113/574\,788$, $653\,531/902\,794$. The failing preimages closest to $E$ are at distance $1.0662$, and the first 20 failing images checked are exact non-members (finite orbits of 21, 596 or 604 points, without $E$).

### 4.2 Exact data of Theorem 1

`k4.py` (exact, integers): each letter of $u_1,u_2,u_3$ (and $w_1,w_2,w_3$) applied to both ends of its segment.

**Table 4.2.** Slack $r_c^2-|z\mp1|^2$ before each letter, in $\mathbb Z[\varphi]$ ($0$ = tight; $4.4721=-2+4\varphi$).

| word | at the left end | at the right end | translation |
|---|---|---|---|
| $u_1=AAbb$ | $t=-\varphi^2$: $0,0,4.47,4.47$ | $t=-\varphi^{-1}$: $4.47,4.47,0,0$ | $(2,0,0,-2)=2\varphi E$ |
| $u_2=abAA$ | $t=-\varphi^{-1}$: $4.47,0,0,0$ | $t=1$: $0,0,4.47,4.47$ | $(0,-2,2,0)=-2E$ |
| $u_3=bbAB$ | $t=1$: $4.47,4.47,0,0$ | $t=\varphi^2$: $0,0,0,4.47$ | $(0,-2,2,0)=-2E$ |

The $w_i$ rows reproduce Table 2.1 of the critical-orbits note (slacks $1.7082$, $0.6525$, $4.0689$ at the non-tight ends). The words $u_i$ were found by `path` (shortest word, by breadth-first search with parent pointers, from $tE$ to $(t+2\varphi)E$ or $(t-2)E$ for the 66 lattice points $t=a+b\varphi$ of $[-\varphi^2,\varphi^2)$ with $|a+b(1-\varphi)|\le14$). The three words were the same along each piece.

### 4.3 Renormalization inclusion at $r_c$

`relmap`/`rel2`: for a start $y$ (random lattice points within $\rho$ of $E$ with $|\sigma y|\le M$, rounded from uniform samples in $\mathbb C\times\mathbb C$), compute $O(y)$ and $O(\Psi y)$ (cap as stated). Test $\Psi z\in O(\Psi y)$ for every $z\in O(y)$ within $\rho$ of $E$. A start counts as conclusive when both orbits are finite.

| radius | $\rho$, $M$, starts | conclusive starts | point checks | exact failures |
|---|---|---|---|---|
| $r_c$ | $0.72$, $80$, 800 (cap $3\cdot10^6$) | 592 | 1 152 962 | **0** |
| $r_c$ | $0.70$, $200$, 400 (cap $3\cdot10^6$) | 302 | 564 143 | **0** (34 inconclusive: $O(\Psi y)$ capped) |
| $r_c$ | $0.76$, $30$, 1 500 (cap $10^6$) | 946 | 214 645 | **0** |
| $r_c$ | $0.80$, $30$, 1 500 (cap $10^6$) | 977 | — | **7 starts**, smallest failing pair at distance $0.7753$ |
| $r_c$ | $0.90$, $30$, 20 | 13 | — | 1 start, failing point at distance $0.8452$ |

**Table 4.3** (`tower`, $\rho=0.8$, $r_c$). Sizes $|O(\Psi^kx)|$ and window counts $|S_k|$, where $S_k=\Psi^{-k}(O(\Psi^kx)\cap B(E,0.8\varepsilon^k))$. On all 44 starts with finite orbits up to $k=3$, $S_0\subseteq S_1\subseteq S_2\subseteq S_3$. Examples:

| start | $|O(\Psi^kx)|$, $k=0..3$ | $|S_k|$, $k=0..3$ |
|---|---|---|
| $(4,5,-1,6)$ | 8 170; 103 688; 1 359 179; 18 203 542 | 795, 903, 930, 936 |
| $(0,3,-2,2)$ | 643; 8 170; 103 688; 1 359 179 | 66, 72, 72, 72 |
| $(-5,2,-4,-2)$ | 40; 4 205; 52 234; 695 095 | 4, 35, 35, 35 |
| $(1,0,0,0)$ | 5; 31; 355; 4 205 | 1, 1, 1, 1 |

The orbit sizes grow by about 13 per step, as the level orbits do. The window counts grow and then stabilize. In Table 4.3, $S_{k+1}\setminus S_k$ contains points at all distances from $E$, not only near the window boundary.

### 4.4 Renormalization inclusion at the levels, and sharpness

`rel2` with orbit $A$ at the first radius and orbit $B$ at the second, $\rho=0.7$; every listed orbit was finite.

| radii ($y$ at → $\Psi y$ at) | starts ($M$) | point checks | failures |
|---|---|---|---|
| level 0 → level 1 | 300 ($M=20$) | 40 729 | **0** |
| level 1 → level 2 | 300 ($M=20$) and 300 ($M=60$) | 398 838 + 444 278 | **0** |
| level 2 → level 3 | 120 ($M=30$, cap $3\cdot10^7$) | 1 459 635 | **0** |
| level 0 → level 2 | 300 | 40 729 | 0 (implied by the two rows above) |
| level 0 → $\delta'=0.025$ | 300 | 40 729 | 30 starts (8 692 points) |
| level 0 → $\delta'=0.030,\ 0.040,\ 0.060$ | 300 | 40 729 | 49, 83, 130 starts |
| $r_c+\varepsilon/10$ → level 2 | 160 | 24 564 | 31 starts |

So the defect $\varepsilon\delta$ in RI cannot be replaced by $0.025$ at $\delta=1/10$ ($\varepsilon/10=0.02361$). Starting above $r_c$ fails, as it must: inclusion into a smaller radius is not expected.

### 4.5 The reverse inclusion fails

`rel3`: for $y$ within $0.7$ of $E$, test $\Psi^{-1}(O_{\rm level\,1}(\Psi y)\cap B(E,0.7\varepsilon))\subseteq O_{\delta'}(y)$, only on starts with both orbits finite.

| $\delta'$ | conclusive starts | starts with failures |
|---|---|---|
| $1/10$ (level 0) | 150 | 119 |
| $0$ ($r_c$) | 103 | 68 |
| $-1/10$ (above $r_c$) | 47 | 11 |

At $r_c$ itself the orbit of $E$ gives exact failures of $\Psi^{-1}$: for example $p=(-107,62,-105,-5)$ has a finite orbit of 596 points not containing $E$, while $\Psi p\in O(E)$ (`psim` with $u=\Psi^{-1}$ factor $(-1,0,2,2)=-\varepsilon^{-1}$: $470\,782/563\,061$ found within $0.25$).

### 4.6 $\Psi$ and the large orbits; classes

- `psio`: $\Psi(O(0)\cap B(E,0.7))\subseteq O(0)$ on $144\,916/146\,306$ tested points. Every miss has image internal radius above $6\,685$, beyond the completely explored part of the capped orbit ($4\cdot10^7$ points, $\max|\sigma|=13\,822$), so no failure is established. $\Psi(O(E))\subseteq O(E)$ is Table 4.1.
- `psi2`: $\Psi(O(-\zeta^2)\cap B(E,0.7))\subseteq O((-2,-2,-1,-2))$ on $102\,108/102\,108$. The reverse map lands in another class (0 found, as it must).
- Classes (`cls.py`, exact, the 20 $\Gamma$-classes of `sharp-bound-n5-invariant.md` Proposition 2): $\Psi$, and every unit zoom by $\pm\varepsilon$ about any of $0,\pm E,\pm\bar E$, fixes the classes of $0$ and of $E$. It permutes the classes of $-\zeta^2$, $(-2,-2,-1,-2)$, $\zeta^2$, $(2,2,1,2)$ cyclically in this order. So $\Psi^4$ is the least power fixing the class of $-\zeta^2$.
- `wit`: in $O(-\zeta^2)$ (cap $4\cdot10^7$) there are 110 points $x$ within $0.7$ of $E$ with $\Psi^4x\in O(-\zeta^2)$, out of 118 tested. The 8 misses have image internal radius $15\,699$–$17\,057$, at the edge of the explored part ($\max|\sigma|=17\,632$). The witness of Proposition 7 is the first of them in breadth-first order.

### 4.7 Holes on offset lines

`holes.py` (50-digit `mpmath`) evaluates the exact domains of Theorem 2 and compares them with Corollary 2.1. At $\delta=10^{-4}$ and $s=3\cdot10^{-4},10^{-4},10^{-5},0$ and their negatives, and at $\delta=0$, the exact and first-order widths agree to relative $10^{-3}$. For example $H_{-\varphi^{-1}}=2.247570\cdot10^{-4}$ against $2.247214\cdot10^{-4}$ at $s=\delta=10^{-4}$, and $1.600025\cdot10^{-5}$ against $1.6\cdot10^{-5}$ at $\delta=0$, $s=10^{-5}$. On the grid $\delta\in\{10^{-2},3\cdot10^{-3},10^{-3},10^{-4}\}$, $s/\delta\in\{-0.1,-0.0975,\dots,0.1\}$, the exact total hole width of $T$ is at most $1.795\,\delta$ (at $\delta=10^{-2}$, $s=\delta/10$), below the proved bound $2.002\,\delta$ of Theorem 3.

---

## 5. What this changes in the earlier notes

- **K4** (`sharp-bound-n5-critical-orbits.md` §5) is Theorem 1 here.
- **K3** is false (Theorem 3, after the referee's computation). Its corrected form is Corollary 4.1, which follows from Conjecture A. The repaired statement of §6.3 of the critical-orbits note points here.
- **K2**'s first-order claim is Corollary 2.1. The cascade part of K2 is not proved.
- **The renormalization unit.** `sharp-lower-bound-limit-system.md` §5.3 and the period-two note found period two at the levels, with the zoom $+\varepsilon$, for equality of first-return sets. At $r_c$, and between consecutive levels, the data support period one with the zoom $-\varepsilon$, for *inclusion* of orbit relations. The two are compatible: equality fails with both units, and the observation $R_{k+1}=-R_k$ at $E$ itself is the unit $-\varepsilon$.
- **Lemma 6 of the critical-orbits note** (depth formulation) is the setting of §6 below.
- **The chord line below $r_c$.** Conjecture D of `sharp-bound-n5-orbit-of-zero.md` (not refereed) describes $O_{r_k}(0)\cap\mathbb RE$ at the levels as a cut-and-project set, and its inclusion "$\supseteq$" asks for words reaching every window point. At $r_c$, Theorem 1 supplies them for the part $2\mathbb Z[\varphi]E$ on the whole long segment, with the three words $u_i$. Below $r_c$ the holes of $M$ (Corollary 2.1) are the natural tool for that inclusion.

## 6. The remaining gap

By Lemma 6 of the critical-orbits note, (B) says that for each $r<r_c$ the depth-$r$ strict orbits of the $r_c$ system are uniformly bounded. The plan of task 4 was:
1. find an exact renormalization $\mathcal R$ of the $r_c$ system at the tight points;
2. show that depth $\delta$ at scale $k$ corresponds to depth $\delta/\varepsilon$ at scale $k-1$;
3. conclude that a depth-$\delta$ orbit descends only $\log(1/\delta)/\log\varphi^3$ scales before the effective depth is macroscopic, where finiteness is certified, and bound the orbit by a product over those scales of a per-annulus constant (from a relative certificate for one annulus).

Where it stands:
- Step 2 is what RI says, with the sharp constant (§4.4), so the defect does transform as $\delta\mapsto\varepsilon\delta$ under the zoom $-\varepsilon$.
- Step 1 holds only as an inclusion (RI, unproved), and step 3 needs the *other* inclusion: a deep window at defect $\varepsilon\delta$ must have no more connections than the coarse window at a defect $c\,\delta$ with $c>\varepsilon$. That inclusion fails exactly at every defect tested, including $\delta'=0$ and $\delta'<0$ (§4.5). Zooming in adds connections ($S_k\subsetneq S_{k+1}$, Table 4.3).
- So the descent argument is **dead in this form**. What survives is Proposition 8: under RI, (R-core-t) at $E$ is equivalent to a uniform bound on the classes of the monotone limit relation $S_\infty$. The data show $S_k$ stabilizing after one to three steps on every computed start (Table 4.3). Neither RI nor the bound on $S_\infty$ is proved, and (R-bulk-t) is untouched.

The precise open statements are therefore:
1. **RI** (Conjecture, §2.4). A proof would plausibly be a finite verification of the following kind. Take a window $W$ at the four tight points with finitely many first-return germs at $r_c$ (as in the certified four-window closures of `sharp-lower-bound-limit-system.md` Table 4.2). For each germ $g$, exhibit a word realizing $\Psi g\Psi^{-1}$ on $\Psi(\operatorname{dom}g)$, and check the containment of domains bounded by circular arcs. This is a certificate-scale computation and was not attempted.
2. **(L)**: $\sup_x|S_\infty(x)|<\infty$ at the levels.
3. (R-bulk-t), as before.

---

## Appendix. Reproduction

Programs (scratch, not committed): `z5.h` (arithmetic, exact disk test, hash set, breadth-first orbit), `psim`, `psio`, `psi2`, `psimiss`, `wit` (zoom tests on one capped orbit), `orb` (orbit of each listed point: finite or capped, contains the target or not), `rel`, `relv`, `relmap`, `rel2`, `rel3` (inclusion tests between two orbits at two radii), `tower`, `tower2` (the sets $S_k$), `path` (shortest words), `exre` (exploratory), `gen.py` (random lattice points with prescribed physical and internal radius, by inverting the Minkowski embedding and rounding), `cls.py` ($\Gamma$-classes modulo $2(1-\zeta)\Lambda$, Hermite basis $(2,0,0,8),(0,2,0,8),(0,0,2,8),(0,0,0,10)$), `k4.py` (Table 4.2), `lines.py`, `centres.py`, `holes.py`, `wnum.py` (Table 2.1 and §4.7, `sympy`/`mpmath`). Seeds of the random samples: 1–7, 11–13, 21–23, 31. The repository engine `tdcsg-orbit orbit` (copied to scratch) was used only for cross-checks; no `certify` run was made.
