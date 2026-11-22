# Orbits of $GG_5$ at the critical radius $\sqrt{3+\varphi}$: the chord, its tube, and what survives below

Authors: Eric Vergo, Claude

**Review.** Independently refereed: [`referee-report-sharp-bound-n5-critical-orbits.md`](referee-report-sharp-bound-n5-critical-orbits.md). Verdict: Theorems 1, 3, 4, 5, Propositions 2.2, 2.3, 6.1, Lemma 6 and Corollaries 1.1, 3.1, 5.1 correct; Theorem 2 and Corollary 2.1 correct after minor fixes (the domains of Theorem 2 are taken inside each word's own segment; the description of the holes; one rounded constant in the comparison with the conjugate note), applied below. The computed values of §4.1–§4.4 were reproduced with the engine and independent exact code. Conjecture K3 is false as stated, uniformly over all orbits, and needs a restriction on the starting points (report §5); K1, K2 and K4 are consistent with the data. The parts revised after that report (K2, K3, K4, §6.3, which cite [`sharp-bound-n5-critical-renormalization.md`](sharp-bound-n5-critical-renormalization.md)) were refereed with that note in [`referee-report-sharp-bound-n5-critical-renormalization.md`](referee-report-sharp-bound-n5-critical-renormalization.md): correct, with one clause of §6.3 item 1 made precise.

**What this note establishes, and what it does not.**

- **Not established: (B).** This note does **not** prove that $GG_5(r)$ is finite for every $r<r_c=\sqrt{3+\varphi}$. The equality $r_{\rm crit}(5)=r_c$ remains open. §6 explains why the two arguments this line was asked to try (a limiting or semicontinuity argument, and an arithmetic obstruction from norms) cannot by themselves give (B), and states the remaining gap.
- **Proved** (§3), for the system at $r_c$ and just below it:
  1. the chord rotation of Theorem A is realized by chains that move only at points of the *open* disks, so the orbits of all but countably many chord points stay infinite when the disks are opened (Theorem 1). Hence the union of all the systems with $r<r_c$ is an infinite system, and orbit sizes tend to infinity as $r\uparrow r_c$;
  2. below $r_c$ the three chord words still realize the chord rotation, except on holes of width $\delta/\sqrt5+O(\delta^2)$, $\delta=r_c^2-r^2$, on both sides of $-\varphi^{-1}$, to the right of $-\varphi^{-3}$ and to the left of $1$, given in closed form (Theorem 2). Consequently $|O_r(0)|\ge0.97/\delta-3$ and the internal extent of $O_r(0)$ is at least $4.13/\delta-12$ for $0<\delta\le1/10$ (Corollary 2.1);
  3. an exact height function: along the chord words, $\operatorname{Re}(\sigma x/\sigma E)-\operatorname{Re}(x/E)$ drops by exactly $2\sqrt5$ per step (Proposition 2.2);
  4. the chord words act as translations along $E$ on explicit two-dimensional convex domains (the *tube*), so every line parallel to the chord is invariant under them (Proposition 2.3);
  5. at every radius, points off the closure of the cut set have finite orbits, with $|O(x)|\le36.26/d(x)^2$ at $r_c$, where $d(x)$ is the distance to that closure; so every infinite orbit at $r_c$ lies in the closure of the cut set, which contains the chord (Theorem 3);
  6. a congruence obstruction: modulo $2(1-\zeta)\mathbb Z[\zeta]$ the lattice splits into 20 classes under the full rotation group, and the lattice points of the chord lines lie in only 2 of them. So the orbits of lattice points in the other 18 classes never meet the chord or its mirror image, at any radius (Theorem 4);
  7. openness at non-norm radii: if $GG_5(r_0)$ is finite and $r_0^2$ is not $|w|^2$ for any $w\in\mathbb Q(\zeta_5)$, then $GG_5$ is finite on a neighbourhood of $r_0$. So if $GG_5(r_{\rm crit})$ were finite, $r_{\rm crit}^2$ would be such a norm (Theorem 5).
- **Computed** (exact arithmetic; §4, with the reproducing commands):
  1. a classification of all lattice points with coefficients in $[-2,2]$ at $r_c$: 19 orbits up to symmetry, 15 finite (largest 8 376 points) and 4 reaching the cap. Two of the four meet the chord. The other two lie in chord-free classes, so by Theorem 4 they never meet it, yet their orbits reach $3\cdot10^7$ points;
  2. in the large orbits at $r_c$ the populated lines parallel to the chord nearest to it are at offsets $\pm\tfrac12\varphi^{-m}$ or $\pm\tfrac{\sqrt5}2\varphi^{-m}$ that tend to $0$; many other populated lines lie between them;
  3. at the levels $r_k$, $k\le3$, the innermost such line (other than $\mathbb RE$) sits at offset of order $\delta$: exactly $0.385\,\delta_k$ for the orbit of $0$ ($k=0,\dots,3$), and $0.041\,\delta_k$ or $0.066\,\delta_k$, alternating with the parity of $k$, for the orbit of $-\zeta^2$;
  4. the cell counts of the orbit of $0$ at $r_c$ (floating-point binning of exact points) give slopes about $1.8$ between the scales tested; the counts have not converged in the number of points, so this is not a dimension estimate.
- **Conjectured** (§5): every infinite orbit at $r_c$ accumulates on the chord (or its mirror); the infinite orbits are cascades of chord-parallel runs with offsets tending to $0$; below $r_c$ the cascade stops at offset of order $\delta$. The uniform form of the last statement (K3) is false; its corrected form follows from Conjecture A of the conjugate note (§5).
- **Proved in** [`sharp-bound-n5-critical-renormalization.md`](sharp-bound-n5-critical-renormalization.md): K4 is proved (the long segment carries the rotation by $2\varphi$ of $\mathbb R/2\varphi^2\mathbb Z$, realized by three words of length 4, with $T$ as first-return map); the first-order part of K2 and the failure of K3 are theorems there.

**Honest assessment.** The line does not close (B). The forcing argument (an infinite orbit below $r_c$ must create a structure that exists only at $r\ge r_c$) is **dead as stated**: the limit of the systems below $r_c$ is itself infinite (Theorem 1), and arithmetic excludes only exact boundary contact at lattice points, not accumulation (§6). What the line adds is a description of the infinite orbits at $r_c$ with a new, one-dimensional coordinate: the offset of a chord-parallel line. The remaining gap can be phrased as a statement about that coordinate (§6.3). Whether this is easier than the gap stated in the earlier notes is not known.

**Relation to [`sharp-bound-n5-conjugate.md`](sharp-bound-n5-conjugate.md)** (refereed). That note proves the linear drift of the conjugate coordinate along the chord (its Theorem 4) and a two-sided cut-off of the chord at scale $1/\delta$ (its Theorem 6: $0.0590/\delta-1.18<K(\delta)\le(F_j-1)/2<2.12/\delta$). Here Proposition 2.2 extends the drift identity from chord points to every lattice point of the tube, as the height $H$. Theorem 2 gives the exact holes, hence the leading constant of the lower bound: about $0.97/\delta$ chord points against $0.059/\delta$ there, and internal reach $4.13/\delta$ against $0.502/\delta$. The exact chain counts of §4.1 reproduce its exit index $K(\delta_k)=(F_{3k+7}-1)/2$ for $k=0,\dots,3$. The results on the strict system, the tube, the exceptional set, the congruence classes, openness, and the chord-parallel lines are not in that note.

Everything here concerns $n=5$. Status labels: **proved**, **computed** (exact, with a command), **conjectured**.

---

## 1. Setting and definitions

Notation as in `critical-radius-n5.md` §1 and `sharp-lower-bound-n5.md` §1:
- $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$, $\varphi=(1+\sqrt5)/2$, and $\sigma\colon\zeta\mapsto\zeta^2$ (internal embedding; on $\mathbb Q(\varphi)$ it is $\sqrt5\mapsto-\sqrt5$);
- $D_1,D_2$ are the closed disks of radius $r$ about $-1,+1$; $a,b$ rotate by $\zeta^{-1}$ about $-1,+1$ on their disks and are the identity elsewhere; $GG_5(r)=\langle a,b\rangle$; $O_r(x)$ is the orbit of $x$;
- words are read left to right; $A,B$ are the global rotations;
- $r_c^2=3+\varphi$, and for $r\le r_c$ we write $\delta=\delta(r)=r_c^2-r^2\ge0$. The levels are $r_k^2=3+\varphi-\varepsilon^k/10$, $\varepsilon=\varphi^{-3}$.

**D1 (strict system).** Let $a^\circ$ be $A$ on the *open* disk $\{|z+1|<r_c\}$ and the identity elsewhere, likewise $b^\circ$, and $G^\circ=\langle a^\circ,b^\circ\rangle$. These are bijections. $O^\circ(x)=G^\circ x$ is the *strict orbit*. A chain $z_0,\dots,z_L$ with $z_i=S_i(z_{i-1})$, $S_i\in\{A^{\pm1},B^{\pm1}\}$, is *strict* if each $z_{i-1}$ lies in the open disk of radius $r_c$ of $S_i$ (Definition 3.1 of `sharp-lower-bound-combined.md`). $O^\circ(x)$ is the set of endpoints of strict chains from $x$.

**D2 (depth).** For $r\le r_c$, a strict chain has *depth at least $r$* if each moving step starts at a point $z$ with $|z-p|\le r$ for the centre $p$ of its rotation.

**D3 (the chord and its rotation).** $E=\zeta-\zeta^2=(0,1,-1,0)$, $F=\varphi^{-1}E$, $G=\varphi^{-3}E$, and the chord is $\mathcal C=\{tE:-1\le t\le1\}$. The three words of `critical-radius-n5.md` §3.2 are
$$w_1=a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}\ \text{on }[E',F'],\qquad w_2=abab\,b\ \text{on }[F',G'],\qquad w_3=aba\,b^{-1}a^{-1}b^{-1}\ \text{on }[G',E],$$
with $E'=-E$, etc. In the parameter $t$ they act as $t\mapsto t+2\varphi^{-1}$ ($w_1,w_2$) and $t\mapsto t-2\varphi^{-2}$ ($w_3$). The induced map $T$ is the rotation by $2\varphi^{-1}$ of $\mathbb R/2\mathbb Z$. The *tight parameters* are
$$b_1=-\varphi^{-1}\ (=1-\varphi),\qquad b_2=1,\qquad b_3=-\varphi^{-3}\ (=3-2\varphi).$$
The *exceptional set* is $X=(1+2\mathbb Z[\varphi])\cup(\varphi^2+2\mathbb Z[\varphi])\subset\mathbb R$. Note $b_2,b_3\in1+2\mathbb Z[\varphi]$ and $b_1\in\varphi^2+2\mathbb Z[\varphi]$. The mirror chord is $\bar{\mathcal C}$.

**D4 (tube domains).** $U_i(r)$ is the set of $x\in\mathbb C$ at which every letter of $w_i$ applies at radius $r$ when $w_i$ is read as the composite of global rotations. Equivalently $U_i(r)=\bigcap_j D(c'_{ij},r)$, where $c'_{ij}=h_{ij}^{-1}(p_{ij})$, $h_{ij}$ is the composite global rotation of the first $j-1$ letters and $p_{ij}=\pm1$ the centre of letter $j$.

**D5 (height).** For $x\in\mathbb Q(\zeta)$, $H(x)=\operatorname{Re}\bigl(\sigma(x)/\sigma(E)\bigr)-\operatorname{Re}(x/E)$.

**D6 (cut set, exceptional closure).** $K(r)=\bigcup_{g\in GG_5(r)}g(\partial D_1\cup\partial D_2)$ and $\bar K(r)$ its closure. For $x\notin\bar K(r)$, $d_r(x)$ is the distance from $x$ to $\bar K(r)$.

**D7 (congruence classes).** $L=2(1-\zeta)\Lambda$, an ideal of index $N(2)N(1-\zeta)=16\cdot5=80$. $\Gamma=\langle A,B\rangle$ is the full-plane group. Since $L$ is stable under multiplication by $\zeta$, $\Gamma$ acts on $\Lambda/L$; its orbits there are the *$\Gamma$-classes*. A class is a *chord class* if it contains a lattice point of the line $\mathbb RE$ or of $\mathbb R\bar E$.

**D8 (norm radius).** $r$ is a *norm radius* if $r^2=|w|^2$ for some $w\in\mathbb Q(\zeta)$; otherwise a *non-norm radius*. The non-norm radii include every $r$ with $r^2\notin\mathbb Q(\varphi)$ (since $|w|^2\in\mathbb Q(\varphi)$), and every level $r_k$ (`sharp-lower-bound-n5.md` Lemma 2.2).

**D9 (chord-parallel lines).** For $y\in\Lambda$, the line through $y$ parallel to the chord has *key* $\kappa(y)=y\bar E-\bar yE\in\Lambda$ (purely imaginary) and *offset* $s(y)=\operatorname{Im}(y\bar E)/|E|$, the signed distance of $y$ from the line $\mathbb RE$. Two lattice points lie on the same chord-parallel line iff their keys are equal.

---

## 2. Statements

### 2.1 At the critical radius

**Theorem 1 (the chord rotation is strict).** Let $t\in[-1,1)$, $t\notin X$. Then every point $T^k(t)E$, $k\in\mathbb Z$, is the endpoint of a strict chain from $tE$. So $O^\circ(tE)$ is infinite. [proved]

**Corollary 1.1.** For $t$ as in Theorem 1, $O^\circ(tE)=\bigcup_{r<r_c}O_r(tE)$ is an increasing union of sets with infinite union, so $|O_r(tE)|\to\infty$ as $r\uparrow r_c$. This holds for $t=0$ and for all but countably many $t$. In particular the strict group $G^\circ$ has infinite orbits: (B) cannot be obtained from a bound on the open-disk system at $r_c$. [proved]

**Proposition 2.3 (the tube).** For every $r$ and $i$, $w_i$ acts on $U_i(r)$ as the translation by $\tau_i E$, with $\tau_1=\tau_2=2\varphi^{-1}$ and $\tau_3=-2\varphi^{-2}$. Hence every line parallel to the chord is mapped into itself by each $w_i$ wherever it applies. At $r=r_c$, $U_i(r_c)\supseteq$ the closed sub-segment of $w_i$, and the pull-back centres $c'_{ij}$ are the lattice points of Table 2.1. [proved; the centres are an exact computation]

**Table 2.1.** Pull-back centres $c'_{ij}$ (D4) and the tight tests. "Tight at" names the segment end at which $|x-c'_{ij}|^2=3+\varphi$ exactly; the other end then has slack at least $(-22+14\varphi)=0.6525$.

| word | letters | $c'_{ij}$ in order | tight tests (letter: end) |
|---|---|---|---|
| $w_1$ | $a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}$ | $(-1,0,0,0)$, $(-1,0,0,0)$, $(-1,0,0,2)$, $(-1,0,-2,2)$, $(-1,2,-2,2)$ | 3rd, 4th: $F'$ |
| $w_2$ | $ababb$ | $(-1,0,0,0)$, $(-1,2,0,0)$, $(-1,2,-2,0)$, $(-1,2,-2,2)$, $(-1,2,-2,2)$ | 2nd, 3rd: $F'$ |
| $w_3$ | $aba\,b^{-1}a^{-1}b^{-1}$ | $(-1,0,0,0)$, $(-1,2,0,0)$, $(-1,2,-2,0)$, $(-1,2,-2,2)$, $(-1,2,-4,2)$, $(-1,4,-4,2)$ | 1st, 2nd: $E$; 5th, 6th: $G'$ |

In particular $w_1$ is not tight at $E'$ and $w_2$ is not tight at $G'$.

**Theorem 3 (exceptional set; any radius).** Let $r>0$ and $x\notin\bar K(r)$, and let $U$ be the component of $\mathbb C\setminus\bar K(r)$ containing $x$. Every $g\in GG_5(r)$ acts on $U$ as one isometry $z\mapsto\zeta^jz+t$ and maps $U$ onto a component. Hence
$$|O_r(x)|\le\frac{5\,\operatorname{Area}(D_1\cup D_2)}{\operatorname{Area}(U)}\le\frac{5\,\operatorname{Area}(D_1\cup D_2)}{\pi\,d_r(x)^2}.$$
At $r=r_c$, $\operatorname{Area}(D_1\cup D_2)=22.7826$, so $|O_{r_c}(x)|\le36.26/d_{r_c}(x)^2$. [proved]

**Corollary 3.1.** Every point with an infinite orbit at $r_c$ lies in $\bar K(r_c)$. In particular $\mathcal C\subseteq\bar K(r_c)$, and $K(r_c)$ is not a finite union of circular arcs. [proved]

**Theorem 4 (congruence obstruction).** $\Lambda/L$ has 80 residues, which form 20 $\Gamma$-classes (15 of size 5, and 5 fixed residues, those of $z\equiv1\pmod 2$). The lattice points of $\mathbb RE\cup\mathbb R\bar E$ occupy 7 residues, which lie in exactly two $\Gamma$-classes: the class of $0$ (3 chord residues) and the class of $E$ (4 chord residues). Consequently, for every $r>0$ and every lattice point $y$ outside these two classes, $O_r(y)$ contains no point of $\mathbb RE\cup\mathbb R\bar E$, so in particular none of $\mathcal C\cup\bar{\mathcal C}$. For example $y=-\zeta^2$, $(-1,-1,0,-1)$, $(-2,-2,-1,-2)$ and $(-2,-2,-1,-1)$. [proved; the class enumeration is an exact finite computation]

### 2.2 Below the critical radius

**Theorem 2 (the chord words below $r_c$).** Let $0<\delta<0.65$ and put
$$h(\delta)=\frac{2\delta/\sqrt5}{1+\sqrt{1-\kappa\delta}},\qquad\kappa=\tfrac45(3-\varphi)=1.10557 .$$
At radius $r$, $r^2=3+\varphi-\delta$, the set of parameters $t$ in the segment of $w_i$ at which $w_i$ applies (every letter's test passes) is exactly
$$w_1:\ [-1,\,b_1-h(\delta)],\qquad w_2:\ [b_1+h(\delta),\,b_3],\qquad w_3:\ [b_3+h(\delta),\,1-h(\delta)].$$
So the chord words realize $T$ on the chord minus holes of width $h(\delta)=\delta/\sqrt5+O(\delta^2)$ on both sides of $b_1$, to the right of $b_3$ and to the left of $b_2$. ($w_2$ also applies beyond its segment, to the right of $b_3$; there it does not realize $T$, and the statement is restricted to the segments for that reason.) [proved]

**Corollary 2.1 (explicit growth below $r_c$).** For $0<\delta\le1/10$:
1. $O_r(0)$ contains at least $0.97/\delta-3$ points of the chord; in terms of $r$, $|O_r(0)|\ge0.226/(r_c-r)-3$;
2. $\max_{y\in O_r(0)}|\sigma(y)|\ge4.13/\delta-12$;
3. $|GG_5(r)|\ge0.97/\delta-3$, so the group order tends to infinity as $r\uparrow r_c$. [proved]

**Proposition 2.2 (height; on chord points this is Theorem 4(1) of `sharp-bound-n5-conjugate.md`).** For $x\in\mathbb Q(\zeta)\cap U_i(r)$, $H(w_i x)=H(x)-2\sqrt5$, at every radius. So along chord words $H$ is strictly decreasing, chord-word orbits of lattice points are injective, and after $k$ chord-word steps from a chord point $t_0E$, $|\sigma(t_kE)|\ge(2\sqrt5\,k-|\sigma(t_0)-t_0|-1)\,|\sigma E|$ with $|\sigma E|=2\sin72^\circ=1.9021$. [proved]

**Theorem 5 (openness at non-norm radii).** If $r_0$ is a non-norm radius and $GG_5(r_0)$ is finite, then there is $r_1>r_0$ such that $GG_5(r)$ is finite for every $r<r_1$. [proved, from refereed results]

**Corollary 5.1 (is the infinite set closed?).** The set $\mathcal I=\{r:GG_5(r)\text{ infinite}\}$ is $[r_{\rm crit},\infty)$ unless $r_{\rm crit}$ is a norm radius at which $GG_5$ is finite. Since $GG_5(r_c)$ is infinite (Theorem A), (B) holds iff $\mathcal I=[r_c,\infty)$. [proved]

**Lemma 6 (depth formulation).** For $r<r_c$, $O_r(x)$ is the set of endpoints of strict chains from $x$ of depth at least $r$. Hence (B) holds iff for every $r<r_c$ the depth-$r$ strict orbits of the single system at $r_c$ are uniformly bounded in size. [proved]

**Proposition 6.1 (what an infinite orbit below $r_c$ would have to do).** Suppose $r<r_c$ and $O_r(x)$ is infinite. Then:
1. $O_r(x)\subseteq O^\circ(x)$, and $O^\circ(x)$ is infinite;
2. $O_r(x)$ has infinitely many points in the four windows of circumradius $0.1815$ about $\pm E,\pm\bar E$ (modulo the certified four-window closure of `sharp-lower-bound-limit-system.md` Table 4.2, row $(5,-1,4,0)$);
3. if $x\in\Lambda$, its points have unbounded internal coordinate; and if $r$ is a non-norm radius equal to $r^*(x)$, the orbit accumulates from inside at a point of $\partial D_1(r)\cup\partial D_2(r)$ that is not in $\mathbb Q(\zeta)$. [proved]

None of 1–3 is contradictory. §6 says why.

---

## 3. Proofs

### 3.1 Theorem 1 and Corollary 1.1

*Strict convexity.* If $p\ne q$ lie in a closed disk $D$ of radius $\rho$ about $c$, every point $(1-s)p+sq$, $0<s<1$, lies in the open disk: $|(1-s)(p-c)+s(q-c)|\le(1-s)|p-c|+s|q-c|\le\rho$, with equality only if $p-c,q-c$ are parallel, of the same direction and both of length $\rho$, i.e. $p=q$.

*The words at the segment ends.* Lemma 3.1 of `critical-radius-n5.md` checks, letter by letter, that both endpoints of every intermediate segment lie in the closed disk of the letter. By strict convexity every interior point of each intermediate segment lies in the open disk, so each $w_i$ is strict on the open sub-segment. At the ends, Table 2.1 lists exactly which tests are tight (exact computation in $\mathbb Z[\varphi]$, reproduced in §4.1). $w_1$ is strict at $E'$ ($t=-1$; slacks $-2+4\varphi$, $-2+4\varphi$, $-8+6\varphi$, $-22+14\varphi$, $-38+26\varphi$, all positive) and $w_2$ is strict at $G'$ ($t=b_3$). So the strict domains are $[-1,b_1)$ for $w_1$, $(b_1,b_3]$ for $w_2$ and $(b_3,1)$ for $w_3$, and on $[-1,1)\setminus\{b_1,b_2,b_3\}$ the strict words realize $T$ (at $t=b_3$ the strict word is $w_2$, which maps $G'$ to $E$; Theorem 1 does not need this case).

*Avoiding the tight parameters.* $T^k(t)\in t+2\mathbb Z[\varphi]$, since $2\varphi^{-1},2\varphi^{-2},2\in2\mathbb Z[\varphi]$. If $T^k(t)=b_j$, then $t\in b_j+2\mathbb Z[\varphi]\subseteq X$. So for $t\notin X$ the two-sided $T$-orbit avoids $b_1,b_2,b_3$. Each forward step $T^k(t)\to T^{k+1}(t)$ is then a strict chain of length 5 or 6. Each backward step is the reverse of the strict chain from $T^{k-1}(t)$, and the reverse of a strict chain is strict, since $A^{-1}$ acts on the same open disk as $A$. The points $T^k(t)E$ are distinct because $T$ is an irrational rotation. $\square$

*Corollary 1.1.* A strict chain has finitely many steps, each strictly inside an open disk, so it is an $r$-chain for every $r$ above the largest of its finitely many distances $|z-p|$ (`sharp-lower-bound-combined.md` Lemma 3.3 gives the converse inclusion). So $O^\circ(x)=\bigcup_{r<r_c}O_r(x)$, an increasing union by orbit monotonicity (`boundary-contact.md` Theorem 3.1). $X$ is countable and $0\notin X$, since $0\in2\mathbb Z[\varphi]$, while every element of $1+2\mathbb Z[\varphi]$ and of $\varphi^2+2\mathbb Z[\varphi]$ is non-zero modulo $2$. $\square$

### 3.2 Theorem 2 and Corollary 2.1

*Domains.* Fix a word, a letter with centre $p$, and the current images $P_j,Q_j$ of the segment ends. The letter applies at the parameter $s\in[0,1]$ of the segment iff $f(s)=|(1-s)(P_j-p)+s(Q_j-p)|^2\le r^2$. $f$ is a convex quadratic with leading coefficient $L^2=|Q-P|^2$, so the set is an interval.
- A non-tight letter has $f(0),f(1)\le r_c^2-0.6525<r^2$ when $\delta<0.65$ (Table 2.1 slacks, exact), so it applies on all of $[0,1]$.
- A tight letter, measured from its tight end, has $f(s)=r_c^2-|f'(0)|s+L^2s^2$ and $f(1)<r^2$. So it applies exactly on $[s_-,1]$ with $s_-=2\delta/\bigl(|f'(0)|+\sqrt{f'(0)^2-4L^2\delta}\bigr)$. The discriminant is positive because $f'(0)^2/(4L^2)\ge1/\kappa=0.9045>\delta$.
- The exact data (§4.1) are as follows. At $F'$ the binding letter of $w_1$ (the 4th) and of $w_2$ (the 2nd) have $f'(0)=4-3\varphi$, with $L^2=18-11\varphi$ and $t$-length $\ell=\varphi^{-2}$. At $E$ and $G'$ the binding letters of $w_3$ (the 2nd and the 5th) have $f'(0)=-6+2\varphi$, with $L^2=28-16\varphi$ and $\ell=2\varphi^{-1}$. In both cases one checks in $\mathbb Z[\varphi]$ that $\ell/|f'(0)|=1/\sqrt5$ and $4L^2/f'(0)^2=\kappa$. For example $(2-\varphi)(2\varphi-1)=3\varphi-4$ with $2\varphi-1=\sqrt5$, and $(12-4\varphi)(25-15\varphi)=5(72-44\varphi)$.
- The other tight letter at each end has $|f'(0)|$ larger by the factor $\sqrt5$ (e.g. $(3\varphi-4)(2\varphi-1)=10-5\varphi$), so its hole is smaller.

Hence the $t$-hole is $\ell s_-=h(\delta)$ at each tight end, and the domains are as stated. $\square$

*Corollary 2.1.*
1. *Distance to the holes.* For $k\ge0$ put $x=T^k(0)-b$ with $b\in\{b_1,b_2,b_3\}$. Then $x\in b+2\mathbb Z[\varphi]$. The norm is odd: $N(b_2)=1$ and $N(b_1)=N(b_3)=-1$, and $N(b+2y)\equiv N(b)\pmod2$. So $|x|\ge1/|\sigma(x)|$. Now $T^k(0)=2k\varphi^{-1}-2m$ with $|T^k(0)|\le1$, so $\sigma(T^k(0))=-2k\varphi-2m=-2\sqrt5\,k+T^k(0)$, using $\varphi+\varphi^{-1}=\sqrt5$. With $|\sigma(b)|\le\varphi^3$ this gives $|\sigma(x)|\le2\sqrt5\,k+5.24$. Backward iterates are treated in the same way.
2. *Valid steps.* By Theorem 2, the forward chain from $0$ is valid at $T^k(0)$ whenever $1/(2\sqrt5k+5.24)>h(\delta)$, for every $k$ up to the first failure. So it has at least $N\ge(1/h-5.24)/(2\sqrt5)$ steps, and the backward chain at least $N-1$ steps.
3. *Count.* With the starting point, that is at least $(1/h-5.24)/\sqrt5$ distinct chord points (distinct by Theorem 1). For $\delta\le1/10$, $1/h\ge\sqrt5/(1.02929\,\delta)$, which gives at least $0.9715/\delta-2.35$ points.
4. *In terms of $r$.* $\delta=(r_c-r)(r_c+r)\le2r_c(r_c-r)$.
5. *Internal extent.* $|\sigma(T^N(0)E)|=|\sigma(T^N(0))|\,|\sigma E|\ge(2\sqrt5N-1)\cdot1.9021\ge(1/h-6.24)\cdot1.9021\ge4.13/\delta-12$.
6. *Group order.* A finite group has order at least its largest orbit. $\square$

### 3.3 Propositions 2.2, 2.3

*Proposition 2.3.* On $U_i(r)$ every letter applies, so $w_i$ acts as the composite global rotation. Its rotation part is $\zeta^0$ (the exponents sum to $0\bmod5$) and its translation part is $\tau_iE$ (Lemma 3.1 of `critical-radius-n5.md`). The centres of Table 2.1 come from applying the inverse prefixes to $\pm1$. $\square$

*Proposition 2.2.* $w_ix=x+\tau_iE$ with $\tau_i\in\mathbb Q(\varphi)$, so $H(w_ix)-H(x)=\sigma(\tau_i)-\tau_i$. Now $\sigma(2\varphi^{-1})-2\varphi^{-1}=-2\varphi-2\varphi^{-1}=-2\sqrt5$, and $\sigma(-2\varphi^{-2})+2\varphi^{-2}=-2(\varphi^2-\varphi^{-2})=-2\sqrt5$. For chord points, $H(tE)=\sigma(t)-t$, and the bound on $|\sigma(t_kE)|$ follows from $|t_k|\le1$. $\square$

### 3.4 Theorem 3 and Corollary 3.1

$K=K(r)$ is invariant: $g(K)=K$ for all $g$, since $K$ is a union over the whole group. Let $U$ be a component of $\mathbb C\setminus\bar K$.

*Induction on word length.* Suppose $g'(U)$ is a connected open set disjoint from $K$ on which $g'$ is one isometry. It misses $\partial D_p\subseteq K$, so it lies in $\operatorname{int}D_p$ or outside $D_p$. The next letter then acts on it as one isometry, and $(sg')(U)$ is again connected, open and disjoint from $s(K)=K$.

*Components go to components.* An open set disjoint from $K$ is disjoint from $\bar K$. So $g(U)$ lies in one component $V$, and applying the argument to $g^{-1}$ gives $g(U)=V$.

*Counting.* If $U$ misses $D_1\cup D_2$, every generator fixes it and $|O(x)|=1$. Otherwise $U\subseteq\operatorname{int}(D_1\cup D_2)$, and the distinct images $g(U)$ are disjoint subsets of $D_1\cup D_2$ of area $\operatorname{Area}(U)$. For a fixed image $V$, the maps $g|_U$ onto $V$ have the form $z\mapsto\zeta^jz+t$ (`critical-radius-n5.md` Lemma 1.1). For each $j$ there is at most one $t$, since a non-trivial translation cannot map the bounded set $U$ onto itself. Finally $U\supseteq B(x,d_r(x))$.

At $r_c$, $\operatorname{Area}(D_1\cup D_2)=2\pi r_c^2-\bigl(2r_c^2\arccos(1/r_c)-2\sqrt{r_c^2-1}\bigr)=22.7826$. $\square$

*Corollary 3.1.* The first claim is the contrapositive. Chord points have infinite orbits at $r_c$ (Theorem A), so $\mathcal C\subseteq\bar K(r_c)$. If $K(r_c)$ were a finite union of arcs, it would be closed and would meet the segment $\mathcal C$ in finitely many points, since an arc of a circle meets a segment in at most two points. Every other chord point would then have a finite orbit. $\square$

### 3.5 Theorem 4

$A(y+l)=A(y)+\zeta^{-1}l$ and $\zeta^{-1}L=L$, so $\Gamma$ acts on $\Lambda/L$, and every $GG_5(r)$-orbit lies in one $\Gamma$-orbit, hence in one $\Gamma$-class modulo $L$. The lattice points of $\mathbb RE$ are $\mathbb Z[\varphi]E$. Indeed $E=\zeta(1-\zeta)$, and a real $t$ with $t(1-\zeta)\in\Lambda$ has even $(1-\zeta)$-adic valuation $\ge-1$, hence $\ge0$. $\Lambda/L\cong\Lambda/2\Lambda\times\Lambda/(1-\zeta)$ has exponent $10$, so the residues of $\mathbb Z[\varphi]E$ and its conjugate are those of $aE+b\varphi E$ (and conjugates) with $0\le a,b<10$. The enumeration of these residues and of the $\Gamma$-classes is an exact finite computation (§4.4): 7 chord residues, in the classes of $0$ and $E$. A residue $z$ fixed by $\Gamma$ satisfies $(\zeta^{-1}-1)(z+1)\in L$, i.e. $z\equiv-1\equiv1\pmod 2$. $\square$

### 3.6 Theorem 5 and Corollary 5.1

$r_0$ is a non-norm radius, so Corollary 2.3 of `sharp-lower-bound-n5.md` holds at $r_0$: no point of $\mathbb Q(\zeta)$ lies on a circle of radius $r_0$ about a point of $\mathbb Q(\zeta)$, no two such circles are tangent, and no three meet. That corollary, Lemma 3.0 and Theorem 3.1 there are stated for $r_0^2\in\mathbb Q(\varphi)$. Their proofs use only Corollary 2.3, which holds verbatim when $r_0^2\notin\mathbb Q(\varphi)$, because $|z-c|^2$, $|c-c'|^2/4$ and circumradii squared of points of $\mathbb Q(\zeta)$ lie in $\mathbb Q(\varphi)$. Hence the finite group gives a finite cut set $K(r_0)$ satisfying (C1)–(C4).

The interval-of-validity argument of `relative-certificates.md` §8 (refereed correct) then applies to its symbolic arc set. As $\rho=r^2$ increases from $\rho_0$, the checker's decisions change only at a disk event (a circle becoming tangent to $\partial D_p$) or a triple event (two named points on one circle coinciding). There are finitely many candidate values, and none equals $\rho_0$: a disk event at $\rho_0$ would be a tangency and a triple event a triple point, both excluded at $\rho_0$. So there is $\rho_1>\rho_0$ such that the same arcs satisfy (C1)–(C4) for every $\rho\in[\rho_0,\rho_1)$. The certificate theorem (`critical-radius-n5.md` Theorem 4.2) gives finiteness there, and group monotonicity gives it below $\rho_0$. $\square$

*Corollary 5.1.* $\mathcal I$ is an up-set (`boundary-contact.md` Theorem 3.4). If $r_{\rm crit}\notin\mathcal I$, then $GG_5(r_{\rm crit})$ is finite. If $r_{\rm crit}$ were a non-norm radius, Theorem 5 would give finiteness slightly above $r_{\rm crit}$, a contradiction. $\square$

### 3.7 Lemma 6 and Proposition 6.1

*Lemma 6.* Delete the trivial steps of an $r$-chain; what remains is a strict chain of depth at least $r$ (`sharp-lower-bound-combined.md` Lemma 3.3). Conversely, a strict chain of depth at least $r$ is an $r$-chain by `boundary-contact.md` Lemma 2.1. Bounded orbits are equivalent to finiteness (`boundary-contact.md` Proposition 3.3). $\square$

*Proposition 6.1.*
1. This is Lemma 6.
2. Corollary 4.4 of `sharp-lower-bound-limit-system.md` is `sharp-lower-bound-combined.md` Corollary 4.3 for the certified four-window set. The statements there bound $|O_r(x)|$ by the supremum over all orbits, but their proof gives the per-orbit bound $|O_r(x)|\le\beta\max(1,|O_r(x)\cap W^{\rm t}|)$, which is what is used here. The same holds for the row $(5,-1,4,0)$, also certified there, whose windows have circumradius $0.1815$.
3. The first part is the finiteness criterion. Bounded internal coordinates give finitely many lattice points in the bounded region $D_1\cup D_2$. For the second part: at a non-norm radius no point of $O_r(x)\subset\Lambda$ lies on a boundary circle (Corollary 2.3 there), so case (A) of `boundary-contact.md` Theorem 5.1 holds. The limit point $y^\ast$ is not in $\mathbb Q(\zeta)$, since a point of $\mathbb Q(\zeta)$ cannot lie on $\partial D_p(r)$. $\square$

---

## 4. Computations

All computations are exact: elements of $\Lambda$ are integer 4-vectors, and squared distances are elements $a+b\varphi$ of $\mathbb Z[\varphi]$ compared by integer sign tests. The engine commands use only the exploratory subcommand `orbit` of `tdcsg-orbit` (`../engine.md`). The point lists from `--format lines --conj-points` were post-processed by short scripts that are not part of the repository. What they compute is described precisely enough to redo.

### 4.1 Chord words: tight tests, domains, counts (exact)

Table 2.1 and the derivatives $f'(0)$, slacks and $L^2$ of §3.2 were computed by applying each letter of $w_i$ to both segment ends with exact arithmetic. The following values hold exactly: $|E+1|^2=3+\varphi$; $|E-1|^2=5-3\varphi$; and $|\varphi^2E-1|^2=3+\varphi$, so $\pm\varphi^2E$ are critical points, on $\partial D_2$ and $\partial D_1$ respectively.

**Chord points in $O_r(0)$** (forward and backward chains of chord words from $0$, every disk test exact). The forward counts equal those predicted by the hole formula of Theorem 2 (evaluated with 40-digit arithmetic) in every row.

| $\delta$ | forward steps | backward steps | chord points | bound $0.97/\delta-3$ | $\delta\times$ chord points |
|---|---|---|---|---|---|
| $1/10$ | 6 | 6 | 13 | 6.7 | 1.30 |
| $\varepsilon/10$ (level 1) | 27 | 27 | 55 | 38.1 | 1.30 |
| $1/55$ | 27 | 27 | 55 | 50.4 | 1.00 |
| $\varepsilon^2/10$ (level 2) | 116 | 116 | 233 | 171.1 | 1.30 |
| $\varepsilon^3/10$ (level 3) | 493 | 493 | 987 | 734.3 | 1.30 |
| $1/1000$ | 1292 | 1292 | 2585 | 967 | 2.59 |
| $1/10000$ | 5472 | 5472 | 10945 | 9697 | 1.09 |

At the levels $k=0,\dots,3$ the counts are the Fibonacci numbers $13,55,233,987=F_{3k+7}$, so the forward exit index is $(F_{3k+7}-1)/2$, the upper bound of Theorem 6(4) of `sharp-bound-n5-conjugate.md`, attained. For comparison, the full orbits have $1\,433$, $30\,165$, $400\,519$ and $5\,673\,561$ points (`sharp-lower-bound-n5.md` §7, reproduced by the engine). The chord carries a vanishing fraction of the orbit.

### 4.2 Lattice orbits at $r_c$ (exact; capped runs claim nothing)

For every lattice point with coefficients in $[-2,2]$ lying in $D_1\cup D_2$ at $r_c$, the orbit was computed with `tdcsg-orbit orbit -n 5 --r2 closed --start pow:c0,c1,c2,c3 --cap 200000 --format lines --conj-points`. A point was skipped when it, or its image under $z\mapsto-z,\bar z,-\bar z$, had appeared in an earlier orbit. "Chord" counts orbit points of $\mathcal C\cup\bar{\mathcal C}$, tested as $y\bar E$ (resp. $yE$) real with $|y|\le|E|$. "Boundary" is the engine's count of orbit points lying exactly on a boundary circle.

| representative | orbit at $r_c$ | chord points | boundary | $\max|\sigma|$ |
|---|---|---|---|---|
| $(-1,0,0,0)$ | 5 | 0 | 0 | 2.9 |
| $(-1,-2,0,-2)$ | 8 | 0 | 0 | 4.1 |
| $(-2,2,-1,-1)$ | 25 | 0 | 0 | 9.7 |
| $(-1,-2,-2,-2)$ | 31 | 0 | 0 | 9.3 |
| seven classes | 40 each | 0 | 0 | 6.7–13.2 |
| $(-2,-1,-2,-2)$ | 643 | 0 | 10 | 35.9 |
| $(-2,-2,0,-2)$ | 645 | 0 | 0 | 41.0 |
| $(-2,1,-1,-2)$ | 8 170 | 0 | 0 | 150.2 |
| $(-2,-2,-2,-2)$ | 8 376 | 0 | 0 | 170.8 |
| $(-2,-1,-1,-1)$ (class of $0$) | cap | 695 | 0 | 741.3 |
| $(-2,-1,-2,0)$ (class of $E$) | cap | 872 | 20 | 924.3 |
| $(-2,-2,-1,-2)$ (chord-free) | cap | 0 | 0 | 817.0 |
| $(-2,-2,-1,-1)$ (chord-free; contains $-\zeta^2$ up to symmetry) | cap | 0 | 0 | 886.1 |

The four capped runs are four distinct orbits up to symmetry, although none was completed: their starting points lie in four $\Gamma$-classes no two of which are exchanged by $z\mapsto-z,\bar z,-\bar z$ (these maps normalize $\Gamma$ and the groups $GG_5(r)$). The two chord-free orbits are in chord-free $\Gamma$-classes, so Theorem 4 proves they never meet $\mathbb RE\cup\mathbb R\bar E$ at any radius. With `--cap 30000000` both $(-2,-2,-1,-2)$ and $-\zeta^2=$ `pow:0,0,-1,0` still reach the cap at $r_c$ (internal maxima $1.370\cdot10^4$ and $1.470\cdot10^4$, boundary count 0). For comparison, the orbit of $0$ reaches $1.52\cdot10^4$ at $5\cdot10^7$ points (`../engine.md`). Their boundary counts are 0, so these orbits are also strict orbits as far as computed. Whether they are infinite is not decided.

### 4.3 Chord-parallel lines (exact keys)

For each orbit point $y$, the key $\kappa(y)$ (D9) was computed exactly, and points were grouped by key. The innermost populated lines have keys $\pm(F_m,2F_m,-F_{m-1},F_{m+2})$, with Fibonacci numbers $F_m$, or the same with Lucas numbers $L_m$. Their offsets are exactly $\pm\tfrac12\varphi^{-m}$, resp. $\pm\tfrac{\sqrt5}2\varphi^{-m}$, with signs alternating with $m$ (checked numerically from the exact keys, e.g. $\tfrac12\varphi^{-9}=0.0065778$). In the table, a line is listed if it carries at least 300 orbit points (runs at $r_c$), at least 2 points (levels 0–2), or at least 20 points (level 3). Populated lines with keys that are not of this form also occur between the listed ones (for example, in $O_{r_c}(0)$ at offsets $1.64\cdot10^{-3}$ and $1.83\cdot10^{-3}$); the table lists the unit-offset lines nearest to the chord:

| orbit (start, radius, points) | innermost lines: $m$ (points on the line) |
|---|---|
| $0$ at $r_c$, cap $4\cdot10^6$ | the line $\mathbb RE$ (4 541); Lucas $m=16$ (1 559, 1 563 on the two sides), $15$ (3 611 each), $13$ (1 481 each), $12$ (3 639, 3 641) |
| $-\zeta^2$ at $r_c$, cap $4\cdot10^6$ | Fibonacci $m=17$ (3 868), $15$ (4 624), $13$ (2 458), $11$ (2 661) |
| $(-2,-2,-1,-2)$ at $r_c$, cap $4\cdot10^6$ | Fibonacci $m=18$ (4 621), $16$ (3 011), $14$ (3 884), $12$ (2 962) |
| $-\zeta^2$, level 0 (1 724, finite) | $m=9$ (55) |
| $-\zeta^2$, level 1 (62 095, finite) | $m=13$ (261), $11$ (465), $9$ (465) |
| $-\zeta^2$, level 2 (256 931, finite) | $m=15$ (987), $13$ (493), $11$ (987) |
| $-\zeta^2$, level 3 (11 123 374, finite) | $m=19$ (4 675), $17$ (8 361), $15$ (8 361) |
| $0$, level 0 (1 433) | the line $\mathbb RE$ (67); Lucas $m=7$ (12 each side) |
| $0$, level 1 (30 165) | the line $\mathbb RE$ (289); Lucas $m=10$ (116 each side), $9$ (288 each) |
| $0$, level 2 (400 519) | the line $\mathbb RE$ (1 219); Lucas $m=13$ (493 each), $12$ (1 220 each) |
| $0$, level 3 (5 673 561) | the line $\mathbb RE$ (5 169); Lucas $m=16$ (2 090 each), $15$ (5 168 each) |

At level $k$ the innermost offset $s_{\min}$ is of order $\delta_k$. For the orbit of $0$ it is exactly $\tfrac{\sqrt5}2\varphi^{-(3k+7)}=5\sqrt5\,\varphi^{-7}\,\delta_k=0.385\,\delta_k$ at $k=0,1,2,3$ (period one, $m=3k+7$). For the orbit of $-\zeta^2$, $s_{\min}/\delta_k=0.066,\ 0.041,\ 0.066,\ 0.041$ for $k=0,1,2,3$ (period two, $m=9,13,15,19$). On the line $m=15$ of the orbit of $-\zeta^2$ at $r_c$, the 4 624 points have $t=\operatorname{Re}(y/E)$ spread uniformly over $[-2.616,2.618]\approx[-\varphi^2,\varphi^2]$ (86–91 points per interval of length $0.1$). That is the full chord $[-\varphi^2E,\varphi^2E]$ of $D_1\cup D_2$ whose ends are the critical points of §4.1, not only $\mathcal C$.

Commands: `tdcsg-orbit orbit -n 5 --r2 R --start S --cap C --format lines --conj-points` with `R` = `closed` ($r_c$), `closed-1/10` (level 0), `re:41/10,4/5` (level 1), `re:7/2,9/5` (level 2), `re:61/10,-12/5` (level 3), and `S` = `0` or `pow:0,0,-1,0` or `pow:-2,-2,-1,-2`. The keys were computed from the printed coefficient vectors.

**Distance to the chord.** For $(-2,-2,-1,-2)$ at $r_c$, the least distance from an orbit point to $\mathcal C\cup\bar{\mathcal C}$ is $1.06\cdot10^{-2}$, $1.55\cdot10^{-3}$, $5.93\cdot10^{-4}$, $2.27\cdot10^{-4}$ and $8.65\cdot10^{-5}$ after $10^3,10^4,10^5,10^6$ and $4\cdot10^6$ points. All four orbits that reach the cap come within $0.0023$ of each of $\pm E,\pm\bar E$ within $10^6$ points.

### 4.4 Congruence classes (exact)

$L=2(1-\zeta)\Lambda$ was put in Hermite normal form (index 80). The $\Gamma$-classes were found by closing residues under $A^{\pm1},B^{\pm1}$ modulo $L$: 20 classes, of sizes $5$ (15 classes) and $1$ (5 classes). Under the symmetries $\pm z,\pm\bar z$ they form 12 types. The residues of $aE+b\varphi E$ and their conjugates, $0\le a,b<10$, are 7. They meet only the class of $0$ (3 residues) and that of $E$ (4 residues).

### 4.5 Coverage of the orbit of $0$ at $r_c$ (exact points, floating-point binning)

The plane was cut into square cells of side $h$, and the cells containing a point of $O_{r_c}(0)$ were counted (union of disks: 9 108, 56 896 and 227 804 cells).

| points | $h=0.05$ | $h=0.02$ | $h=0.01$ |
|---|---|---|---|
| $10^5$ | 5 272 | 25 708 | 63 140 |
| $10^6$ | 5 416 | 27 192 | 90 676 |
| $4\cdot10^6$ | 5 460 | 27 896 | 94 508 |

From $h=0.05$ to $0.02$ to $0.01$ the counts give slopes $1.78$ and $1.76$. The counts still grow with the number of points in every column, so these slopes are not estimates of a box-counting dimension of the orbit closure. The exponent is close to the growth exponent $1.7$–$1.9$ of $|O_r(0)|$ in $1/(r_c-r)$ (`../overview.md` §3).

---

## 5. Conjectures

**Conjecture K1 (accumulation on the chord).** Every infinite orbit of $GG_5(r_c)$ has $\mathcal C$ or $\bar{\mathcal C}$ in its closure. Evidence: §4.3 (offsets of populated chord-parallel lines tend to $0$ in all three large orbits tested, including two chord-free ones) and the distance data. A weak point: any orbit with unbounded internal coordinate that is spread over a region approaches every line there; what supports K1 beyond this is the line structure, not the distances.

**Conjecture K2 (cascade).** Every infinite orbit at $r_c$ contains points on chord-parallel lines of offsets $\pm c\varphi^{-m}$ for infinitely many $m$, with $c\in\{\tfrac12,\tfrac{\sqrt5}2\}$. Each such line carries a run of the chord rotation of length of order $\varphi^{m}$. By Proposition 2.3 the chord words preserve the line. The holes of the chord words on a line of offset $s$ are given exactly by Theorem 2 of `sharp-bound-n5-critical-renormalization.md`; at $r_c$ their total width is $\tfrac{31+\sqrt5}{10}|s|+O(s^2)$ (proved there, Corollary 2.1). The cascade itself is conjectural.

**K3 (cut-off below $r_c$): false as stated; corrected form.** The statement "there is $c_1>0$ such that at radius $r<r_c$ no orbit meets a chord-parallel line of offset in $(0,c_1\delta)$ in more than a bounded number of points" is false: for $\delta\le1/100$, every lattice line at offset $0<|s|\le\delta/10$ carries a lattice point whose orbit has more than $0.99/\delta$ points on that line, and such lines exist at offsets in every interval $(0,c_1\delta)$ (`sharp-bound-n5-critical-renormalization.md` Theorem 3, proved; computed earlier by the referee, report §5). The correct statement involves the internal coordinate. Every lattice point $y$ off $\mathbb RE$ has $|s(y)|\ge1/(4|\sigma y|)$ (Proposition 4 there, proved), so an orbit with internal coordinates at most $M$ meets no line at offset in $(0,1/(4M))$. **Corrected K3:** *there is $c_1>0$ such that for every $r<r_c$ and every lattice point $x$, $O_r(x)$ has no point on a chord-parallel line at offset in $(0,\,c_1\delta/(1+\delta|\sigma x|))$.* It follows from Conjecture A of `sharp-bound-n5-conjugate.md` (Corollary 4.1 there) and is consistent with §4.3: the innermost populated line has $s_{\min}/\delta_k=0.385$ for the orbit of $0$ and $\in\{0.041,0.066\}$ for the orbit of $-\zeta^2$ ($k=0,\dots,3$). The offset $0$, the line $\mathbb RE$, is populated by Corollary 2.1.

**K4 (the long chord): proved** in `sharp-bound-n5-critical-renormalization.md` Theorem 1. The segment $[-\varphi^2E,\varphi^2E]$, whose ends are critical points, carries at $r_c$ the rotation by $2\varphi$ of $\mathbb R/2\varphi^2\mathbb Z$, realized by $a^{-1}a^{-1}bb$, $aba^{-1}a^{-1}$, $bba^{-1}b^{-1}$, with $T$ as its first-return map to $\mathcal C$. The data agree with it: the uniform distribution of §4.3 over $[-\varphi^2,\varphi^2]$. More directly, the $4\,541$ points of $O_{r_c}(0)$ on $\mathbb RE$ at cap $4\cdot10^6$ have $t\in[-2.6173,2.6173]$, with $86$–$89$ points per interior interval of length $0.1$, and $2\,806$ of them lie outside $\mathcal C$ (referee report §4).

**Heuristic, not a proof.** If K2 and the corrected K3 held with a uniform bound on the number of runs per offset scale and on the excursions between runs, then orbit sizes at radius $r$ would be bounded by a sum over $m\le\log_\varphi(1/\delta)+O(1)$ of (runs at scale $m$)$\times\varphi^m$, which is finite for each $\delta>0$. That would give (B). The branching (runs per scale) is what the observed exponent $\approx1.8>1$ measures. Nothing here bounds it.

---

## 6. Why the forcing argument does not close, and the remaining gap

### 6.1 Semicontinuity and limits

- **The limit system is infinite.** Every system with $r<r_c$ is contained in the strict system at $r_c$ (Lemma 6), and that system has infinite orbits through the chord (Theorem 1). So an argument of the form "the limit is finite, hence nearby systems are finite" is not available. The limit is infinite because the chord rotation survives the opening of the disks, not because of the closed-disk convention at the tight points.
- **The infinite set is closed unless $r_{\rm crit}$ is a norm radius with a finite group, but that does not locate $r_{\rm crit}$.** Corollary 5.1 shows $\mathcal I=[r_{\rm crit},\infty)$ in all cases except a norm radius with a finite group. That is consistent with any $r_{\rm crit}\le r_c$. Closedness rules out an *accumulation* of finite radii onto an infinite one from above. It does not prevent the infinite set from starting below $r_c$.
- **"The chord words are no longer valid" is true only at the ends.** Below $r_c$ the chord words fail only on holes of width $\approx\delta/\sqrt5$ (Theorem 2). They still produce $\Theta(1/\delta)$ chord points (Corollary 2.1, §4.1). The mechanism is truncated, not absent, and the truncation alone gives finiteness only for the chord-word pseudogroup, not for the group. The group's orbits grow like $\delta^{-1.8}$, faster than the chord part.

### 6.2 Arithmetic

At a non-norm radius no lattice point lies on any lattice-centred circle. So an infinite lattice orbit at its own critical radius must accumulate from inside at a non-lattice boundary point (Proposition 6.1(3)). That is no obstruction: $\Lambda$ is dense, so every boundary point is a limit of lattice points from inside. The quantitative form, the margin bound of `sharp-lower-bound-n5.md` Lemma 6.1(1), says that a lattice point of internal size $R$ is at depth at least $1/(10(10R^2+O(R)+24+\varphi^{3k}))$ from a level-$k$ circle. That only restates that infinite orbits have unbounded internal coordinates. The congruence classes of Theorem 4 are finer arithmetic, and they show something negative for this purpose. Large orbits exist in classes that never meet the chord, so an argument that attaches infinitude to the chord's own lattice points (the classes of $0$ and $E$) cannot cover them.

### 6.3 The remaining gap

By Lemma 6, (B) is the statement: *for every $r<r_c$, depth-$r$ strict orbits of the system at $r_c$ are uniformly bounded.* By Proposition 6.1(2) the unbounded part, if any, lives in the four tight windows. That is (R-core-t) of `sharp-lower-bound-limit-system.md`, and nothing here proves it. The new information is a candidate coordinate for it. The tight windows sit at the ends of the chord, where the runs of the chord rotation on chord-parallel lines begin and end. The data (§4.3) say that the infinite orbits are cascades over the offsets $\pm c\varphi^{-m}$, and that at radius $r$ the cascade stops at offset of order $\delta$. A proof of (B) along these lines would need:
1. a description, by finitely many words, of how a run that ends near a tight point at offset $s$ continues on lines of offset $\pm\varphi^{-j}s$ for a bounded set of $j$. This would be a renormalization of the offset coordinate, which is one-dimensional, a $\mathbb Z[\varphi]$-module. At $r_c$ the candidate self-similarity is the zoom $z\mapsto E-\varphi^{-3}(z-E)$ (unit $-\varphi^{-3}$, period one), which maps offset $s$ to $-\varphi^{-3}s$. It holds as an *inclusion* of orbit relations on all computed cases within distance about $0.76$ of $E$ at small defect, fails beyond distance $0.771$ and at large defect, and fails as an equality (`sharp-bound-n5-critical-renormalization.md` §2.4, §4.3–§4.5);
2. a bound, uniform in the starting point, on the number of runs per offset scale;
3. the corrected cut-off K3 (§5), which is implied by Conjecture A of the conjugate note; the uniform K3 is false.

Items 1–3 are not proved. In §4.3 the ratio $s_{\min}/\delta_k$ is constant for the orbit of $0$ and has period two for the orbit of $-\zeta^2$. A period two also appears at the tight points (`sharp-lower-bound-limit-system.md` §5.3); whether the two are the same phenomenon is not known.

**Assessment.** (B) is not closed by this line. The forcing argument as posed is dead (§6.1, §6.2). A cascade argument (items 1–3) is a possible repair. It is not yet clear that it is easier than the renormalization at the tight points, but it puts that renormalization in a one-dimensional coordinate.

---

## Appendix. Reproduction

- Engine: `tdcsg-orbit orbit` only, with the options of §4.2–§4.3; a cap reached claims nothing.
- Chord-word computations (§4.1): apply the letters of $w_i$ to exact lattice vectors, decide $|z\mp1|^2\le r^2$ by the sign of an element of $\mathbb Q(\varphi)$, and iterate $T$ in exact coordinates $t=a+b\varphi$.
- Lines (§4.3): key $\kappa(y)=y\bar E-\overline{y\bar E}$ from the printed coefficients; offset $\operatorname{Im}(y\bar E)/|E|$.
- Congruence (§4.4): Hermite normal form of the matrix of multiplication by $2(1-\zeta)$, then closure of residues under $A^{\pm1},B^{\pm1}$.
