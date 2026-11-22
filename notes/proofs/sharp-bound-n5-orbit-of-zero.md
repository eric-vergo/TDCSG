# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$, conjugate coordinate II: every chord seed, the tube, and the orbit of $0$

Authors: Eric Vergo, Claude

**Review.** Independently refereed: [`referee-report-sharp-bound-n5-orbit-of-zero.md`](referee-report-sharp-bound-n5-orbit-of-zero.md). Verdict: Theorems 9, 10, 11 and Propositions 12, 13 correct; Theorem 9(3) and Theorem 11(1)–(2) after a range fix ($0<\delta\le\sqrt5\varphi^{-2}$; the proof does not cover larger $\delta$), and the summary after three fixes (the backward lower bound, the range of Proposition 12(2), the radius in item 4(d)); Table 6.2 completed by a missing line, one value of Table 6.1 corrected in the fourth decimal, and Conjecture E restricted to the lines whose window is a rectangle. These fixes are applied below, with two added remarks (the exceptional seeds of Theorem 9 never occur in the orbit of $0$; the critical-orbits note has the better lower-bound constant). The computations of §6 were reproduced at levels 0–4 with the engine and independent exact code. Conjectures C, D, E are consistent with the data; the report says which parts look provable. It continues [`sharp-bound-n5-conjugate.md`](sharp-bound-n5-conjugate.md) (refereed; cited below as "Part I", with its numbering: Lemma 1, Theorems 4 and 6, Proposition 5). Numbering here continues Part I's: Theorems 9–11, Propositions 12–13, Conjectures C–E.

**What is established and what is not.** Let $r_c=\sqrt{3+\varphi}$ and $\delta=r_c^2-r^2$. **(B), finiteness of $GG_5(r)$ for every $r<r_c$, is not proved here. Neither is the weaker statement that the single orbit $O_r(0)$ is finite for every $r<r_c$.** What is established:

1. **Proved: Theorem 6 of Part I holds for every lattice seed on the chord** (Theorem 9). For $s_0\in\mathbb Z[\varphi]\cap[-1,1)$ and $0<\delta\le\sqrt5\varphi^{-2}=0.854$ the chord passage of $s_0E$, forward and backward, lasts fewer than $\varphi^3/\delta=4.2361/\delta$ steps, and at least $0.05901/\delta-0.2237\,|\sigma s_0|-1.40$ steps forward (one fewer backward) unless it meets a breakpoint exactly, which can happen only within the first $0.2237\,|\sigma s_0|+1.40$ steps and only for seeds outside the congruence class of $0$ (so never for a chord point of $O_r(0)$). Its conjugate reach lies between $0.50202/\delta-1.903\,(2|\sigma s_0|+8.24)$ and $36.035/\delta+1.903\,(|\sigma s_0|+2)$. The same holds for the images under $z\mapsto-z$ and $z\mapsto\bar z$.
2. **Proved: exact chord-parallel coordinates and a tube theorem** (Theorem 10, Theorem 11). Every lattice point lies on a chord-parallel line with key $m\in\mathbb Z[\varphi]$; its physical offset from $\mathbb RE$ is $d=\tfrac\varphi2m$ and its conjugate offset from $\mathbb R\sigma(E)$ is $d'=\sigma(m)/(2\varphi)$, so $d\,d'=N(m)/4$ exactly. Hence the right shape for a neighbourhood of the chord is a box of physical width of order $\delta$ and conjugate width of order $1/\delta$: lattice points at physical distance $\le c\delta$ from the chord have conjugate distance $\ge1/(4c\delta)$ from the conjugate chord. On such a tube the chord words are translations; for $0<\delta\le0.854$, **every** chord passage, from any point $x$ of the plane with $s(x)\in[-1,1)$, ends within $2\varphi^3/\delta$ steps and changes the conjugate coordinate by less than $72.07/\delta+3.81$ (by $36.04/\delta+3.81$ on the chord itself). Combined with Lemma 5 of `sharp-bound-n5-invariant.md` (line 4, refereed) this sharpens line 4's uniform cut-off ($5.86/\delta$ steps, $58.4/\delta+9.6$ conjugate) to $\varphi^3/\delta=4.24/\delta$ steps and $36.04/\delta+13.4$. Further, the tube box $\{|d|\le c\delta,\ |d'|\le C/\delta\}$ contains a number of lattice lines bounded independently of $\delta$.
3. **Proved: reduction of the orbit-of-$0$ problem to the level radii** (Proposition 12). $O_r(0)$ is finite for every $r<r_c$ iff it is finite at every level radius $r_k$; and a bound $M_0(r_k)\le C/\delta_k$ at the levels gives $M_0(r)<\varphi^3C/\delta$ at every $r$ with $\delta\le1/10$.
4. **Computed (exact, levels $0$–$4$): the orbit of $0$ is exactly self-similar in several precise senses** (§6). (a) Near 18 of the 38 critical points (among them the four tight points), the zoomed orbit $\varepsilon^{-k}(O_{r_k}(0)-Q)$ inside the zoomed core is **period two** from level 1 on; near the other 20 it is empty from level 3 on. (b) The chord line carries an exact **model set**: $O_{r_k}(0)\cap\mathbb RE=\{sE: s\in2\mathbb Z+\mathbb Z\varphi,\ sE\in D_1\cup D_2,\ |\sigma s|\le T_k\}$ with $\delta_kT_k\to\varphi^7/10$; its size is $2F_{3k+9}-(-1)^k$. (c) The chord-parallel lines met by the orbit within distance $8\delta_k$ of the chord are, in the rescaled offset $d/\delta_k$, the same at levels 1–4. (d) $\varepsilon\cdot O_{r_k}(0)$ and $O_{r_{k+1}}(0)$ share a fixed fraction of points, and $\varepsilon y\in O_{r_{k+1}}(0)$ for every $y\in O_{r_k}(0)$ with $|y|<1.067$ ($k=0,\dots,3$).
5. **Conjectured:** exact period-two self-similarity of the orbit of $0$ near the critical points at all levels (Conjecture C), the chord-line model set at all levels (Conjecture D), and a rescaled limit object for $\{(y,\delta\sigma y)\}$ (Conjecture E). None of them, if proved, gives finiteness of $O_r(0)$ by itself; §7 says what would.

**The remaining gap.** The new results control *chord passages*, wherever they start, uniformly: bounded length $O(1/\delta)$ and bounded conjugate gain $O(1/\delta)$ per passage. They do not bound the number of passages an orbit makes, nor control the moves of an orbit that are not chord words. A bound on the number of passages per orbit, uniform in $\delta$, would give Conjecture A and (B), and for the orbit of $0$ alone its finiteness (§7).

Labels: **proved** (argument written here), **computed** (exact unless stated otherwise; method and command in §8), **conjecture**.

---

## 1. Setting

As in Part I §1. In particular $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$, $\varphi=-\zeta^2-\zeta^3$, $\sigma\colon\zeta\mapsto\zeta^2$, $E=\zeta-\zeta^2$, $|E|^2=3-\varphi$, $|\sigma E|^2=2+\varphi$, $|E|\,|\sigma E|=\sqrt5$; the chord words $w_1,w_2,w_3$, the rotation $T$ of $[-1,1)$ by $2\varphi^{-1}$ modulo $2$, the breakpoint set $B=\{-1,b_1,b_3,1\}$ with $b_1=-\varphi^{-1}=1-\varphi$, $b_3=-\varphi^{-3}=3-2\varphi$; $\kappa=2\varphi^3/\sqrt5=3.78885$; the levels $r_k^2=3+\varphi-\delta_k$, $\delta_k=\varepsilon^k/10$, $\varepsilon=\varphi^{-3}=2\varphi-3$, $\sigma(\varepsilon)=-\varphi^3$. $F_j$ are the Fibonacci numbers, $F_1=F_2=1$. $H(t)=\sigma(t)-t$ for $t\in\mathbb Q(\varphi)$.

- **Translation parts.** $w_1,w_2$ translate by $\tau E$ with $\tau=2\varphi^{-1}$, $w_3$ with $\tau=-2\varphi^{-2}$; in both cases $H(\tau)=\sigma(\tau)-\tau=-2\sqrt5$ (Part I Theorem 4(2)).
- **Pull-back centres.** For a word $w_i$ and its $m$-th letter with centre $p\in\{\pm1\}$, $c'_{im}=h^{-1}(p)$, where $h$ is the composite *global* rotation of the first $m-1$ letters. The $m$-th letter applies at the current point exactly when the starting point $x$ satisfies $|x-c'_{im}|\le r$, provided the earlier letters applied (`sharp-bound-n5-critical-orbits.md` D4 and Table 2.1, refereed; recomputed here, §8.1).
- **Chord passage.** For $x\in\mathbb C$ with $s(x)\in[-1,1)$ (defined in §2), put $x_0=x$ and $x_{k+1}=w_{i(s(x_k))}(x_k)$, where $i(s)$ is the word $T$ assigns to $s$ (Part I §1), as long as every letter's disk test passes at radius $r$. The *forward passage length* $L^+(x)$ is the least $k\ge0$ at which a test fails. The *backward passage* uses $x_{-k-1}=w_i^{-1}(x_{-k})$ with $i$ the word assigned to $T^{-1}(s(x_{-k}))$, and $L^-(x)$ is defined likewise. The points $x_{-L^-},\dots,x_{L^+}$ lie in $O_r(x)$. For a chord point $x=s_0E$ these are $t_kE$ with $t_k=T^k(s_0)$, and $L^+(s_0E)$ is the chord time $K(\delta)$ of Part I when $s_0=0$.

*The backward passage is legitimate.* If the letter $A$ moves $z\in D_1$ to $A(z)$, then $A(z)\in D_1$ and $a^{-1}$ moves $A(z)$ back, because $D_1$ is $A$-invariant; likewise for the other letters. So $w_i^{-1}$ acts at $w_i(y)$, letter by letter, exactly when $w_i$ acts at $y$.

## 2. Statements

**Theorem 9 (every chord seed).** Let $s_0\in\mathbb Z[\varphi]\cap[-1,1)$, $t_k=T^k(s_0)$ for $k\in\mathbb Z$, and $c(s_0)=|\sigma s_0|+|s_0|+1+\varphi^3$.
1. (*Exact hits.*) $t_k\in B$ for at most one $k$ per breakpoint, and only for $|k|\le c(s_0)/(2\sqrt5)$. If $s_0\notin(1+2\mathbb Z[\varphi])\cup(\varphi^2+2\mathbb Z[\varphi])$, then $t_k\notin B$ for all $k$.
2. (*Lower bound.*) Let $0<\delta\le1/20$ and let $K_0$ be the largest integer $k\ge0$ with $2\sqrt5\,k+c(s_0)\le1/(\kappa\delta)$, if one exists. Let $k^+_{\rm hit}$ ($k^-_{\rm hit}$) be the least $k\ge0$ with $t_k\in B$ ($t_{-k}\in B$), or $\infty$. Then $L^+(s_0E)\ge\min(K_0+1,\,k^+_{\rm hit})$ and $L^-(s_0E)\ge\min(K_0,\,k^-_{\rm hit}-1)$. Numerically $K_0+1>0.0590169/\delta-0.22361\,c(s_0)$.
3. (*Upper bound; $0<\delta\le\sqrt5\varphi^{-2}=0.8541$, every real $s_0\in[-1,1)$.*) $L^\pm(s_0E)<\varphi^3/\delta$. (For larger $\delta$, $L^\pm$ is at most its value at $\delta=\sqrt5\varphi^{-2}$, hence at most $4$, because the disk tests have centres independent of $r$.)
4. (*Conjugate reach.*) For $|k|\le L^\pm$, $|\sigma(t_kE)|\le|\sigma E|\bigl(|\sigma s_0|+|s_0|+1+2\sqrt5|k|\bigr)<36.0342/\delta+1.90212\,(|\sigma s_0|+2)$. If $K_0$ exists and $k^+_{\rm hit}>K_0+1$, then $\max_{0\le k\le L^+}|\sigma(t_kE)|>0.502028/\delta-1.90212\,\bigl(c(s_0)+|\sigma s_0|+|s_0|+1\bigr)$.
5. (*Symmetric images.*) $O_r(-x)=-O_r(x)$ and $O_r(\bar x)=\overline{O_r(x)}$, and $\sigma$ commutes with both maps; so 1–4 hold verbatim for seeds on $-\mathbb RE=\mathbb RE$ traversed backwards and on the mirror chord $\mathbb R\bar E$.

**[proved]** For $s_0=0$, item 2 is Theorem 6(1) of Part I ($c(0)=1+\varphi^3$). Item 3 is weaker than Theorem 6(3) for $s_0=0$ (Fibonacci exit, $\varphi^3/(2\delta)$) but needs no arithmetic of the seed. Item 2 uses the safe distance $\kappa\delta$ of Part I; the exact holes of `sharp-bound-n5-critical-orbits.md` Theorem 2 (refereed) give a leading constant about eight times larger, $0.97/\delta-3$ chord points for $s_0=0$ (Corollary 2.1 there), and the same argument with $c(s_0)$ in place of $1+\varphi^3$ applies to every seed.

The exceptional classes of item 1 are exactly the chord points outside the congruence class of $0$: modulo $K=2(1-\zeta)\Lambda$ the class of $sE$ depends only on $s$ modulo $2\mathbb Z[\varphi]$ (since $E=\zeta(1-\zeta)$), and $sE$ lies in the $\Gamma$-class of $0$ for $s\equiv0,\varphi$ and in that of $E$ for $s\equiv1,\varphi^2$ (`sharp-bound-n5-invariant.md` Proposition 2, `sharp-bound-n5-critical-orbits.md` Theorem 4; the four residues checked exactly). So no chord point of $O_r(0)$ is an exceptional seed, and item 2 applies to all of them without the hit clause.

**Theorem 10 (chord-parallel coordinates).** For $x\in\Lambda$ put $y=x/E$ and
$$s=\operatorname{Re}y,\qquad d=\frac{\operatorname{Im}(x\bar E)}{|E|},\qquad s'=\operatorname{Re}\frac{\sigma x}{\sigma E},\qquad d'=\frac{\operatorname{Im}(\sigma x\,\overline{\sigma E})}{|\sigma E|},$$
so that $x=sE+d\,\frac{iE}{|E|}$ and $\sigma x=s'\sigma E+d'\frac{i\sigma E}{|\sigma E|}$ ($d,d'$ are the signed distances of $x$ from $\mathbb RE$ and of $\sigma x$ from $\mathbb R\sigma E$). Then:
1. $2s\in\mathbb Z[\varphi]$ and $s'=\sigma(s)$.
2. The key $\kappa(x)=x\bar E-\bar xE$ equals $(\zeta-\zeta^{-1})\,m$ with $m\in\mathbb Z[\varphi]$, and $d=\tfrac\varphi2\,m$, $d'=\sigma(m)/(2\varphi)$. Hence
$$d\,d'=\tfrac14N(m),\qquad N(m)\in\mathbb Z.$$
In particular, if $x\notin\mathbb RE$ then $|d|\,|d'|\ge\tfrac14$.
3. (*Chord words in these coordinates.*) Wherever $w_i$ acts at $x$ as the composite global rotation, it maps $(s,d,s',d')$ to $(s+\tau_i,\ d,\ s'+\sigma(\tau_i),\ d')$, with $s'-s$ decreasing by exactly $2\sqrt5$.
4. (*Disk tests off the chord.*) For every letter $m$ of $w_i$ and every $x=sE+d\,iE/|E|\in\mathbb C$,
$$|x-c'_{im}|^2=|sE-c'_{im}|^2+\gamma_{im}\,d+d^2,\qquad\gamma_{im}=-2\,d(c'_{im})\in\{\pm\varphi^{-1},\ \pm(3\varphi-1)\}.$$
The values are listed in Table 2.1; the tight letters at $b_1$ are the fourth letter of $w_1$ ($\gamma=3\varphi-1$, tight from the left) and the second letter of $w_2$ ($\gamma=-(3\varphi-1)$, tight from the right).

**[proved; Table 2.1 is an exact computation]**

**Table 2.1.** Pull-back centres $c'_{im}$ and their coefficients $\gamma_{im}$ (§8.1).

| word | letters | $c'_{im}$ | $\gamma_{im}$ |
|---|---|---|---|
| $w_1$ | $a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}$ | $(-1,0,0,0)$, $(-1,0,0,0)$, $(-1,0,0,2)$, $(-1,0,-2,2)$, $(-1,2,-2,2)$ | $-\varphi^{-1},-\varphi^{-1},\varphi^{-1},3\varphi-1,\varphi^{-1}$ |
| $w_2$ | $ababb$ | $(-1,0,0,0)$, $(-1,2,0,0)$, $(-1,2,-2,0)$, $(-1,2,-2,2)$, $(-1,2,-2,2)$ | $-\varphi^{-1},-(3\varphi-1),-\varphi^{-1},\varphi^{-1},\varphi^{-1}$ |
| $w_3$ | $aba\,b^{-1}a^{-1}b^{-1}$ | $(-1,0,0,0)$, $(-1,2,0,0)$, $(-1,2,-2,0)$, $(-1,2,-2,2)$, $(-1,2,-4,2)$, $(-1,4,-4,2)$ | $-\varphi^{-1},-(3\varphi-1),-\varphi^{-1},\varphi^{-1},3\varphi-1,\varphi^{-1}$ |

**Theorem 11 (the tube).** Let $\delta>0$ and $x\in\mathbb C$ with $s=s(x)\in[-1,1)$ and $d=d(x)$.
1. (*Every passage is short.*) For $0<\delta\le\sqrt5\varphi^{-2}=0.8541$: $L^\pm(x)<2\varphi^3/\delta=8.4722/\delta$, and $L^\pm(x)<\varphi^3/\delta=4.2361/\delta$ if $d=0$. With Lemma 5 of [`sharp-bound-n5-invariant.md`](sharp-bound-n5-invariant.md) (refereed: a bad interval of length $2\delta/\sqrt5$ at every offset, for $\delta\le2/5$), $L^\pm(x)<\varphi^3/\delta$ for every $x$.
2. (*Bounded conjugate gain.*) If $x\in\mathbb Q(\zeta)$, then along the passage $|\sigma(x_k)-\sigma(x_0)|\le|\sigma E|\,(2+2\sqrt5|k|)$ exactly, and the conjugate offset $d'$ does not change. So every passage changes the conjugate coordinate by less than $72.069/\delta+3.805$, and by less than $36.035/\delta+3.805$ if $d=0$ or (with the cited Lemma 5) for every $x$ when $\delta\le2/5$. The prefix of the word that ends the passage adds at most $5|\sigma E|<9.52$.
3. (*Long passages in the tube.*) Put $\delta_{\rm eff}=\delta+(3\varphi-1)|d|+d^2$. If $\operatorname{dist}(s(x_k),B)\ge\kappa\,\delta_{\rm eff}$ then the $k$-th step of the passage acts. For $x\in\Lambda$ with $c(x)=|s'|+|s|+1+\varphi^3$: unless the passage meets a point with $s(x_k)\in B$ (possible only for $|k|\le c(x)/(2\sqrt5)$), $L^+(x)\ge K_0+1$, where $K_0$ is the largest $k\ge0$ with $2\sqrt5k+c(x)\le1/(4\kappa\delta_{\rm eff})$. For $|d|\le c\,\delta$ and $\delta\le1/20$ this is $L^+(x)>0.014754/\bigl((1+3.8542c+c^2/20)\,\delta\bigr)-0.2237\,c(x)$.
4. (*The tube box has boundedly many lattice lines.*) For $c,C>0$ let $\mathcal T_\delta(c,C)$ be the set of $x\in\Lambda$ with $s(x)\in[-1,1)$, $|d(x)|\le c\delta$ and $|d'(x)|\le C/\delta$. It lies on the chord line and on the lines with keys $m\ne0$, $|m|\le2c\delta/\varphi$, $|\sigma m|\le2\varphi C/\delta$; these satisfy $|N(m)|\le4cC$, and their number is bounded independently of $\delta$. The key set at $\varepsilon\delta$ is $\varepsilon$ times the key set at $\delta$. Off the chord line, every point of $\mathcal T_\delta(c,C)$ has $|\sigma x|\ge|d'|\ge1/(4c\delta)$.

**[proved]**

So the tube piece is this: over the physical strip of width $2c\delta$ about the chord, the lattice points with conjugate offset at most $C/\delta$ lie on a $\delta$-independent number of lines. On each line the chord words act as the rotation $T$ with holes of size of order $\delta$. Every passage on it is shorter than $2\varphi^3/\delta$ and moves the conjugate coordinate by less than $72.07/\delta+3.81$ along $\sigma E$. In the rescaled coordinates $(s,\,d/\delta;\ \delta s',\,\delta d')$ the lines are the same at every level (the key set scales by $\varepsilon$). What the theorem does not give is a region *invariant under the generators*: the tube is invariant only under the chord words, and orbits leave it through the holes (§7).

**Proposition 12 (orbit of $0$: reduction to the levels).** Let $r_k\uparrow r_c$ be any sequence (for instance the levels).
1. $O_r(0)$ is finite for every $r<r_c$ iff $O_{r_k}(0)$ is finite for every $k$; and $GG_5(r)$ is finite for every $r<r_c$ iff $GG_5(r_k)$ is.
2. If $M_0(r_k)\le C/\delta_k$ for every level $k$ (with $\delta_k=\varepsilon^k/10$), then $M_0(r)<\varphi^3C/\delta$ and $O_r(0)$ is finite for every $r$ with $\delta\le1/10$.

**[proved]** (Orbit monotonicity, `boundary-contact.md` Theorem 3.1, refereed and Lean-checked; Lemma 1 of Part I.)

**Proposition 13 (the chord part of the orbit of $0$ is a model set).** For every $\delta>0$, the points of the passage of $0$ are
$$\{t_kE:-L^-\le k\le L^+\}=\{sE:\ s\in2\mathbb Z[\varphi]\cap[-1,1),\ -2\sqrt5L^+\le H(s)\le2\sqrt5L^-\},$$
a cut-and-project set with a parallelogram window. **[proved]**

The computed statements of §6 and the conjectures are listed there, with their evidence.

---

## 3. Proofs of Theorems 9 and 10

### 3.1 Theorem 9

*Item 1.* $T$ adds $2\varphi^{-1}$ or $2\varphi^{-1}-2$, both in $2\mathbb Z[\varphi]$, so $t_k\in s_0+2\mathbb Z[\varphi]$, and $H(t_k)=H(s_0)-2\sqrt5k$ (§1, translation parts; backwards with $+2\sqrt5$). If $t_k=b\in B$ then $2\sqrt5k=H(s_0)-H(b)$, which determines $k$, and $|H(s_0)-H(b)|\le|\sigma s_0|+|s_0|+|\sigma b|+|b|\le c(s_0)$, using $|\sigma b|\le\varphi^3$ and $|b|\le1$. Modulo $2$, $\pm1\equiv1$, $b_3=3-2\varphi\equiv1$, $b_1=1-\varphi\equiv1+\varphi=\varphi^2$; so if $s_0$ is in neither class, $t_k-b\not\equiv0\pmod2$ and $t_k\ne b$.

*Item 2.* Since $2$ is inert in $\mathbb Z[\varphi]$, $\mathbb Z[\varphi]/2$ is the field with four elements and the norm of an element not divisible by $2$ is odd. So if $t_k\ne b$, $|N(t_k-b)|\ge1$ and $|t_k-b|\ge1/|\sigma(t_k-b)|$. From item 1, $\sigma(t_k)=\sigma(s_0)+(t_k-s_0)-2\sqrt5k$, so $|\sigma(t_k-b)|\le|\sigma s_0|+|s_0|+1+2\sqrt5|k|+\varphi^3=c(s_0)+2\sqrt5|k|$. For $0\le k\le K_0$ with $k<k^+_{\rm hit}$ this gives $\operatorname{dist}(t_k,B)\ge1/(c(s_0)+2\sqrt5k)\ge\kappa\delta$, and Steps 1–2 of the proof of Part I Theorem 6 (which do not involve the seed) show that the word assigned to $t_k$ acts at $t_kE$. By induction $L^+\ge\min(K_0+1,k^+_{\rm hit})$. Backwards, the step from $t_{-k}$ to $t_{-k-1}$ acts iff the word assigned to $t_{-k-1}$ acts at $t_{-k-1}E$ (§1); the same bound for $1\le k+1\le K_0$ gives $L^-\ge\min(K_0,k^-_{\rm hit}-1)$. The numerical form: maximality of $K_0$ gives $2\sqrt5(K_0+1)>1/(\kappa\delta)-c(s_0)$, and $1/(2\sqrt5\kappa)=0.05901699\ldots$, $1/(2\sqrt5)=0.2236068$.

*Item 3.* Let $d_*\in(0,\delta/\sqrt5)$, and consider $t=b_1-d_*$ (word $w_1$) and $t=b_1+d_*$ (word $w_2$), and $t=b_1$ (word $w_1$). Part I, proof of Theorem 6(3), computes the tight test: the fourth letter of $w_1$, resp. the second letter of $w_2$, has squared distance $r_c^2-\sqrt5d_*+(3-\varphi)d_*^2>r_c^2-\delta=r^2$ from its centre, and $r_c^2>r^2$ at $t=b_1$. So the word assigned to every $t$ in the open interval $J=(b_1-\delta/\sqrt5,\,b_1+\delta/\sqrt5)$ fails at radius $r$ (an earlier letter may fail first; either way the word does not act). On the circle $\mathbb R/2\mathbb Z$, rescaled to length 1, $T$ is the rotation by $\alpha=\varphi^{-1}$ and $J$ is an open arc of length $\delta/\sqrt5$.

*Three-gap lemma.* For every $j\ge3$ and every $u$, the points $u+k\alpha$, $0\le k<F_j$, cut the circle of length 1 into arcs of lengths $\varphi^{-(j-1)}$ and $\varphi^{-(j-2)}$. This is the three-distance theorem (V. T. Sós, 1958; S. Świerczkowski, 1959) for $N=q_n$: the $q_n$ points $\{k\alpha\}$, $0\le k<q_n$, cut the circle into $q_n-q_{n-1}$ gaps of length $\|q_{n-1}\alpha\|$ and $q_{n-1}$ gaps of length $\|q_{n-1}\alpha\|+\|q_n\alpha\|$. For $\alpha=\varphi^{-1}$ the denominators $q_n$ are the Fibonacci numbers and $\|F_j\alpha\|=|F_j\varphi^{-1}-F_{j-1}|=\varphi^{-j}$ (Part I, proof of Theorem 6(3)); a translate by $u$ has the same gaps. (Checked numerically to 60 digits for $4\le j\le23$, §8.)

So an open arc of length larger than $\varphi^{-(j-2)}$ contains one of $u,\dots,u+(F_j-1)\alpha$. Let $j$ be least with $\varphi^{-(j-2)}<\delta/\sqrt5$. Then $\varphi^{-(j-3)}\ge\delta/\sqrt5$, so $\varphi^j\le\sqrt5\varphi^3/\delta$ and, by Binet, $F_j\le(\varphi^j+1)/\sqrt5\le\varphi^3/\delta+1/\sqrt5$. Some $t_k$ with $0\le k\le F_j-1<\varphi^3/\delta$ lies in $J$, and the passage stops there or earlier. Backwards: $t_{-k-1}$, $0\le k<F_j$, are the points $t_{-F_j}+k'\alpha$, so one of them lies in $J$ and the backward step into it fails. The range $\delta\le\sqrt5\varphi^{-2}$ is used twice: it makes $J\subseteq(-1,b_3)$, where the assigned words are $w_1$ (left of $b_1$, and at $b_1$) and $w_2$ (right of $b_1$), as the tight tests above require; and it gives $\delta/\sqrt5\le\varphi^{-2}$, so $j\ge5$ and the three-gap lemma (which needs $j\ge3$) applies. For larger $\delta$ the passage is no longer than at $\delta=\sqrt5\varphi^{-2}$ (a test passed at radius $r$ is passed at every larger radius, and the sequence $t_k$ does not depend on $r$), where $j=5$ and $L^\pm\le F_5-1=4$. Nothing here used $s_0\in\mathbb Z[\varphi]$.

*Item 4.* The upper estimate is item 1's formula for $\sigma(t_k)$ with $|k|<\varphi^3/\delta$; the constants are $|\sigma E|\cdot2\sqrt5\varphi^3=36.03414\ldots$ and $|\sigma E|=1.902113\ldots$, with $|s_0|+1\le2$. The lower estimate: $|\sigma(t_{K_0+1})|\ge2\sqrt5(K_0+1)-|\sigma s_0|-|s_0|-1>1/(\kappa\delta)-c(s_0)-|\sigma s_0|-|s_0|-1$, times $|\sigma E|$; $|\sigma E|/\kappa=0.5020285\ldots$.

*Item 5.* $-A(-z)=\zeta^{-1}(z-1)+1=B(z)$ and $-D_1=D_2$, so $z\mapsto-z$ conjugates $a$ to $b$. $\overline{A(\bar z)}=\zeta(z+1)-1=A^{-1}(z)$ and $\overline{D_1}=D_1$, so complex conjugation conjugates $a$ to $a^{-1}$ and $b$ to $b^{-1}$. Both maps therefore carry orbits to orbits. $\sigma(-x)=-\sigma(x)$, and $\sigma$ commutes with complex conjugation (Part I §1). $\square$

### 3.2 Theorem 10

*Item 1.* Put $z=x\bar E\in\Lambda$, $z=\sum_{j=0}^3c_j\zeta^j$. Then $z+\bar z=2c_0+c_1(\zeta+\zeta^{-1})+(c_2+c_3)(\zeta^2+\zeta^{-2})\in\mathbb Z[\varphi]$. Since $\bar E=\zeta^{-1}(1-\zeta^{-1})$ is divisible by the prime $(1-\zeta)$, so are $z$, $\bar z$ and $z+\bar z$; and $(1-\zeta)\Lambda\cap\mathbb Z[\varphi]=\sqrt5\,\mathbb Z[\varphi]$ (the prime of $\mathbb Z[\varphi]$ below $(1-\zeta)$, which is totally ramified over $5$). Now $2s=2\operatorname{Re}(x\bar E)/|E|^2=(z+\bar z)/(3-\varphi)$, and $3-\varphi=\sqrt5/\varphi$, so $2s=\varphi(z+\bar z)/\sqrt5\in\mathbb Z[\varphi]$. Next, $\sigma(x/E)=\sigma(s)+\sigma(y-s)$; $y-s=(y-\bar y)/2$ is purely imaginary and $\sigma$ commutes with conjugation, so $\sigma(y-s)$ is purely imaginary and $\operatorname{Re}\sigma(y)=\sigma(s)$.

*Item 2.* $z-\bar z=\sum_jc_j(\zeta^j-\zeta^{-j})=c_1(\zeta-\zeta^{-1})+(c_2-c_3)(\zeta^2-\zeta^{-2})$, and $\zeta^2-\zeta^{-2}=(\zeta-\zeta^{-1})(\zeta+\zeta^{-1})=(\zeta-\zeta^{-1})(\varphi-1)$. So $\kappa(x)=z-\bar z=(\zeta-\zeta^{-1})m$ with $m=c_1+(c_2-c_3)(\varphi-1)\in\mathbb Z[\varphi]$. On the other hand $z-\bar z=2i\operatorname{Im}(x\bar E)=2i|E|d$ and $\zeta-\zeta^{-1}=2i\sin72^\circ=i|\sigma E|$, so $m=2|E|d/|\sigma E|$, i.e. $d=\frac{|\sigma E|}{2|E|}m=\frac{\varphi}{2}m$ (indeed $|\sigma E|^2/|E|^2=(2+\varphi)/(3-\varphi)=\varphi^2$). Apply $\sigma$: $\sigma(z-\bar z)=\sigma x\,\overline{\sigma E}-\overline{\sigma x}\,\sigma E=2i|\sigma E|d'$, and $\sigma(\zeta-\zeta^{-1})=\zeta^2-\zeta^{-2}=2i\sin144^\circ=i|E|$, so $\sigma(m)=2|\sigma E|d'/|E|=2\varphi d'$. Multiply: $dd'=\frac\varphi2m\cdot\frac{\sigma m}{2\varphi}=N(m)/4$. If $x\notin\mathbb RE$ then $d\ne0$, so $m\ne0$ and $|N(m)|\ge1$.

*Item 3.* $w_i$ acts as $x\mapsto x+\tau_iE$ (Part I §1 and `critical-radius-n5.md` Lemma 3.1); then $y\mapsto y+\tau_i$ with $\tau_i$ real, so $s\mapsto s+\tau_i$ and $d$ is unchanged; applying $\sigma$, $\sigma x\mapsto\sigma x+\sigma(\tau_i)\sigma E$ with $\sigma(\tau_i)$ real. $H(\tau_i)=-2\sqrt5$.

*Item 4.* With $n=iE/|E|$, $|x-c'|^2=|sE-c'|^2+2d\operatorname{Re}\bigl(n\,\overline{(sE-c')}\bigr)+d^2$. Here $\operatorname{Re}(n\,s\bar E)=\operatorname{Re}(is|E|)=0$ and $-2\operatorname{Re}(n\bar c')=-2\operatorname{Re}(iE\bar c')/|E|=2\operatorname{Im}(E\bar c')/|E|=-2\operatorname{Im}(c'\bar E)/|E|=-2d(c')$. The centres $c'$ are lattice points, and $-2d(c')=-\varphi m(c')$ is computed exactly from the key of $c'$ (§8.1). $\square$

## 4. Proof of Theorem 11

*Item 1.* By Theorem 10(4) and the computation in the proof of Theorem 9(3), for $x$ with $s(x)=b_1-d_*$, $0\le d_*<\delta/\sqrt5$ (word $w_1$, fourth letter), the squared distance is $r_c^2-\sqrt5d_*+(3-\varphi)d_*^2+(3\varphi-1)d+d^2$, which exceeds $r_c^2-\delta$ when $d\ge0$. For $s(x)=b_1+d_*$, $0<d_*<\delta/\sqrt5$ (word $w_2$, second letter) it is $r_c^2-\sqrt5d_*+(3-\varphi)d_*^2-(3\varphi-1)d+d^2$, which exceeds $r_c^2-\delta$ when $d\le0$. (These are the tests of the first letters that can fail; if an earlier letter fails, the word fails anyway.) Since $d$ is constant along the passage (Theorem 10(3), and the theorem's statement is about the passage only while the words act), the set of $s$ at which the passage stops contains the half-open arc $(b_1-\delta/\sqrt5,\,b_1]$ if $d\ge0$ and $(b_1,\,b_1+\delta/\sqrt5)$ if $d\le0$: an arc of length $\delta/(2\sqrt5)$ on the rescaled circle (both arcs lie in $I_1\cup I_2$, with the words $w_1$, $w_2$ assigned as used, because $\delta/\sqrt5\le\varphi^{-2}$). A half-open arc of length larger than every gap contains a point (take the last point at or before its left end; the next point is less than one gap further). With $j$ least such that $\varphi^{-(j-2)}<\delta/(2\sqrt5)$, $F_j\le2\varphi^3/\delta+1/\sqrt5$ as in the proof of Theorem 9(3), and $L^\pm<2\varphi^3/\delta$. For $d=0$ both arcs are holes and Theorem 9(3) applies.

With the cited Lemma 5 the stopping set contains an open arc of length $2\delta/\sqrt5$ at every offset, and the proof of Theorem 9(3) gives $L^\pm<\varphi^3/\delta$ verbatim. (Theorem 7 of the cited note proves $L\le5.86/\delta$ from the same lemma with a weaker gap estimate, its Lemma 6; the three-gap lemma gives the sharp gap $\varphi^{-(j-2)}$.)

*Item 2.* By Theorem 10(3), $\sigma(x_k)-\sigma(x_0)=(s'_k-s'_0)\sigma E$ and $s'_k-s'_0=(s_k-s_0)-2\sqrt5k$ with $|s_k-s_0|<2$. Use item 1; $4\sqrt5\varphi^3|\sigma E|=72.0683$, $2|\sigma E|=3.8042$. Each letter of the failing word that acts changes the translation part by $\pm(\zeta^{\mp1}-1)$-type terms of conjugate modulus $|\zeta^{\mp2}-1|=|\sigma E|$, and at most five act. (Lemma 4 of the cited note bounds the per-step gain by $2\varphi^2|\sigma E|=9.959$; the exact drift identity $H(\tau_i)=-2\sqrt5$ gives $2\sqrt5|\sigma E|=8.507$ per step plus the constant $2|\sigma E|$.)

*Item 3.* Part I, proof of Theorem 6, Step 1, gives $|sE-c'_{im}|^2\le r_c^2-(3-\varphi)(s-b)(b'-s)$ on the interval $[b,b']$ of $w_i$. With Theorem 10(4) and $|\gamma_{im}|\le3\varphi-1$, the letter passes if $(3-\varphi)(s-b)(b'-s)\ge\delta_{\rm eff}$, and Step 2 there turns this into $\operatorname{dist}(s,B)\ge\kappa\delta_{\rm eff}$. For a lattice point, $s_k-b\in\tfrac12\mathbb Z[\varphi]$ (Theorem 10(1)); if non-zero, $|N(2(s_k-b))|\ge1$, so $|s_k-b|\ge1/(4|\sigma(s_k-b)|)$, and $|\sigma(s_k-b)|\le c(x)+2\sqrt5|k|$ as in Theorem 9. Exact hits $s_k=b$ again force $2\sqrt5k=H(s_0)-H(b)$. The induction is that of Theorem 9(2). Numerically, $\delta_{\rm eff}\le(1+(3\varphi-1)c+c^2\delta)\delta$ and $1/(8\sqrt5\kappa)=0.0147542$.

*Item 4.* Theorem 10(2): $|d|\le c\delta$ and $|d'|\le C/\delta$ mean $|m|\le2c\delta/\varphi$ and $|\sigma m|\le2\varphi C/\delta$, so $|N(m)|\le4cC$. Multiplication by $\varepsilon$ maps $\Lambda$ onto $\Lambda$, multiplies $d$ by $\varepsilon$ and $d'$ by $|\sigma\varepsilon|=\varphi^3$, and maps the key $m$ to $\varepsilon m$; so the key set at $\varepsilon\delta$ is $\varepsilon$ times the key set at $\delta$, and the number of keys is a function of $\delta$ that is periodic under $\delta\mapsto\varepsilon\delta$. For $\delta\in[\varepsilon\delta_0,\delta_0]$ every key lies in the bounded box $|m|\le2c\delta_0/\varphi$, $|\sigma m|\le2\varphi^4C/\delta_0$ of the lattice $\{(m,\sigma m)\}\subset\mathbb R^2$, which contains finitely many points; so the number is bounded for all $\delta$. Each key gives one line, and the lattice points of $\mathcal T_\delta$ on it have $|\sigma x|\ge|d'|=|N(m)|/(4|d|)\ge1/(4c\delta)$. $\square$

## 5. Proofs of Propositions 12 and 13

*Proposition 12.* (1) If $r<r_c$, choose $k$ with $r\le r_k$; then $O_r(0)\subseteq O_{r_k}(0)$ (orbit monotonicity) and $GG_5(r)$ is finite if $GG_5(r_k)$ is (group monotonicity, `boundary-contact.md` Theorem 3.4). The converse directions are trivial. (2) For $r$ with $\delta_{k+1}\le\delta<\delta_k$ we have $r\le r_{k+1}$, so $M_0(r)\le M_0(r_{k+1})\le C/\delta_{k+1}=C\varphi^3/\delta_k<C\varphi^3/\delta$. A finite conjugate bound on a set of lattice points in the bounded region $D_1\cup D_2$ makes it finite. $\square$

*Proposition 13.* $T^k(0)=2k\varphi^{-1}-2m_k$ (Part I (1.1)). Every $s=2(a+b\varphi)\in[-1,1)$ equals $T^b(0)$: $2b\varphi^{-1}=2b\varphi-2b$, so $s-T^b(0)\in2\mathbb Z$, and both lie in $[-1,1)$. So $k\mapsto T^k(0)$ is a bijection $\mathbb Z\to2\mathbb Z[\varphi]\cap[-1,1)$, and $H(T^k(0))=-2\sqrt5k$. $\square$

---


## 6. Computations: the orbit of $0$ across levels

All orbits are exact breadth-first searches of `tdcsg-orbit orbit` at the level radii $r_k$, $k=0,\dots,4$; every membership and coordinate statement below is a comparison of exact coefficient vectors in $\Lambda$ (or exact elements of $\tfrac12\mathbb Z[\varphi]$), unless marked "double precision". Moduli and offsets printed as decimals are double-precision evaluations of exact points, used only for reading. Method and commands: §8.

**Table 6.1.** The orbit of $0$ at the levels.

| $k$ | $|O_{r_k}(0)|$ | ratio | $M_0$ | $\delta_kM_0$ | on $\mathbb RE$ | $2F_{3k+9}-(-1)^k$ |
|---|---|---|---|---|---|---|
| 0 | 1 433 | — | 53.746 | 5.3746 | 67 | 67 |
| 1 | 30 165 | 21.05 | 273.21 | 6.4496 | 289 | 289 |
| 2 | 400 519 | 13.28 | 1 165.00 | 6.4923 | 1 219 | 1 219 |
| 3 | 5 673 561 | 14.17 | 4 933.19 | 6.4899 | 5 169 | 5 169 |
| 4 | 76 031 321 | 13.40 | 20 905.0 | 6.4923 | 21 891 | 21 891 |

(Levels 0–3 agree with Part I Table 4.1. Level 4 is new: 1.1 GB of point store, 3.3 GB resident.) Sizes grow by about $189$ per two levels against $\varphi^{12}=322$ for all lattice points of the scaled window, so the orbit is a vanishing fraction of the window; $\log189/\log\varphi^{6}=1.82$ is consistent with the box-counting dimension $\approx1.8$ of `sharp-bound-n5-critical-orbits.md` §4. $\delta_kM_0$ is $6.4923$ at both even levels and $6.4496,\,6.4899$ at the odd ones.

### 6.1 Period two at the critical points (computed, exact)

For a critical point $Q$ and a level $k$ let $S_k(Q)=\{\eta\in\Lambda:\ |\eta|\le\tfrac3{10},\ Q+\varepsilon^k\eta\in O_{r_k}(0)\}$ (the zoomed orbit inside the zoomed core of `sharp-lower-bound-limit-system.md`; $\varepsilon$ is a unit, so $\eta\in\Lambda$).
1. At 18 of the 38 critical points (the four tight points $\pm E,\pm\bar E$, the two lens corners $\pm(1,2,1,1)$ and the twelve points of the class of $(-3,-1,-1,0)$), $S_1(Q)=S_3(Q)$ and $S_2(Q)=S_4(Q)$, all non-empty; $|S_k(Q)|=26,47,47,47,47$ at the tight points ($S_1\ne S_2$ there: they share 34 points), $7,35,19,35,19$ at the lens corners, $7,25,17,25,17$ at the twelve.
2. At the other 20, the zoomed core empties: $|S_k|=14,1,0,0,0$ at 16 of them and $28,11,2,0,0$ at four.
3. $S_0(Q)\subseteq S_2(Q)$ at the 18 points.

At larger zoom radius the sets grow from level to level instead of repeating. Put $T_k(Q,\rho)=\{\eta:|\eta|\le\rho,\ Q+\varepsilon^k\eta\in O_{r_k}(0)\}$. At $Q=E$: $T_1\subseteq T_3$ and $T_2\subseteq T_4$ for every $\rho\le4$ (and $T_2\subseteq T_4$ up to $\rho=6$), with equality only at $\rho=0.3$; for example $|T_2|,|T_4|=124,126$ at $\rho=\tfrac12$ and $4731,5344$ at $\rho=4$. At $Q=0$, period one: $T_2(0,\rho)\subseteq T_3(0,\rho)\subseteq T_4(0,\rho)$ for every $\rho\le6$, equal at $\rho=0.3$ ($53$ points).

### 6.2 The chord line is a model set (computed, exact)

At every level $k=0,\dots,4$,
$$O_{r_k}(0)\cap\mathbb RE=\{sE:\ s=a+b\varphi,\ a\in2\mathbb Z,\ b\in\mathbb Z,\ sE\in D_1(r_k)\cup D_2(r_k),\ |\sigma(s)|\le T_k\}$$
for a threshold $T_k$, with no exception (the condition $a\in2\mathbb Z$ is the congruence class of $0$, see the remark after Theorem 9; points with $a$ odd lie in the class of $E$ and are in no orbit of $0$): every point of the lattice $2\mathbb Z+\mathbb Z\varphi$ (index 2 in $\mathbb Z[\varphi]$) with $s$ in the physical window and $|\sigma s|\le\max_{O}|\sigma s|$ is in the orbit, and no other point of the line is. The physical window is the full intersection of the line with $D_1\cup D_2$; its end $s_{\rm lim}(r)$ solves $(3-\varphi)s^2-\sqrt5s+1=r^2$ and tends to $\varphi^2$. The bracket for the conjugate threshold:

| $k$ | $\delta_k\max_{\rm in}|\sigma s|$ | $\delta_k\min_{\rm out}|\sigma s|$ |
|---|---|---|
| 1 | 2.89443 | 2.92705 |
| 2 | 2.89787 | 2.90557 |
| 3 | 2.90294 | 2.90476 |
| 4 | 2.90313 | 2.90356 |

Each bracket contains $\varphi^7/10=2.903444$, which is $2\sqrt5\lim\delta_kK(\delta_k)$: the conjugate window is exactly as wide as the conjugate reach of the Fibonacci chord passage (Part I Observation 1). The chord passage itself (Proposition 13) supplies only the sublattice $2\mathbb Z[\varphi]$ on $[-1,1)$, $F_{3k+7}$ points; the other points of the window ($2F_{3k+9}-(-1)^k$ in all) are reached by other routes.

### 6.3 Chord-parallel lines near the chord (computed, exact keys)

The lines (Theorem 10) met by $O_{r_k}(0)$ within physical distance $8\delta_k$ of $\mathbb RE$ are, in the rescaled offset $d/\delta_k$, **the same 24 pairs $\pm d$ at levels 1, 2, 3 and 4** ($\pm0.3851,\pm0.6231,\pm1.2461,\dots,\pm7.9180$; level 0 lacks four of them). The key norms $|N(m)|$ are $5,5,20,25,5,20,55,5,55,\dots$; the sign of $N(m)$, hence of $\delta d'$, alternates with the level, as it must if line $m$ at level $k$ corresponds to line $\varepsilon m$ at level $k+1$ ($N(\varepsilon)=-1$). The counts per line grow by $\varphi^3$ to within $10^{-3}$ and are often exact Fibonacci expressions: the line at $0.3851\,\delta_k$ carries $(F_{3k+10}-1)/2=116,493,2090,8855$ points and the line at $0.6231\,\delta_k$ carries $2F_{3k+9}=288,1220,5168,21892$, for $k=1,\dots,4$.

**Table 6.2.** The first lines at levels 3 and 4 in rescaled coordinates (the conjugate offset $\delta d'=\delta N(m)/(4d)$ is level-independent up to sign).

| $d/\delta$ | $|N(m)|$ | $|\delta d'|$ | range of $\delta s'$, level 3 | level 4 | points, level 3 | level 4 |
|---|---|---|---|---|---|---|
| 0.3851 | 5 | 3.2461 | $\pm2.347$ | $\pm2.349$ | 2 090 | 8 855 |
| 0.6231 | 5 | 2.0062 | $\pm3.244$ | $\pm3.246$ | 5 168 | 21 892 |
| 1.2461 | 20 | 4.0125 | $\pm2.217$ | $\pm2.218$ | 2 961 | 12 541 |
| 1.3932 | 25 | 4.4861 | $\pm1.450$ | $\pm1.451$ | 987 | 4 180 |
| 1.6312 | 5 | 0.7663 | $\pm1.663$ | $\pm1.663$ | 1 481 | 6 271 |
| 2.0163 | 20 | 2.4798 | $\pm2.218$ | $\pm2.218$ | 2 962 | 12 542 |
| 2.4013 | 55 | 5.7260 | $\pm0.553$ | $\pm0.554$ | 493 | 2 090 |
| 2.6393 | 5 | 0.4736 | $\pm2.984$ | $\pm2.984$ | 4 704 | 19 916 |

On some lines the points fill the box of their lattice coset exactly (at level 2: the lines at $0.3851,1.6312,2.4013,2.8773,6.1397$, and the chord line); on others they do not, so the window there is not a rectangle in these coordinates.

### 6.4 Scaled copies of the whole orbit (computed, exact)

The map $y\mapsto\varepsilon y$ carries $67.90\%$, $67.85\%$, $67.97\%$ of $O_{r_k}(0)$ into $O_{r_{k+1}}(0)$ for $k=0,1,2$, and $68.00\%$ for $k=3$; it carries every $y$ with $|y|<1.193,\ 1.113,\ 1.074,\ 1.068$ (respectively). For $\varepsilon^2$ and $k\to k+2$ the fractions are $77.4\%$, $77.5\%$ and $77.9\%$. From level 1 to level 2, voting over a sample of 60 points found 875 maps $y\mapsto\zeta^j\varepsilon y+t$ ($t\in\Lambda$) each carrying at least half of the sample into $O_{r_2}(0)$; the best carries $20\,898$ of the $30\,165$ points of $O_{r_1}(0)$ (for example $t=2\sqrt5\,\varepsilon=1.0557$, $j=0$), and together their images cover $97.4\%$ of $O_{r_2}(0)$, each point on average about 30 times. So $O_{r_{k+1}}(0)$ is locally a union of $\varepsilon$-scaled pieces of $O_{r_k}(0)$, but no single map, and no small family, gives an exact recursion $O_{r_{k+1}}(0)=F(O_{r_k}(0))$: the overlaps are large and each copy is only about $68\%$ faithful.

### 6.5 Conjectures

**Conjecture C (period two at the critical points).** For every $k\ge1$, $S_{k+2}(Q)=S_k(Q)$ at the 18 critical points of §6.1(1), and $S_k(Q)=\varnothing$ for $k\ge3$ at the other 20. Evidence: $k=1,2$ (§6.1). It is the orbit-of-$0$ case of the period-two renormalization of `sharp-lower-bound-limit-system.md` Conjecture 5.1, restricted to the cores; `sharp-bound-n5-period-two.md` shows that period two fails for general first-return sets, so the orbit of $0$ is special here. **[conjecture]**

**Conjecture D (the chord line is a model set).** For every $k$, $O_{r_k}(0)\cap\mathbb RE$ is the model set of §6.2 with $\delta_kT_k\to\varphi^7/10$, and its size is $2F_{3k+9}-(-1)^k$. **[conjecture]**

**Conjecture E (rescaled limit).** Along even levels and along odd levels separately, the sets $Y_k=\{(y,\delta_k\sigma(y)):y\in O_{r_k}(0)\}\subset\mathbb C\times\mathbb C$ converge in the Hausdorff metric, to compact sets $Y_{\rm even}$, $Y_{\rm odd}$. Near the chord the two are exchanged by $(z,u)\mapsto(z,u')$, $u'$ the reflection of $u$ in the line $\mathbb R\sigma(E)$ (the sign alternation of $\delta d'$ in §6.3); whether this holds globally is not tested. The fibre of each limit over a point $sE$ of the chord contains the union of the segments $\{(\tau\,\sigma E+v_i\,i\sigma E/|\sigma E|):|\tau|\le w_i\}$ over the lines of §6.3 whose points fill a rectangle of their coset (§6.3, last paragraph; $v_i=\delta d'$, $w_i$ the half-width of the $\delta s'$-range), and the segment of the chord line itself, $|\tau|\le\varphi^7/10$, $v=0$. On the other lines the window is not a rectangle, and the fibre over $sE$ contains only the limits of the values $\delta s'$ of the points near $s$, a subset of the segment. The limit has internal radius $\max|u|\approx6.49$ (Table 6.1: $6.4923$ at levels 2 and 4; $6.4496$, $6.4899$ at levels 1 and 3, not yet stable). Evidence: Table 6.2, the stable maxima, and §6.1. **[conjecture]**

Over the chord the conjectured limit is thus a union of segments in the conjugate fibre, one per chord-parallel line, at heights $N(m)/(4\,d/\delta)$. This is the fibred region asked for in Part I §5.3, near the chord; away from the chord the limit is not described here (dimension about $1.8$ in the scaled window, §6 opening).

## 7. What would close the gap, and an assessment

**For the orbit of $0$.** By Proposition 12 it suffices to show $O_{r_k}(0)$ finite for every $k$, and a bound $M_0(r_k)\le C/\delta_k$ gives Conjecture A for this orbit. Theorem 11 bounds the length and the conjugate gain of every chord passage. The orbit is made of chord passages and connecting moves; if one could show that every point of $O_{r_k}(0)$ is reached from $0$ by a chain containing at most $P$ chord passages (or segments of them, of any of the four symmetric classes, to which Theorem 11 transfers by the symmetries of Theorem 9(5)) and at most $Q$ other letters, with $P,Q$ independent of $k$, then $M_0(r_k)\le P(36.04/\delta_k+13.4)+1.91\,Q$ (with $72.07$ in place of $36.04$ if the cited Lemma 5 is not used). That bound on the number of passages is exactly Conjecture B$^\ast$ of `sharp-bound-n5-invariant.md` for this orbit. The computations of §6 point to a renormalization proof of it: the orbit is period-two self-similar at the cores (Conjecture C), on the chord line (Conjecture D) and on the chord-parallel lines (§6.3). What is missing is a proved correspondence between the moves at level $k$ and at level $k+2$; the period-two note shows that such a correspondence cannot be a conjugacy of chains, so it has to be stated for return relations.

**For (B).** The same, for every orbit; Theorem 11 is uniform over the plane, and Theorem 9 over chord seeds, so the passage part of any such argument is done.

**Assessment.** Tasks 1 and 2 of this line are closed: Theorem 9 and Theorem 11 are complete proofs with explicit constants. Task 3 (a proof that $O_r(0)$ is finite) is **not** closed; it is **repairable in principle**: the reduction to the levels is proved, the passage bounds are proved, and the self-similarity is exact in the data at levels 1–4, but the step from data to a proof is the same renormalization step that stops lines 3 and 4. Task 4 gives a precise conjectured limit near the chord (Conjecture E).

## 8. Reproduction

Engine: `tdcsg-orbit` built from this repository, copied to a scratch folder; only the exploratory `orbit` subcommand is used. Levels: `re:39/10,1`, `re:41/10,4/5`, `re:7/2,9/5`, `re:61/10,-12/5`, `re:-49/10,77/5` for $k=0,\dots,4$ ($r^2=3+\varphi-\varepsilon^k/10$; the `re:` basis is $1,\varphi-1$).

```sh
B=tdcsg-orbit
$B orbit -n 5 --r2 re:61/10,-12/5 --cap 30000000 --format lines --conj-points   # level 3, all points
$B orbit -n 5 --r2 re:-49/10,77/5 --cap 200000000 --format lines --conj-points  # level 4 (stream-filter it)
```

Level 4 takes about 25 minutes, most of it printing; the point records were filtered on the fly, keeping the points within $0.0187$ of a critical point or of $0$, and within $0.00249$ of $\mathbb RE$ (approximate coordinates, fields 5–6, used only to select; every selected point was then treated exactly). Size and $M_0$ are the `result` and `conj 2` records.

The scratch scripts are not part of the repository. What they do:

- **§8.1 Table 2.1.** Apply the inverse prefixes of each $w_i$ to its letter's centre $\pm1$ (exact, in $\Lambda$); $\gamma=-2d(c')=-\varphi m(c')$ with $m$ from the key $c'\bar E-\bar c'E=(\zeta-\zeta^{-1})m$. Theorem 10(1)–(2) were also checked numerically on all $13^4$ lattice points with coefficients in $[-6,6]$: $2s\in\mathbb Z[\varphi]$ and $4dd'\in\mathbb Z$ with minimum $1$ off the chord.
- **Passage simulation (exact).** Letters applied in $\Lambda$, disk tests as signs of $a+b\varphi$ decided by integers ($a+b\varphi\ge0$ iff $u+v\sqrt5\ge0$ with $u=2a+b$, $v=b$, by the signs of $u$, $v$ and $u^2-5v^2$); $s=(x\bar E+\bar xE)(2+\varphi)/10$ exact; the word chosen by $T$ from exact comparisons with $B$. It reproduces $K(\delta_k)=6,27,116,493,2090$ for $k=0,\dots,4$, forward and backward. On the 62 chord seeds $s_0=a+b\varphi\in[-1,1)$, $|b|\le15$, at $\delta=\varepsilon/10,1/80,\varepsilon^2/10,1/320,\varepsilon^3/10$: $\max\delta L^\pm\in[0.975,1.050]$ (bound $4.236$), mean $\delta L^+\approx0.59$, and the lower bound of Theorem 9(2) holds on every seed outside the two exceptional classes; seeds in those classes can stop at once (for example $s_0=b_1$). For 60 orbit points at each of levels 2 and 3 with $0<|d|\le\delta$: $\max\delta L^\pm\le1.29$ (bound $8.47$).
- **Three-gap check.** The gaps of $\{k\varphi^{-1}\}$, $0\le k<F_j$, computed with 60-digit arithmetic for $4\le j\le23$: maximum $\varphi^{-(j-2)}$, minimum $\varphi^{-(j-1)}$.
- **§6.1.** For each critical point $Q$ (all $y$ with coefficients in $[-4,4]$ and $|y\mp1|^2=3+\varphi$ exactly: 38 points), the orbit points within $\rho\varepsilon^k$ of $Q$, mapped by $\eta=\varphi^{3k}(y-Q)$ (multiplication by $2\varphi+1$, $k$ times, exactly), compared as sets of coefficient vectors.
- **§6.2.** On-line points: key $x\bar E-\bar xE=0$; $s\in\mathbb Z[\varphi]$ exact; all $a+b\varphi$ with $a$ even in the window enumerated and looked up.
- **§6.3.** Keys and $N(m)=4dd'$ from the exact points; counts per key.
- **§6.4.** Images under $y\mapsto\zeta^j\varepsilon y+t$ looked up in the sorted key array of the next level; candidate $t$ from votes $t=z-\zeta^j\varepsilon y$ over all $z\in O_{r_{k+1}}(0)$ and a random sample of $y$.
