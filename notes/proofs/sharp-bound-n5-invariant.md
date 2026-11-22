# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: conserved quantities, the chord-strip mechanism, and a uniform $1/\delta$ cut-off

Authors: Eric Vergo, Claude

**Review.** Independently refereed: [`referee-report-sharp-bound-n5-invariant.md`](referee-report-sharp-bound-n5-invariant.md). Verdict: Propositions 1, 2, Lemmas 4–6 and Theorem 7 correct (Lemma 4, Lemma 6 and Theorem 7 after minor fixes: a constant rounded down, a missing step, the domain of the run and the range $\delta>2/5$); Proposition 3 correct after a wording fix; Corollary 11 correct after restricting "Conjecture A" to $0<\delta\le\delta_0$, which is all that (B) needs. Conjecture B$^\ast$ is restated in the structural form that the evidence supports; in the form "a sum of arbitrary chord runs" it was equivalent to Conjecture A. The single-run comparison of item 4 rules out only the constant 1, not Conjecture B of line 1 with a constant. The referee's exact re-implementation reproduces Computations 2.1, 8, 9 and 10 at the radii checked, and finds the run patterns of item 4 unchanged under $\delta\mapsto\varphi^{-3}\delta$ (and $\varphi^{-6}\delta$ for $\delta=1/30$).

**What is established and what is not.** Let $r_c=\sqrt{3+\varphi}$ and $\delta=r_c^2-r^2$. **(B), finiteness of $GG_5(r)$ for every $r<r_c$, is not proved here; it remains open.** This note pursues (B) through invariants and controlled quantities, following the reshaping of the line by `sharp-bound-n5-conjugate.md` ("line 1"). What it establishes:

1. **Proved: the exact invariants are useless for (B).** Each letter conserves one element of $\mathbb Z[\varphi]$, the squared distance to its centre, in both embeddings (Proposition 1). The only congruence invariant of lattice orbits coming from the ambient group is a class in a set of 20 elements (Proposition 2), and no finer congruence invariant appears in the data (Computation 2.1). Every invariant, symmetry or reversing involution that is also present at $r_c$ is compatible with an infinite group, so it cannot by itself prove (B) (Proposition 3). Line (a) and line (c) of the brief are therefore closed in the negative.
2. **Proved: every chord-type run is cut off at scale $1/\delta$, uniformly over all starting points $sE+hN$, $s\in[-1,1)$, $h\in\mathbb R$** (Theorem 7). A *chord run* is an orbit segment along which the three critical words of Theorem A act as translations, at any perpendicular offset from the critical chord. For $0<\delta\le 2/5$ every chord run has at most $5.86/\delta$ steps, and every word map along it has internal translation at most $58.4/\delta+9.6$. The same holds for the four symmetric images of the mechanism. Line 1 proved the cut-off only for the orbit of $0$; the new ingredient is an exact identity at the breakpoint $-\varphi^{-1}$ (Lemma 5): the two tight test centres there are symmetric about the breakpoint, so a bad interval of length $2\delta/\sqrt5$ exists at every offset.
3. **Computed (exact orbits): conjugate growth comes from chord tokens.** On the shortest words realizing the largest internal translations of 107 orbits at ten radii ($\delta$ from $1/10$ down to level 2), at least $90\%$ of the letters belong to the twelve chord tokens (the three critical words and their images under $z\mapsto\bar z$, $z\mapsto-z$). These words consist of at most 8 runs; the other letters contribute at most $24.73$ to the internal translation (Computation 10). Exact orbits give $\delta M(r)\ge16.9$ to $24.7$ (Computation 9).
4. **Computed: one run is not enough.** At six of the ten radii the best single chord run accounts for the largest internal translation found, to within $1\%$ (Computation 8). At $\delta=1/30$ and $1/55$, words that chain several runs on the two chord lines $\mathbb RE$ and $\mathbb R\bar E$ exceed the best single run by factors $1.12$ and $1.45$. So a single run does not account for $M(r)$ with constant 1: a single-run form of Conjecture B of line 1 for $M(r)$ needs a constant $C'\ge1.45$ (and the data are consistent with $C'=1.5$). The data support the refined form "chord tokens alone produce the growth" (item 3).
5. **Conjectured:** Conjecture B$^\ast$, every word map is realized by a word made of boundedly many chord-run segments plus connector letters of bounded total effect. With Theorem 7 it implies Conjecture A of line 1 ($M(r)\le C/\delta$) for $0<\delta\le\delta_0$, and hence (B).

**The remaining gap.** The bound on the *number* of chord runs that a word can chain (Conjecture B$^\ast$). Runs end in the $\delta$-windows around the breakpoints, and the windows on the two chord lines are linked by single letters (for example $a(-\bar F)=-F$ exactly). Bounding the chaining is a statement about the first-return dynamics to these windows. That is the tight-window renormalization of the earlier notes in a new, one-dimensional form, and it is not solved here (§5).

Labels: **proved** (argument written here), **computed** (with the method and the reproducing command in §6; "exact" means exact arithmetic in $\mathbb Z[\zeta]$ and $\mathbb Z[\varphi]$, and "double precision" means floating point), **conjecture**. Results of other notes are cited with their labels.

---

## 1. Setting and definitions

As in `sharp-bound-n5-conjugate.md` §1. In brief:

- $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$ with basis $1,\zeta,\zeta^2,\zeta^3$, $\varphi=(1+\sqrt5)/2=-\zeta^2-\zeta^3$. $\sigma$ is $\zeta\mapsto\zeta^2$; on $\mathbb Q(\varphi)$ it is $\sqrt5\mapsto-\sqrt5$, and it commutes with complex conjugation.
- $D_1,D_2$ are the closed disks of radius $r$ about $-1,+1$. $A(z)=\zeta^{-1}(z+1)-1$ and $B(z)=\zeta^{-1}(z-1)+1$ are the global rotations. $a=A$ on $D_1$ and $a=\mathrm{id}$ elsewhere, likewise $b$. Words are read left to right, and $A,B$ written inside words mean $a^{-1},b^{-1}$.
- $\rho=r^2$, $\delta=r_c^2-\rho$. Word maps are written $\mu_w(z)=(x\mapsto\zeta^jx+t)$, and $M(r)=\sup|\sigma t|$ over all word maps at all points (line 1 §1).
- $E=\zeta-\zeta^2$, $F=\varphi^{-1}E=(1,-1,1,-1)$, $|E|^2=3-\varphi$, $|\sigma E|=\sqrt{2+\varphi}=1.902113$.
- **The critical words and the chord rotation** (`critical-radius-n5.md` §3, refereed, Lean-checked): $w_1=a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}$, $w_2=ababb$, $w_3=aba\,b^{-1}a^{-1}b^{-1}$. $I_1=[-1,-\varphi^{-1}]$, $I_2=(-\varphi^{-1},-\varphi^{-3})$, $I_3=[-\varphi^{-3},1)$, and $i(s)$ is the index with $s\in I_{i(s)}$. $T(s)=s+v_{i(s)}$ with $v_1=v_2=2\varphi^{-1}$, $v_3=-2\varphi^{-2}$ is the rotation by $2\varphi^{-1}$ of $[-1,1)$ modulo 2. $b^\ast=-\varphi^{-1}$.
- **Strip coordinates.** $N=iE/|E|$. Every $X\in\mathbb C$ is $X=sE+hN$ with $s,h\in\mathbb R$; $h$ is the signed distance from the chord line $\mathbb RE$.
- **Test centres.** If the letters of a word $w$ before its $m$-th letter act at $X$ as the global rotations, whose composite is $g_m$, then the $m$-th letter acts at $X$ as its global rotation exactly when $X\in D(P_m,r)$, where $P_m=g_m^{-1}(p_m)$ and $p_m=\mp1$ is the centre of the letter. For the critical words the test centres are, in order:

| word | test centres $P_1,\dots,P_6$ (basis $1,\zeta,\zeta^2,\zeta^3$) | composite |
|---|---|---|
| $w_1$ | $(-1,0,0,0)$, $(-1,0,0,0)$, $(-1,0,0,2)$, $(-1,0,-2,2)$, $(-1,2,-2,2)$ | translation by $2F$ |
| $w_2$ | $(-1,0,0,0)$, $(-1,2,0,0)$, $(-1,2,-2,0)$, $(-1,2,-2,2)$, $(-1,2,-2,2)$ | translation by $2F$ |
| $w_3$ | $(-1,0,0,0)$, $(-1,2,0,0)$, $(-1,2,-2,0)$, $(-1,2,-2,2)$, $(-1,2,-4,2)$, $(-1,4,-4,2)$ | translation by $(2,-4,4,-2)=-2\varphi^{-2}E$ |

- **Symmetries.** $\iota(z)=\bar z$ and $\nu(z)=-z$. The group $S=\{\mathrm{id},\iota,\nu,\iota\nu\}$ acts on words by renaming letters: $\iota$ exchanges $a\leftrightarrow a^{-1}$ and $b\leftrightarrow b^{-1}$, and $\nu$ exchanges $a\leftrightarrow b$ and $a^{-1}\leftrightarrow b^{-1}$. The **chord tokens** are the twelve words $g\cdot w_i$, $g\in S$, $i=1,2,3$. The token $g\cdot w_i$ acts at $g(X)$ as $g\circ w_i\circ g^{-1}$ (Proposition 3(1)), so the classes $\mathrm{id},\nu$ live on the line $\mathbb RE$ and the classes $\iota,\iota\nu$ on $\mathbb R\bar E$. (Inverses are included: $\nu\cdot w_3=w_3^{-1}$ and $\nu\cdot w_1=w_2^{-1}$.)
- **Chord runs.** Fix $r$ and $X_0=s_0E+hN$ with $s_0\in[-1,1)$. Put $s_k=T^k(s_0)$ and $X_k=s_kE+hN$. The *run length* $L(X_0;r)\in\{0,1,\dots,\infty\}$ is the least $k$ such that the word $w_{i(s_k)}$ fails some disk test at $X_k$ at radius $r$. A *chord run* is the orbit segment $X_0,\dots,X_L$, and its images under $S$ are chord runs of the other classes.
- **Bad set.** $\mathcal B_h(r)=\{s\in[-1,1): w_{i(s)}\text{ fails some test at }sE+hN\text{ at radius }r\}$. Then $L(X_0;r)=\min\{k:s_k\in\mathcal B_h(r)\}$.

## 2. Statements

### 2.1 Conserved quantities and invariants

**Proposition 1 (what each letter conserves).** For $y\in\Lambda$ put $\alpha(y)=|y+1|^2$ and $\beta(y)=|y-1|^2$, elements of $\mathbb Z[\varphi]$.
1. $a^{\pm1}$ conserves $\alpha$, and $b^{\pm1}$ conserves $\beta$, as elements of $\mathbb Z[\varphi]$; hence also their conjugates $\sigma\alpha=|\sigma y+1|^2$ and $\sigma\beta=|\sigma y-1|^2$.
2. $y\in D_1\iff\alpha(y)\le\rho$ and $y\in D_2\iff\beta(y)\le\rho$. The pair $(\alpha,\beta)$ determines $y$ up to complex conjugation, and $|\sigma y|^2=(\sigma\alpha+\sigma\beta)/2-1$.
3. Consequently $\bigl||\sigma(sy)|-|\sigma y|\bigr|\le2$ for every letter $s$. The orbit of $y$ has bounded conjugates if and only if the conjugates $\sigma\alpha,\sigma\beta$ of the two "squared radii" stay bounded along it.

**[proved]**

**Proposition 2 (congruence invariants of the ambient group).** Let $\Gamma=\langle A,B\rangle$ (global rotations) and $K=2(1-\zeta)\Lambda$.
1. The translations in $\Gamma$ are exactly the translations by $K$, and $\Gamma=\{x\mapsto\zeta^{-m}(x+1)-1+k:\ m\in\mathbb Z/5,\ k\in K\}$.
2. Two lattice points lie in one $\Gamma$-orbit if and only if $y'+1\equiv\zeta^m(y+1)\pmod K$ for some $m$. There are exactly $20$ such classes ($|\Lambda/K|=80$; five classes $y+1\in2\Lambda$ are fixed by $\mu_5$, and the other $75$ residues form $15$ orbits of size $5$).
3. Every orbit of $GG_5(r)$, for every $r$, lies in one $\Gamma$-orbit. Each $\Gamma$-orbit is dense in $\mathbb C$.

**[proved]**

**Computation 2.1 (no finer congruence invariant is visible).** For $m=2,\dots,8$ the orbit of $0$ at level 1 ($\rho=(33+8\varphi)/10$, 30 165 points) meets every residue class modulo $m\Lambda$ that its $\Gamma$-orbit meets: 5, 81, 80, 125, 405, 2 401, 1 280 classes. The orbit at level 0 (1 433 points) does so for $m\le5$; for larger $m$ both orbits are too small to fill the classes. **[computed, exact]**

**Proposition 3 (structure shared with $r_c$ cannot give (B)).**
1. $\iota a\iota=a^{-1}$, $\iota b\iota=b^{-1}$, $\nu a\nu=b$, at every $r$. Hence $a=(a\iota)\iota$ and $b=(b\iota)\iota$ are products of two involutions of $\mathbb C$, and the system is reversible at every $r$.
2. Any property of $GG_5(r)$ that holds at every $r\le r_c$ with the same definition, such as an invariant function on $\mathbb C$ or $\Lambda$ that does not depend on $r$, a conserved quantity of Proposition 1, the classes of Proposition 2, or the reversibility of item 1, is compatible with an infinite group. So no such property implies (B) by itself.
3. A function $F$ on $\Lambda$ that is constant on the orbits of $GG_5(r)$ for every $r$ in some interval $(r_c-\eta,r_c)$ satisfies $F(t_kE)=F(0)$ for every $k\ge0$, a set of lattice points with unbounded conjugates (line 1, Theorems 4(1) and 6(1)).

**[proved]**

### 2.2 The chord-strip mechanism

**Lemma 4 (chord tokens are exact translations).** If the word $w_i$ passes all its disk tests at $X$ at radius $r$, then $w_i(X)=X+v_iE$. So along a chord run $h$ is constant, $s_{k+1}=T(s_k)$, and the word map from $X_0$ to $X_k$ is the translation by $(s_k-s_0)E\in\mathbb Z[\varphi]E$, with conjugate $-(2k\varphi+2n_k)\,\sigma E$, where $n_k$ is the number of $w_3$-steps among the first $k$. Its modulus is at most $2\varphi^2|\sigma E|\,k<9.960\,k$. **[proved]**

**Lemma 5 (a bad interval at every offset).** Let $u=(0,1,1,-1)$, $P=(-1,0,-2,2)$ (fourth test centre of $w_1$) and $P'=(-1,2,0,0)$ (second test centre of $w_2$). Then, exactly:
1. $b^\ast E=-F$, $P+P'=-2F$ (the two centres are symmetric about the breakpoint), $-F-P=u$, and $|u|^2=3+\varphi$;
2. $2\operatorname{Re}(\bar uE)=\sqrt5$.

Consequently, for $0<\delta\le2/5$ and every $h\in\mathbb R$, the bad set $\mathcal B_h(r)$ contains an open interval $J_h$ of length $2\delta/\sqrt5$ (in the coordinate $s$). **[proved]**

**Lemma 6 (gaps of the golden rotation).** Let $\theta=\varphi^{-1}$, $m\ge2$, and $x\in\mathbb R/\mathbb Z$. The $F_m$ points $x+j\theta$, $0\le j<F_m$, cut the circle $\mathbb R/\mathbb Z$ into arcs of length at most $1/F_m+\varphi^{-m}$. ($F_m$ are the Fibonacci numbers, $F_1=F_2=1$.) **[proved]**

**Theorem 7 (uniform cut-off of chord runs).** Let $0<\delta\le2/5$, and let $m$ be the least integer $\ge2$ with $1/F_m+\varphi^{-m}<\delta/\sqrt5$. Then for every $X_0=s_0E+hN$ with $s_0\in[-1,1)$ and $h\in\mathbb R$:
1. $L(X_0;r)\le F_m-1\le5.86/\delta$;
2. every word map along the chord run from $X_0$, including the maps of the prefixes of the word that ends the run, has $|\sigma t|\le58.4/\delta+9.6$;
3. the same bounds hold for the chord runs of the classes $\iota,\nu,\iota\nu$.

In particular no chord run of any class is infinite at any $r<r_c$ (for $\delta>2/5$ by item 1 at $\delta=2/5$, since $L(X_0;r)$ is non-decreasing in $r$). **[proved]**

The theorem bounds runs in which every token is the one assigned by $T$. Tokens used elsewhere (at a point with $s\notin[-1,1)$, or not the word $w_{i(s)}$; the domains overlap) are not covered; in the computed words they are rare (Computation 10).

The theorem is uniform where line 1's Theorem 6 treats one orbit (the orbit of $0$, with $h=0$); its constant is weaker than the computed truth, which is about $2.5/\delta$ steps (Computation 8).

### 2.3 Computations

**Computation 8 (the best single run).** For each radius, the supremum over $(s_0,h)$ of the internal extent of one chord run, $\Sigma_1(\delta)\approx2\sqrt5\,|\sigma E|\sup L=8.507\sup L$, was computed with exact disk geometry in double precision. Here $\sup L$ was taken over $1\,601$ offsets $h\in[-4\delta,4\delta]$ for each radius, and for $\delta=1/55$ over $30\,001$ offsets in $[-3\delta,3\delta]$. A second computation uses the full *strip graph*: all chord tokens of one line and their inverses at every point whose test passes, not only the token chosen by $T$ (the word domains overlap; for example $w_2$ also acts on part of $I_3$). It gives the extent $\Sigma_1^{\rm g}$, maximized over $4\,000$ random starts with $s_0\in[-1,1)$ and $|h|\le\delta/2$. Columns 5–6 give, for comparison, the largest internal translation found in exact orbits (Computation 9) and the largest internal modulus of a cut-set centre (`../certificates.md`; level 2 from `sharp-lower-bound-n5.md` Table 5.2, not certified).

| $\delta$ | $\sup L$ ($h=0$) | $\sup L$ (all $h$) | $\Sigma_1$, $\Sigma_1^{\rm g}$ | $M(r)\ge$ (exact orbits) | cut-set $\max|\sigma c|$ |
|---|---|---|---|---|---|
| $1/10$ | 12 | 22 | 187.2, 194.8 | 196.74 | 188.3 |
| $3/40$ | 33 | 33 | 280.7, 285.4 | 286.14 | 309.6 |
| $1/20$ | 43 | 44 | 374.3, 373.6 | 385.16 | 363.7 |
| $1/30$ | 44 | 77 | 655.0, 662.7 | **739.75** | 738.8 |
| level 1, $\varepsilon/10$ | 99 | 99 | 842.2, 841.4 | 845.69 | 844.7 |
| $1/40$ | 55 | 99 | 842.2, 841.4 | 845.69 | 844.7 |
| $1/50$ | 99 | 99 | 842.2, 841.4 | 845.69 | 844.7 |
| $1/55$ | 99 | 99 | 842.2, 841.4 | **1223.05** | 1407.2 |
| $1/80$ | 188 | 188 | 1599.3, 1598.5 | 1624.71 | — |
| level 2, $\varepsilon^2/10$ | 420 | 420 | 3572.9, 3580.5 | 3582.41 | 3431.4 (uncertified) |

Here $\varepsilon=\varphi^{-3}$. $\delta\sup L$ lies between $1.8$ and $2.6$, and $\delta\Sigma_1$ between $15.3$ and $21.8$. **[computed, double precision]**

**Computation 9 (lower bounds for $M(r)$ from exact orbits).** For a lattice point $y_0$ the lifted search over states $(y,j)$ ($y$ an orbit point, $j$ the rotation index of a word from $y_0$ to $y$) gives the set $V=\{\zeta^{-2j}\sigma y\}$; for two states the word map between them has $|\sigma t|=|V_2-V_1|$. So $M(r)\ge\operatorname{diam}V$, and the diameter is realized by an explicit word. The searches ran from 5 429 lattice seeds with $|\sigma y|\le15$ plus 4 000 random seeds with $|\sigma y|\le25/\delta$, at each radius of the table, and from 115 000 more random seeds at $\delta=1/55$. In most orbits each point is reached with a single rotation index; orbits that contain a fixed point of a non-trivial word map are reached with all five (146 of the 65 382 orbit records), and the bound holds in both cases. The column "$M(r)\ge$" above lists the largest diameter, so $\delta M(r)\ge19.67,\ 21.46,\ 19.26,\ 24.66,\ 19.96,\ 21.14,\ 16.91,\ 22.24,\ 20.31,\ 19.96$ in the order of the table. Witness seeds: $(93,-61,97,-3)$ at $\delta=1/10$; $(470,202,166,493)$ at $1/55$; $(1818,-1259,1899,-135)$ and $(0,0,1,1)=-\varphi$ at level 2. Orbit sizes were checked against `tdcsg-orbit` (for example 111 107 and 793 605 points for the last two radii). **[computed, exact orbits; diameters evaluated in double precision over 512 directions, then recomputed exactly for the extreme pair]**

Two side results. At level 2, $M(r)\ge3582.41$ exceeds the largest internal modulus of the computed closure plus one ($3432.4$), so the internal extent of the cut-set centres can underestimate $M(r)$. At $\delta=1/55$, the closure's $1407.2$ was not reached by any sampled orbit: the largest diameter found is $1223.05$.

**Computation 10 (decomposition of the extreme words).** For each orbit, take the two states realizing $\operatorname{diam}V$, a shortest word between them (breadth-first search), and cut it greedily into chord tokens and single other letters ("connectors"). Results for the three largest orbits and the orbit of $0$ at each of the ten radii (32 words), and for 75 orbits with diameter above 100 drawn at random from the searches at $\delta=1/20$, level 1 and $1/55$:
- the chord tokens cover at least $90.5\%$ of the letters of every word (the minimum is the orbit of $0$ at $\delta=1/10$; from $96\%$ to $99.8\%$ for the extreme words at $\delta\le1/30$);
- consecutive tokens of one class form at most 8 maximal runs;
- the connectors change the internal coordinate by at most $24.73$ in total, so the tokens carry everything else;
- among 1 798 tokens of the extreme words at four radii ($1/10$, $1/55$, level 1, $1/80$), all but 6 are the word that $T$ assigns, so the runs that avoid these 6 tokens are segments of chord runs;
- the largest internal translations at $\delta=1/30$, $1/55$, $1/80$ come from words with 5 to 7 runs that change class at every switch (at $1/55$: runs of $66,10,21,11,10,54$ tokens alternating between the lines $\mathbb RE$ and $\mathbb R\bar E$, 963 of 975 letters; at $1/80$ most consecutive runs lie on $\mathbb R\bar E$ in opposite directions). The runs switch at the windows of the breakpoints $\pm F,\pm\bar F$, through one or two letters. For example $a(-\bar F)=-F$ exactly. Runs of ten or more tokens start at offsets $|h|$ of order $\delta$ (at most $2.1\delta$ in the referee's words).

So all observed conjugate growth comes from the twelve chord tokens. The total number of chord steps on a word, multiplied by $\delta$, stays between $1.9$ and $3.2$ on the 32 extreme words. **[computed, exact orbits and words]**

### 2.4 Conjectures

**Conjecture B$^\ast$ (chord classification with bounded chaining).** There are $\delta_0\in(0,2/5]$, $N_0$ and $c_0$ such that for every $r$ with $0<\delta\le\delta_0$, every word map $x\mapsto\zeta^jx+t$ at every point $z$ is also the word map at $z$ of a word that splits into $N\le N_0$ segments of chord runs (of any classes) and further letters, the *connectors*, whose contributions to $\sigma t$ have total modulus at most $c_0$. Then
$$|\sigma t|\le c_0+\sum_{i=1}^{N}D_i,\qquad N\le N_0,$$
where $D_i$ is the internal translation of the $i$-th segment. **[conjecture]** Evidence: Computation 10 ($N\le8$, $c_0\le25$ suffice on 107 shortest words at ten radii, counting the 6 tokens not assigned by $T$ as connectors).

The requirement that the $D_i$ come from a word realizing the map is the content of the conjecture. If the $D_i$ may be arbitrary chord runs, the inequality is equivalent to Conjecture A for small $\delta$: line 1, Theorem 6(2) gives, for $\delta\le1/20$, a chord run from $0$ with internal translation above $0.50202/\delta-11.862$, so $M(r)\le C/\delta$ yields the inequality with $N_0=\lceil C/0.50202\rceil$ copies of that run and $c_0=11.862\,N_0$.

**Corollary 11.** Conjecture B$^\ast$ implies $M(r)\le c_0+N_0(58.4/\delta+9.6)$ for $0<\delta\le\delta_0$, which is Conjecture A of line 1 for these radii, and hence (B). **[proved, given the conjecture]**

---

## 3. Proofs

### 3.1 Proposition 1

1. If $y\in D_1$ then $a(y)+1=\zeta^{-1}(y+1)$, so $|a(y)+1|^2=|y+1|^2$. Applying $\sigma$, which is a ring homomorphism commuting with conjugation, gives $\sigma(a(y))+1=\zeta^{-2}(\sigma y+1)$. If $y\notin D_1$, $a(y)=y$. The same holds for $a^{-1}$ (with $\zeta$) and for $b^{\pm1}$ about $+1$.
2. The first claim is the definition of the disks. $\alpha-\beta=4\operatorname{Re}y$ and $\alpha+\beta=2|y|^2+2$ determine $\operatorname{Re}y$ and $|\operatorname{Im}y|$. Applying $\sigma$ gives the formula for $|\sigma y|^2$.
3. $|\sigma(ay)|\le|\sigma(ay)+1|+1=|\sigma y+1|+1\le|\sigma y|+2$, and symmetrically. The last sentence follows from item 2. $\square$

### 3.2 Proposition 2

1. Put $\tau=B\circ A^{-1}$ (first $A^{-1}$, then $B$). From $A^{-1}(z)=\zeta z+\zeta-1$, $\tau(z)=\zeta^{-1}(\zeta z+\zeta-2)+1=z+2(1-\zeta^{-1})$. So $\Gamma=\langle A,\tau\rangle$. Conjugation by $A$ multiplies translation vectors by $\zeta^{-1}$, so the normal closure of $\tau$ is the group of translations by $\sum_k\mathbb Z\zeta^k\cdot2(1-\zeta^{-1})=2(1-\zeta^{-1})\Lambda=K$, since $1-\zeta^{-1}=-\zeta^{-1}(1-\zeta)$. Every element of $\Gamma$ is $A^m$ followed by a translation in $K$. The elements $A^m$ with $m\not\equiv0$ have non-trivial linear part, so the translations in $\Gamma$ are exactly $K$. Finally $A^m(x)=\zeta^{-m}(x+1)-1$.
2. The first claim follows from item 1. $|\Lambda/K|=|N_{\mathbb Q(\zeta)/\mathbb Q}(2)|\cdot|N(1-\zeta)|=16\cdot5=80$. Multiplication by $\zeta$ fixes the class of $x$ iff $(1-\zeta)x\in K$, iff $x\in2\Lambda$, and $2\Lambda/K\cong\Lambda/(1-\zeta)$ has 5 elements. Since $\mu_5$ has prime order, the other 75 classes lie in orbits of size 5: $5+15=20$.
3. Each letter acts at each point as $A^{\pm1}$, $B^{\pm1}$ or the identity. $K$ contains $\kappa\mathbb Z[\varphi]$ and $\kappa\zeta\mathbb Z[\varphi]$ with $\kappa=2(1-\zeta)$. Since $\mathbb Z[\varphi]$ is dense in $\mathbb R$, these are dense in the two real lines $\mathbb R\kappa$ and $\mathbb R\kappa\zeta$, which are independent; so $K$ is dense in $\mathbb C$, and so is every coset $\Gamma y\supseteq y+K$. $\square$

### 3.3 Proposition 3

1. $\iota$ maps $D_1$ onto itself and $\iota\circ A\circ\iota(z)=\overline{\zeta^{-1}(\bar z+1)}-1=\zeta(z+1)-1=A^{-1}(z)$; the same for $B$. $\nu$ maps $D_1$ onto $D_2$ and $\nu A\nu(z)=-(\zeta^{-1}(-z+1)-1)=\zeta^{-1}(z-1)+1=B(z)$. Then $(a\iota)^2=a\,\iota a\iota=aa^{-1}=\mathrm{id}$.
2. These properties hold at $r=r_c$, where $GG_5(r_c)$ is infinite (`critical-radius-n5.md` Theorem A; Lean: `infinite_GG_five`). A property that implied finiteness would imply it at $r_c$ too.
3. By line 1, Theorem 6(1), for each $k$ there is $r<r_c$, as close to $r_c$ as wanted, with $t_kE\in O_r(0)$. Its unboundedness in internal space is line 1, Theorem 4(1). $\square$

### 3.4 Lemma 4

If every test passes, every letter applies its global rotation, so $w_i$ acts at $X$ as the composite of the global rotations, which is the translation listed in §1 ($2F=2\varphi^{-1}E$ for $w_1,w_2$, and $(2,-4,4,-2)=-2\varphi^{-2}E$ for $w_3$, checked exactly). The translation is parallel to $E$, so $h$ is unchanged. The conjugates are $\sigma(2\varphi^{-1})=-2\varphi$ and $\sigma(-2\varphi^{-2})=-2\varphi^2$, both multiplying $\sigma E$ (line 1, Theorem 4(2)). So after $k$ steps the conjugate is $-(2\varphi(k-n_k)+2\varphi^2n_k)\sigma E=-(2k\varphi+2n_k)\sigma E$, using $\varphi^2-\varphi=1$, and its modulus is at most $2\varphi^2k|\sigma E|$. $\square$

### 3.5 Lemma 5

Item 1 is exact arithmetic in $\Lambda$: $b^\ast E=-\varphi^{-1}E=-F=(-1,1,-1,1)$, $P+P'=(-2,2,-2,2)$, $-F-P=(0,1,1,-1)=u$, and $|u|^2=3+\varphi$ by the formula $|x|^2=(S_0-P_1)+(P_1-P_2-P_3)\varphi$ with $S_0=\sum x_i^2$ and $P_d=\sum_ix_ix_{i+d}$, which gives $S_0=3$, $P_1=0$, $P_2=-1$, $P_3=0$. Item 2: $\bar uE+u\bar E=(-1,0,-2,-2)=-1-2\zeta^2-2\zeta^3=2\varphi-1=\sqrt5$.

For the consequence, write $X=-F+\Delta$ with $\Delta=(s-b^\ast)E+hN$, and $\ell(\Delta)=2\operatorname{Re}(\bar u\Delta)=\sqrt5(s-b^\ast)+gh$, where $g=2\operatorname{Re}(\bar uN)$ is a real constant. Since $X-P=u+\Delta$ and $X-P'=-u+\Delta$ (item 1),
$$|X-P|^2=r_c^2+\ell(\Delta)+|\Delta|^2\ \ge\ r_c^2+\ell(\Delta),\qquad|X-P'|^2=r_c^2-\ell(\Delta)+|\Delta|^2\ \ge\ r_c^2-\ell(\Delta).$$
Suppose $w_i$ passes all its tests at $X$ at radius $r$. Then in particular it passes the tests whose centres are $P$ (for $i=1$) or $P'$ (for $i=2$), so for $i=1$: $\ell(\Delta)\le-\delta$, and for $i=2$: $\ell(\Delta)\ge\delta$. Hence:
- every $s\in I_1$ with $\sqrt5(s-b^\ast)>-\delta-gh$ lies in $\mathcal B_h(r)$;
- every $s\in I_2$ with $\sqrt5(s-b^\ast)<\delta-gh$ lies in $\mathcal B_h(r)$.

Put $c=gh$. Recall $b^\ast\in I_1$, so $b^\ast$ is in the first set exactly when $c>-\delta$.
- If $-\delta<c\le\delta$: the union of the two sets contains the open interval $\bigl(b^\ast-(\delta+c)/\sqrt5,\ b^\ast+(\delta-c)/\sqrt5\bigr)$, of length $2\delta/\sqrt5$. Its ends stay inside $I_1\cup I_2$, because $2\delta/\sqrt5\le0.358<\varphi^{-2}=|I_1|=|I_2|$ for $\delta\le2/5$.
- If $c>\delta$: the first set contains $\bigl(\max(-1,b^\ast-(\delta+c)/\sqrt5),\,b^\ast\bigr]$, which contains an open interval of length $\min(2\delta/\sqrt5,\varphi^{-2})=2\delta/\sqrt5$.
- If $c\le-\delta$: the second set contains $\bigl(b^\ast,\,\min(-\varphi^{-3},b^\ast+(\delta-c)/\sqrt5)\bigr)$, likewise. $\square$

### 3.6 Lemma 6

Put $q=F_m$, $p=F_{m-1}$. By Binet's formula $q\theta-p=(-1)^{m-1}\varphi^{-m}=:\epsilon$ (line 1, §3.5, item 3). So $x+j\theta=x+jp/q+j\epsilon/q$. Since $\gcd(p,q)=1$, $j\mapsto jp\bmod q$ is a bijection of $\{0,\dots,q-1\}$. So the $q$ points are $x+i/q+e_i$, $i=0,\dots,q-1$, with $e_i=j\epsilon/q$ for the $j$ with $jp\equiv i$, and all $e_i$ lie between $0$ and $\epsilon$. The arc from the point with index $i$ to the point with index $i+1$ (modulo $q$, going once around) has length $1/q+e_{i+1}-e_i\le1/q+|\epsilon|$, and this length is positive because $|\epsilon|=\varphi^{-m}<1/F_m$ (as $F_m<\varphi^{m}$). These $q$ arcs have total length 1, so they tile the circle, so every arc between consecutive points is at most $1/q+\varphi^{-m}$. $\square$

### 3.7 Theorem 7

1. In the coordinate $x=(s+1)/2\in\mathbb R/\mathbb Z$, $T$ is $x\mapsto x+\theta$, and $J_h$ of Lemma 5 is an open arc of length $\delta/\sqrt5$. If $L(X_0;r)\ge F_m$, the points $s_0,\dots,s_{F_m-1}$ avoid $\mathcal B_h(r)\supseteq J_h$. But by Lemma 6 their arcs are shorter than $\delta/\sqrt5$, so the open arc $J_h$ contains one of them: a contradiction. Hence $L\le F_m-1$.

   For the numerical form put $F=F_{m-1}$. The integer $m$ is well defined and at least 3, since $1/F_2+\varphi^{-2}>1>\delta/\sqrt5$. By minimality, $1/F+\varphi^{-(m-1)}\ge\delta/\sqrt5$. By Binet, $\varphi^{m-1}=\sqrt5F+\psi^{m-1}\ge\sqrt5F-\varphi^{-1}$ with $\psi=-\varphi^{-1}$, so $\varphi^{-(m-1)}\le1/(\sqrt5F-0.6181)\le0.6188/F$ for $F\ge1$ (since $1-0.6181/\sqrt5\ge0.7235$). Hence $1.6188/F\ge\delta/\sqrt5$, that is $F_{m-1}\le3.620/\delta$. And $F_m=\varphi F_{m-1}+\psi^{m-1}\le\varphi F_{m-1}+1$, so $L\le F_m-1\le\varphi\cdot3.620/\delta\le5.86/\delta$.

   For $\delta>2/5$: the disk tests have centres $P_m$ independent of $r$, so a test passed at radius $r$ is passed at every larger radius, and $L(X_0;r)$ is non-decreasing in $r$. So $L(X_0;r)$ is at most its value at $\delta=2/5$, where $m=7$ and $L\le12$.
2. By Lemma 4, the word maps after $k\le L$ complete tokens have $|\sigma t|<9.960k\le9.960\cdot5.86/\delta\le58.4/\delta$. The prefixes of the token that fails add at most 5 letters that act. Each acting letter composes the word map with $x\mapsto\zeta^{\mp1}x+c$, $c=\pm(\zeta^{\mp1}-1)$, and changes $|\sigma t|$ by at most $|\sigma c|=|\zeta^{\mp2}-1|=1.9022$; that adds at most $9.6$.
3. By Proposition 3(1), $g\in S$ conjugates the token $w_i$ to the token $g\cdot w_i$ and carries the run from $X_0$ to a run from $g(X_0)$ with the same length. $\sigma$ commutes with $\iota$ and $\nu$, so the internal translations have the same moduli. $\square$

### 3.8 Corollary 11

A segment of a chord run is the chord run from its first point, cut short, so by Theorem 7(2), (3) every $D_i\le58.4/\delta+9.6$ for $\delta\le\delta_0\le2/5$. The connectors add at most $c_0$, by the triangle inequality. So $M(r)<\infty$ for $0<\delta\le\delta_0$, and $GG_5(r)$ is finite there by `critical-radius-n5.md` Lemma 4.1(2), (3), which holds at every radius, norm radius or not. For smaller $r$, finiteness follows by group monotonicity (`boundary-contact.md` Theorem 3.4). Conjecture A on all of $r<r_c$ would also need a bound on $\delta M(r)$ for $\delta>\delta_0$. That does not follow: the "only if" direction of the conjugate criterion is proved only at non-norm radii, and it is not uniform in $r$. (B) does not need it. $\square$

---

## 4. What the computations say, in plain terms

**One mechanism.** In every orbit examined, the conjugate coordinate grows only while the orbit is applying the three critical words, or their mirror images, on a thin strip along one of the two chords through $0$ in the directions $E$ and $\bar E$. Inside such a strip the critical words are exact translations along the chord, so the distance $h$ from the chord is conserved. The position on the chord performs the golden rotation, and the conjugate coordinate drifts linearly with the number of steps (Lemma 4). Everything else the orbit does changes the conjugate coordinate by a bounded amount (at most 25 in the data).

**Each run stops at scale $1/\delta$.** A run stops when the rotation brings the point within about $\delta$ of a breakpoint. At the breakpoint $-\varphi^{-1}$ the two words that meet there have tight test circles centred symmetrically about the breakpoint, so whatever the offset $h$, one side or the other is cut over a length $2\delta/\sqrt5$. The golden rotation enters every interval of that length within about $5.9/\delta$ steps (Theorem 7). The truth is about $2.5/\delta$ steps and $20/\delta$ in the conjugate coordinate (Computation 8).

**But runs chain.** A run that stops in a breakpoint window can continue on the other chord: one letter carries the window of $-\bar F$ onto that of $-F$. The data show chains of up to 7 runs, whose conjugate displacements add with rotations. In the best cases found the chain is $1.45$ times the best single run. The data never show more than $3.2/\delta$ chord steps in a chain, and $\delta M(r)$ stays between $17$ and $25$ from $\delta=1/10$ to level 2.

## 5. The remaining gap, and an assessment

**Gap.** Conjecture B$^\ast$: bound the number of chord runs that one word can chain, uniformly in $\delta$. With Theorem 7 this gives Conjecture A for small $\delta$, and (B). Two things are missing:
1. *Classification.* Show that outside chord runs the conjugate coordinate changes by $O(1)$ per run. The data support it (Computation 10), but nothing here proves that there is no other mechanism.
2. *Bounded chaining.* Runs end in $O(\delta)$-windows at the breakpoints $\pm F,\pm\bar F,\pm\varphi^{-3}E,\dots$ and of their mirror images, and they restart from there on either chord with a new offset $h=O(\delta)$. In coordinates zoomed by $1/\delta$ this is a first-return system on finitely many windows. Its transition maps are piecewise isometries (the connectors), composed with golden-rotation return times. Bounded chaining means that this zoomed system has bounded orbits, uniformly in $\delta$. That is the tight-window renormalization problem of `sharp-lower-bound-limit-system.md`, now in a form where the long excursions between windows are explicitly golden-rotation runs.

**Assessment.**
- *Exact invariants (line (a)) and symmetry or reversibility (line (c)): dead.* Every exact conserved quantity, congruence class or reversing involution is present at $r_c$ as well (Propositions 1–3), and there are no others in the congruence data. They constrain orbits but cannot close them.
- *Controlled quantity (line (b)): repairable, not closed.* The line gives a correct new theorem: uniform $1/\delta$ control of the one mechanism that the data show to be responsible for all conjugate growth. It also reduces Conjecture A to a precise, well-supported statement about chaining (Conjecture B$^\ast$). With constant 1, the single-run form of line 1's Conjecture B for $M(r)$, "a single chord run dominates", fails at $\delta=1/30$ and $1/55$ (ratios $1.12$, $1.45$); with a constant $C'\ge1.45$ it is consistent with the data. The chaining is where the difficulty of (B) now sits, and it is a renormalization statement, not an invariant.

## 6. Reproduction

The engine is `tdcsg-orbit` (`../engine.md`), used for cross-checks of orbit sizes and maximal conjugates:

```sh
B=.lake/build/bin/tdcsg-orbit
$B orbit -n 5 --r2 closed-1/55 --start pow:470,202,166,493 --format lines        # finite 111107, conj 2 = 1299.43
$B orbit -n 5 --r2 re:7/2,9/5 --start pow:1818,-1259,1899,-135 --cap 5000000 --format lines   # finite 793605, conj 2 = 6927.03
$B orbit -n 5 --r2 re:41/10,4/5 --format lines                                    # finite 30165 (level 1)
```

Radii: $\delta=p/q$ is `closed-p/q`; level 1 is `re:41/10,4/5` $=(33+8\varphi)/10$, level 2 is `re:7/2,9/5` $=(17+18\varphi)/10$.

The other computations use throwaway analysis code, not part of the repository; every step is specified here so that it can be re-implemented.
- *Exact lattice dynamics.* Points are integer vectors in the basis $1,\zeta,\zeta^2,\zeta^3$; $\zeta^{-1}(y_0,y_1,y_2,y_3)=(y_1-y_0,y_2-y_0,y_3-y_0,-y_0)$; the disk test is the exact sign of $\rho-|y\pm1|^2$ in $\mathbb Z[\varphi]$, with $|x|^2$ as in §3.5; $\sigma(x_0,x_1,x_2,x_3)=(x_0-x_2,x_3-x_2,x_1-x_2,-x_2)$. A C program performs the lifted breadth-first search over states $(y,j)$ (Computation 9). It reproduces the engine's sizes and maxima on every orbit compared (the orbit of 0 at $1/10$, $1/55$, levels 1 and 2, and the two seeds above).
- *Computation 9.* Seeds: all lattice points of $D_1\cup D_2$ with coefficients in $[-10,10]$ and $|\sigma y|\le15$ (5 429 points), plus random points (a uniform physical point in $D_1\cup D_2$ and a uniform internal point in the disk of radius $R$, rounded to $\Lambda$ in $\mathbb C\times\mathbb C$). Seeds already in a computed orbit are skipped. $\operatorname{diam}V$ is the maximum over 256 directions of the projected width. The extreme pair is then re-found over 512 directions, and $|V_2-V_1|$ is evaluated from its exact points.
- *Computation 10.* A shortest word between the extreme states is found by breadth-first search from the first state, in the state graph. The tokenizer reads left to right and at each position matches a 6-letter token, then a 5-letter token, among the twelve, or else records one connector letter. The $T$-check maps the start of each token by the inverse of its symmetry class and compares $i(s)$ with the token's index.
- *Computation 8.* For each offset $h$, each word's good set on the line $\{sE+hN\}$ is the intersection of the intervals $\{s:|sE+hN-P_m|^2\le\rho\}$ over its test centres, computed by solving quadratics in double precision. $\sup L$ is the largest $n$ for which the $n$ rotated copies $\mathcal B_h-j\cdot2\varphi^{-1}$, $j<n$, do not cover $[-1,1)$, found by doubling and bisection. The strip graph is a breadth-first search over $(n_{12},n_3)\in\mathbb Z^2$, the position $s=s_0+2n_{12}\varphi^{-1}-2n_3\varphi^{-2}$, with an edge whenever the corresponding word, or the inverse word at the image point, passes its tests; its internal extent is $2|\sigma E|$ times the range of $n_{12}\varphi+n_3\varphi^2$.
- *Computation 2.1.* The residues modulo $m\Lambda$ of the $\Gamma$-orbit are the closure of the residue of $y_0$ under $A^{\pm1},B^{\pm1}$ reduced modulo $m$. They are compared with the residues of the exact orbit.
- *Lemma 5, item 1–2, and the transfer identity $A(-\bar F)=-F$:* exact vector arithmetic as above. $-\bar F=(-2,-1,0,-2)$, and $|-\bar F+1|^2=5-3\varphi<\rho$, so $a$ acts there as $A$.
