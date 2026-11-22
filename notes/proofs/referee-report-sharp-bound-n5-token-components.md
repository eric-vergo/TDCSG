# Referee report: `sharp-bound-n5-token-components.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: a fence for the two-family token walk, and the cut-off of every token component at scale $1/\delta$" (`sharp-bound-n5-token-components.md`, commit `700b4a2`). Companions consulted: `sharp-bound-n5-chaining.md` and its referee report (definitions of §1, Conjecture B$^\sharp$, Proposition 6, the three-distance step of Theorem 1), `sharp-bound-n5-invariant.md` (Lemma 5, Proposition 3), `sharp-bound-n5-critical-orbits.md` (Table 2.1, word conventions), `critical-radius-n5.md` (Lemma 4.1), `sharp-bound-n5-conjugate.md` (the definition of $M(r)$).

## Summary

**Verdict: correct after minor fixes. (T) is proved.** Lemma 1, Lemma 2, Theorem 3, Theorem 4 and Corollary 5 are correct as written, with all constants confirmed. The fixes are clarifications of wording, applied to the note; none touches an argument.

I tried to break the proof at the places the brief named. Each one holds.
- **The indices are functions of position.** All token translations lie in $2\mathbb Z[\varphi]E\oplus2\mathbb Z[\varphi]\bar E$. Since $E,\bar E$ are $\mathbb R$-independent and $2n\varphi^{-1}-2m$ determines $(n,m)$, the pair $(n_1,n_2)$ is a homomorphism of the translation lattice to $\mathbb Z^2$, read off from $X-X_0$. No path-dependence is possible. In the computations, no point was ever reached with two different index pairs (0 inconsistencies in $263\,750$ components).
- **No step can jump over the fence.** The worry was that a step of length about 1 might cross a strip of width $\kappa_0\delta$ without starting on it. The proof does not work with geometric strips. It works with the index $n_1$, which every family-1 edge changes by exactly $\pm1$ and every family-2 edge leaves fixed. So any edge between $\{n_1\le c\}$ and $\{n_1\ge c+1\}$ is a family-1 edge whose lower endpoint lies in column $c$. Column $c$ lies on the lifts $\mathcal L(b^\ast+\eta_c+2k)$, and these are exactly the lines Lemma 2 controls. Steps of different lengths ($\tau_1=\tau_2=2\varphi^{-1}$, $\tau_3=-2\varphi^{-2}$) all have $n(\tau_i)=1$, so they cannot jump over the column either.
- **The fence is invariant under the other family.** Family-2 tokens translate by multiples of $\bar E$, which have $s=0$. So they keep both $s$ and $n_1$, and they map each line $\mathcal L(p)$ to itself. The column is a set of positions on the circle $s\bmod 2$, and only family-1 moves change that position.
- **The cut is a genuine partition.** I checked the four edge types between $L=(L_0\setminus\mathcal X)\cup\mathcal Y$ and $R=(R_0\setminus\mathcal Y)\cup\mathcal X$ one by one. The dead ends are what make it work. A point of $\mathcal X$ (on $s=-\varphi^2+\eta$) carries only the $w_1$ edge. A point of $\mathcal Y$ (on $s=\varphi^2+\eta$) carries only backward family-1 edges. The proof uses that the edges at a point are exactly the tokens acting there, because the twelve tokens are closed under inversion ($w_1^{-1}=\nu\cdot w_2$, $w_2^{-1}=\nu\cdot w_1$, $w_3^{-1}=\nu\cdot w_3$). That is true and was checked.

I recomputed every exact input independently: the test centres from the words, the eight disk inequalities, and the Lemma 1 identities. I also ran an adversarial exact computation. It covered $263\,750$ token components at 19 radii, lattice and non-lattice seeds, with seeds concentrated near the fence corners. It also covered $5.1\cdot10^6$ exact test points placed on the fence lines themselves, for $\delta$ from $\tfrac25$ down to $10^{-6}$. Nothing contradicts the note:
- no component crosses a fence column;
- no index range exceeds the bound;
- no internal diameter exceeds the bound;
- no token acts anywhere the note's domain model excludes;
- no point of a fence line violates Lemma 2.

The fence width is sharp at first order. At $1.02\,\kappa_0\delta$, exact points violating Lemma 2 appear near the corners $-F$, $X^\ast$ and $-X^\ast$, at $\delta=0.05$ and at $\delta=10^{-3}$.

**What "(T) is proved" may be relied on for.** For $0<\delta\le\tfrac25$, every connected component of the twelve-token graph $\mathcal T(r)$ satisfies two bounds. This holds for components of any point of $\mathbb C$, lattice or not.
- Each index $n_1$, $n_2$ takes at most $F_j+2<5.2361/\delta+2.4473$ values, where $j$ is the least integer with $\varphi^{-(j-2)}<\kappa_0\delta$.
- $\sup_{X,Y\in K}|\sigma(Y-X)|<72.0683/\delta+41.8152$.

For $\delta>\tfrac25$ the internal diameter is below $222.0$. These are exactly the hypotheses (T) of the chaining note's Conjecture B$^\sharp$, with $\delta_0=\tfrac25$ and $C_T=88.8$. So Proposition 6 now needs only (K). The theorem says nothing about connector letters, and nothing about the number of token components in an orbit.

## 1. Verdicts

| result | verdict |
|---|---|
| §1 definitions (domains, indices, columns, internal displacement) | **correct**; the indices are well defined (see Summary); "$K=2(1-\zeta)\Lambda$" clashed with $K$ for a component and is **renamed** |
| Lemma 1 (two-disk certificates) and rows (a)–(c) | **correct**; all values exact in $\mathbb Z[\varphi]$, re-derived (§2.1) |
| Consequences of Lemma 1, for every $\delta>0$ | **correct** |
| Lemma 2 (fence lemma), items 1–4 | **correct**; every decision re-derived; minimum margin $0.17318$ against $0.144721$ |
| Computation 4.1 | **reproduced independently** (exact centres, 60 digits) |
| Computation 4.2 | not re-run in its double-precision form; its sharpness conclusion is confirmed by exact points (§3.2) |
| Theorem 3 (index cut-off) | **correct**, including the three-distance step and the Binet estimate |
| Theorem 4 ((T)) | **correct**; constants $72.0683$, $41.8152$, $221.99$ confirmed |
| Corollary 5 | **correct after minor fixes**: item 2 now says that $D(r)$ is taken over the orbits of all points of $\mathbb C$, why $D(r)<\infty$ gives words with at most $D(r)$ connectors, and that the bound $222.1$ replaces item 1's bound for $\delta>\tfrac25$ |
| Computation 4.3 (token components) | **reproduced**: every per-radius maximum of $\delta\cdot(n_1\text{-range})$, and the straddle counts at $0.45\delta$ and $\delta$ (§3.3) |
| §2.4 finite-type form of (K) | conjecture, appropriately labelled (§4) |

## 2. The proofs, line by line

### 2.1 Lemma 1

The convex-combination argument is sound. With $X=X_0+\eta E+\tau\bar E$, $q$ and $q'$ have the same quadratic part $|\eta E+\tau\bar E|^2$. The choice of $\lambda$ kills the $\tau$-linear term, so $\lambda q+(1-\lambda)q'\ge\delta+B\eta$ for every $\tau$, that is, on the whole line. It is not only a statement near the corner.

I recomputed every value exactly. I used the norm formula $|x|^2=(S_0-P_1)+(P_1-P_2-P_3)\varphi$, re-derived from $\zeta^d+\zeta^{-d}$, and $\ell(Z)=|v+Z|^2-|v|^2-|Z|^2$.
- (a) $|X_0-c|^2=|X_0-c'|^2=3+\varphi$, $\ell(E)=5$, $\ell(\bar E)=2+\varphi$, $\ell'(E)=2\varphi-1$, $\ell'(\bar E)=4-3\varphi$. Then $\lambda=1-\varphi/2=(3-\sqrt5)/4$, $\lambda\ell(\bar E)+(1-\lambda)\ell'(\bar E)=0$ exactly, and $B=6-2\varphi=5-\sqrt5$.
- (b) The same values with opposite signs, and $B=-(5-\sqrt5)$.
- (c) $X^\ast=(-3,-3,-1,-3)$ has $s=-\varphi^2$ and $t=2$ exactly. Its centres $(-3,-2,-2,-4)$ and $(-3,-2,0,-4)$ are the conjugates of $U_2[3]=U_3[3]$ and $U_2[4]=U_3[4]$, both at squared distance $3+\varphi$. The values are those of (b).
- $1/(5-\sqrt5)=\tfrac15+\tfrac{\varphi}{10}=(5+\sqrt5)/20=\kappa_0$, $2+\varphi=\sqrt5\varphi$ and $4-3\varphi=-\sqrt5\varphi^{-2}$, all exact.

So $U_1$ misses $\mathcal L(b^\ast+\eta)$ for every $\eta>-\kappa_0\delta$, and $U_2,U_3$ miss it for every $\eta<\kappa_0\delta$. Likewise $\overline{U_2},\overline{U_3}$ miss $\mathcal L(-\varphi^2+\eta)$ for every $\eta<\kappa_0\delta$. All four hold for every $\delta>0$.

### 2.2 Lemma 2

- *The domain model.* With $a$ the rotation by $\zeta^{-1}$ about $-1$ and words read left to right, the test centres derived from the words are exactly Table 1.1. The translations are $(2,-2,2,-2)=2\varphi^{-1}E$ for $w_1,w_2$ and $(2,-4,4,-2)$, with $s=2\varphi-4=-2\varphi^{-2}$, for $w_3$. The symmetries give the other nine domains as stated. In the computations, the letter-by-letter test and the disk-intersection test of the note agreed at every visited point, for all twelve tokens (0 mismatches).
- *The $s$-functional.* $\operatorname{Im}(E^2)=|E|^2\sin36^\circ$, and the norm of $X\mapsto s(X)$ is $2\varphi/\sqrt5=1.4472136$ (60 digits). So the single-disk $s$-range of a disk of radius $r_c$ is its centre's $s$ plus or minus $3.1100058$.
- *The $s$-ranges.* All twelve single-disk ranges agree with §3.2 and Computation 4.1(1) to the digits shown: $U_1\subseteq[-3.5572194,-0.5732758]$, $U_2\subseteq[-0.6627922,2.3211514]$, $U_3\subseteq[-0.6627922,1.4267242]$, the family-2 ranges, and their negatives.
- *Item 1.* For $|k|\ge2$ the lines lie outside $[-3.5573,2.3212]$ (they have $s>3.237$ or $s<-4.473$). For $k=0$ the item is Lemma 1.
- *Item 2.* On $\mathcal L_{-1}$, $s\in(-2.7633,-2.4731)$. The table margins are $3.1913$, $0.29688$, $1.1913$ and three times $2.2969$, against the required $0.144721$. The disks used are $-U_1[4]$, $-U_2[4]$, $-U_3[5]$, $\overline{U_1}[4]$, $-\overline{U_2}[2]$ and $-\overline{U_3}[2]$. The centres $c_{13}$ and $-\overline{c_{13}}$ differ by $(-2,0,2,2)$, of squared modulus $8+12\varphi=4\varphi^4$, so they are $5.236>2r_c=4.298$ apart. The eleven other tokens are all accounted for: $U_2,U_3$ by range, $\overline{U_2},\overline{U_3}$ by Lemma 1(c), six by single disks, and $-\overline{U_1}$ by disjointness.
- *Item 3.* $|c_{31}-c_{35}|^2=40-20\varphi$ exactly. The combined disk has squared radius $3.1856614$ and $s(\bar c)=-1.3742646$, and the margin is $0.1731828$. That is the minimum margin, $0.0285$ beyond the required $0.144721$. The $S$-lemma weights $(\tfrac14,\tfrac34)$ are only a certificate, and the combined constraint is a valid consequence of the two disk constraints whatever the weights.
- *Item 4.* $\nu$ maps $\mathcal M$ to $\mathcal L_{-1}$ for the parameter $-\eta$, maps forward family-1 domains to backward ones, and maps family-2 forward domains to family-2 backward ones. The argument is correct.

### 2.3 Theorem 3

- *The partition.* Checked in the Summary. One redundancy, not an error: the neighbours of a point of $\mathcal X$ can only be at $s=-1.382+\eta$, since only $w_1$ acts there; the alternative $-3.382+\eta$ never occurs.
- *The counting.* The three-distance statement for $F_j$ points of the golden rotation (largest gap $\varphi^{-(j-2)}$) was checked numerically for $3\le j\le19$. An open arc longer than the largest gap contains a point, so any $F_j$ consecutive columns contain a fence column. $\kappa_0\delta\le0.14472<\varphi^{-4}=0.14590$ gives $j\ge7$. The contradiction step ($a\le c-1$ and $b\ge c+2$ against the dichotomy) is right.
- *The numerical form.* $\varphi^3/(\sqrt5\kappa_0)=2\varphi^2$, since $\sqrt5\kappa_0=\varphi/2$, and Binet gives the rest.
- *Family 2.* Complex conjugation fixes both disks and conjugates $a,b$ to $a^{-1},b^{-1}$. It exchanges $s$ and $t$, and the classes $\mathrm{id},\nu$ with $\iota,\iota\nu$, so it carries $n_1$ on $\bar K$ to $n_2$ on $K$. The mirrored fence was also tested directly (§3.2).

### 2.4 Theorem 4

- *The internal displacement.* $\sigma(\Delta s)=\Delta s-2\sqrt5n$ holds because $\sigma$ acts on $\mathbb Q(\sqrt5)$ as $\sqrt5\mapsto-\sqrt5$.
- *The modulus.* $\sigma E=\zeta^2-\zeta^4$ has modulus $1.9021130$ and argument $126^\circ$ exactly. $\sigma\bar E=\overline{\sigma E}$ was checked numerically. So $|aw+b\bar w|^2=|w|^2(a^2+b^2-2ab\cos72^\circ)\le\varphi^2|w|^2\max(|a|,|b|)^2$.
- *The constants.* $\varphi|\sigma E|\cdot13.58658=41.8152$, $\varphi|\sigma E|\cdot4\sqrt5\varphi^2=72.0683$, and $72.0682\cdot\tfrac52+41.8152=221.99$.
- *The case $\delta>\tfrac25$.* Monotonicity of the domains in $r$ gives the bound, since every edge at $r$ is an edge at $r'$.

The bound $|\Delta s|\le7.11444$ is crude but valid: every point of a component with more than one point lies in a token domain.

### 2.5 Corollary 5

- *Item 1* is Proposition 6 of the chaining note with the new constant. I re-checked that proof, including the subadditivity of $|\sigma t|$ under composition and the connector contribution $|1-\zeta^{\mp2}|=1.90211$.
- *Item 2* is correct, with three gaps in the wording that are now fixed:
  - "if $D(r)<\infty$ then (K)" needs the remark that the end state determines the word map;
  - $D(r)$ must range over the orbits of all points of $\mathbb C$, since `critical-radius-n5.md` Lemma 4.1 uses $M(r)$ over all points;
  - for $\delta>\tfrac25$ the bound $222.1$ replaces item 1's bound.

"Each lifted orbit has at most $5|GG_5(r)|$ states" is a valid (generous) bound.

## 3. Reproduction

All code is the referee's own and was written for this report. Scratch only; nothing was added to the repository. The engine was not used: the token walk is not a group orbit.

### 3.1 Exact inputs (`zq.py`, `centres.py`, `check1.py`)

Exact $\mathbb Z[\zeta]$ and $\mathbb Q(\varphi)$ arithmetic with Python fractions. The oblique coordinates of lattice points were computed exactly, by inverting the basis $E,\varphi E,\bar E,\varphi\bar E$ of $\mathbb Q(\zeta)$; its determinant is 5, the index stated in §1. The single-disk ranges and margins were computed with mpmath at 60 digits. Everything in §2.1–2.2 above comes from this run.

### 3.2 Lemma 2 on the fence lines (`lem2.c`, exact)

The program builds points exactly on the lines $s=b^\ast+\eta+2k$ ($k=-2,\dots,2$) and $s=\varphi^2+\eta$, with $\eta=m/D$ and $t=n/D$. It also builds their conjugates, which test the family-2 mirror. All twelve tokens are applied letter by letter, with exact closed-disk tests: the sign in $\mathbb Z[\varphi]$ is decided with 256-bit products.
- The $t$-values are drawn in three ways: uniform in $[-4,4]$; within $20\delta$ of the corners $-F$ ($t=0$), $X^\ast$ ($t=2$) and $-X^\ast$ ($t=-2$); and within $0.5$ of those corners.
- A quarter of the $\eta$ are pushed to within $10^{-7}$ (relative) of $\pm\kappa_0\delta$.

| $\delta$ | points (both families) | violations | forward steps on $k=\pm1$ (leaks) |
|---|---|---|---|
| $2/5$ | $1\,000\,000$ | 0 | 55 414 |
| $1/3$ | 600 000 | 0 | 36 206 |
| $1/10$ | 1 000 000 | 0 | 108 471 |
| $1/100$ | 1 000 000 | 0 | 80 849 |
| $\varepsilon^3/10$ | 1 000 000 | 0 | 87 815 |
| $10^{-4}$ | 1 000 000 | 0 | 87 891 |
| $10^{-6}$ | 1 000 000 | 0 | 87 878 |

The leaks are many, so the test is not vacuous: forward steps on the lifts $k=\pm1$ are common, and every one has the dead-end structure of items 2 and 3.

Beyond the hypotheses, no violation appeared at $\delta=0.467$ or $\delta=1$ either. The note does not claim these values.

*Sharpness.* With $\eta$ up to $1.02\,\kappa_0\delta$, violations appear at $\delta=0.05$ and at $\delta=10^{-3}$, about 1 in $10^4$ points. There are three kinds: forward family-1 tokens on $\mathcal L_0$ near $-F$; $\overline{U_2}$ acting together with $w_1$ near $X^\ast$; and item 4 near $-X^\ast$. At $1.3\,\kappa_0\delta$ the rate is about 1 in $10^3$. This confirms the note's statement that $\kappa_0$ is sharp at first order, and its identification of the failing conditions.

### 3.3 Token components (`tc.c`, exact)

Breadth-first search over the twelve tokens, applied letter by letter with exact tests (128-bit). Non-lattice points are handled as $P/d$ with $P\in\Lambda$: the disk centres are scaled by $d$ and the squared radius by $d^2$. The program uses $d=1$, $d=7$ and $d=1000$, and for $d>1$ it forces a non-integral coordinate. It records:
- each point's indices along the search, checked for consistency on every re-visit;
- for every visited point, whether the letter-by-letter test agrees with the disk-intersection model;
- for every visited point on a fence strip ($|\eta|<\kappa_0\delta$ in $s$ or in $t$), the direct conditions of Lemma 2 items 1–4;
- the fence columns and rows, with $\eta$ read from every state of the column. The spread within a column is below $1.1\cdot10^{-11}$, and every column's $|\eta|$ is at least $8\cdot10^{-5}$ away from $\kappa_0\delta$ on the runs checked;
- the internal diameter, exact up to double rounding: convex hull of $\{\sigma X\}$, then the farthest pair;
- the bounding-box diagonal, for comparison with the note.

Seeds of two kinds. Uniform seeds take a uniform physical point of $D_1\cup D_2$ and a uniform internal point of modulus at most $25/\delta$ (mode 0). Corner seeds take a physical point within $4\delta$ or $0.6$ of one of $-F$, $X^\ast$, $F$, $-X^\ast$, $-F+2E$, $\overline{-F}$ (mode 1). No component hit the size cap of $6\cdot10^6$; the largest had $2\,078\,364$ points.

Totals: $263\,750$ components at 19 radii. Zero index inconsistencies, zero model mismatches, zero Lemma 2 violations at $1\,405\,314$ visited strip points (of which $572\,783$ carry a leaking step), and zero fence straddles. Per radius, over all seed kinds:

| $\delta$ | comps | largest | most index values | bound $F_j+2$ | max $\delta\cdot$range | max $\delta\cdot$diam | max $\delta\cdot$bbox |
|---|---|---|---|---|---|---|---|
| $2/5$ | 25 000 | 35 | 7 | 15 | 2.400 | 16.88 | 20.92 |
| $1/3$ | 15 000 | 40 | 7 | 15 | 2.000 | 14.70 | 18.32 |
| $1/7$ | 15 000 | 338 | 20 | 36 | 2.714 | 24.00 | 30.96 |
| $1/10$ | 25 000 | 550 | 25 | 36 | 2.400 | 19.67 | 25.50 |
| $1/20$ | 25 000 | 1 998 | 46 | 91 | 2.250 | 18.77 | 25.82 |
| $1/30$ | 25 000 | 8 378 | 91 | 146 | 3.000 | 24.54 | 34.15 |
| $\varepsilon/10$ | 25 000 | 9 065 | 101 | 146 | 2.361 | 19.91 | 27.44 |
| $1/55$ | 20 000 | 9 341 | 101 | 235 | 1.818 | 20.56 | 24.33 |
| $1/80$ | 15 000 | 26 165 | 190 | 379 | 2.363 | 20.01 | 27.59 |
| $\varphi^{-3}/30$ | 15 000 | 113 390 | 379 | 612 | 2.974 | 24.61 | 34.28 |
| $\varepsilon^2/10$ | 7 500 | 121 149 | 423 | 612 | 2.352 | 19.96 | 27.54 |
| $\varphi^{-3}/55$ | 7 500 | 124 544 | 423 | 989 | 1.811 | 20.63 | 24.42 |
| $1/200$ | 5 000 | 122 074 | 423 | 989 | 2.110 | 17.91 | 24.71 |
| $\varphi^{-6}/30$ | 3 750 | 1 274 183 | 1 599 | 2 586 | 2.968 | 24.62 | 34.31 |
| $\varepsilon^3/10$ | 3 000 | 1 617 654 | 1 787 | 2 586 | 2.350 | 19.98 | 27.57 |
| $1/1000$ | 2 000 | 2 078 364 | 2 586 | 4 183 | 2.585 | 21.98 | 27.44 |
| $0.6$, $1$, $2$ | 30 000 | 19 | 4 | — | — | — | $\delta\cdot$diam $\le 19.9$ against $222.1$ |

Every maximum of $\delta\cdot(n_1\text{-range})$ in the note's table is reproduced exactly: $2.400, 2.400, 2.250, 3.000, 2.361, 1.818, 2.363, 2.974, 2.352, 1.811, 2.968, 2.350$. So are the bounding-box maxima, which the note measures in $\{\sigma y\}$, up to sampling: $20.91$ against $20.92$, and $33.51$ against $34.31$ at $\varphi^{-6}/30$ with a different sample. That last value is slightly above the "$34.3$" quoted in the note and the chaining note. Both describe their own samples, so this is information, not an error.

The true internal diameter is about $0.72$ times the bounding-box diagonal, so the largest observed diameter is $24.6/\delta$ against the proved $72.07/\delta+41.82$. The largest observed index count is $3.0/\delta$ against the proved $5.24/\delta+2.45$.

*Sharpness counts* (lattice uniform seeds; a component straddles a width $w\delta$ if some column $c\in[a+1,b-2]$ has $|\eta_c|<w\delta$; $n_1$ only):

| width | $\kappa_0\delta$ | $0.38\delta$ | $0.40\delta$ | $0.45\delta$ | $0.5\delta$ | $\delta$ |
|---|---|---|---|---|---|---|
| per 1 000, radii $1/10$ to $\varepsilon/10$ | 0 | 0–0.1 | 0–1.0 | 2.5–4.1 | 8.9–12.0 | 81–94 |

This matches the note's "3 to 5 in 1 000" at $0.45\delta$ and "about 85" at $\delta$, within sampling (2.5 at $1/20$). Counting either index raises the rates by a factor of about 1.5–2.

Resources: 4 cores, under 1 GB of memory per process. Large outputs were deleted after analysis.

## 4. Assessment of §2.4: (K) and the finite-type form

- *The reduction.* Corollary 5 is right. B$^\sharp$ is now equivalent to (K) for $\delta\le\tfrac25$, and (K) is equivalent to a uniform bound on the diameter of the lifted component graph. The note's explanation of why the fence does not extend to connectors is accurate: a connector changes the rotation index $j$, and the next component's indices are measured in a frame rotated by $\zeta^{\mp2}$ in internal space.
- *The box structure is correct.* By Theorem 3, the $n_1$-range $[a,b]$ of a component contains no fence column in $[a+1,b-2]$. So it lies in $[c_i,c_{i+1}+1]$ for consecutive fence columns, and likewise for $n_2$. The gaps are return times of the golden rotation to an arc, so they take at most three values, all Fibonacci numbers. In the coordinate $\eta/\delta$ the return map is Proposition 2's with $W=(-\kappa_0,\kappa_0)$, which satisfies that proposition's hypothesis $\delta|W|<\tfrac12$. The data show the Fibonacci structure clearly: the largest index counts are $101,190,379,423,612,1599,1787,2586$, close to Fibonacci numbers plus small offsets.
- *What the form leaves open.* A box type would have to include the physical position, not only the index box. Two components in the same index box but at different physical points are joined by different connectors. And a connector moves to a component whose grid is the grid of a different seed: fence columns are defined by $s\bmod2$ of that component's own points, in that component's own rotated frame. So the "graph on finitely many box types" needs a renormalization that acts on the physical position and on the rotation index together, as Proposition 2 does on one line. The statement is labelled as a direction, not a conjecture to be tested, and it is a reasonable one.
- *Two concrete tests.* The cheapest are the following.
  - Check whether $\varepsilon\cdot$ (a large component at $\delta$) lies in one component at $\varepsilon\delta$, up to $O(\delta)$-lunes.
  - Measure $D(r)$ over a few hundred random orbits, not only extreme ones, as the chaining report already suggested.

## 5. Fixes applied to the note

1. Review line: replaced by the refereed status and verdict.
2. §1: the lattice $2(1-\zeta)\Lambda$ was called $K$, which clashed with $K$ for a token component. It is now written out, with the one-line reason for the containment ($E=\zeta(1-\zeta)$, $\bar E=-\zeta^3(1-\zeta)$).
3. Corollary 5(2): $D(r)$ is over the orbits of all points of $\mathbb C$.
4. Proof of Corollary 5(2): it now says why $D(r)<\infty$ gives words with at most $D(r)$ connectors, and that the bound $222.1$ is used when $\delta>\tfrac25$.

No larger issue was found.
