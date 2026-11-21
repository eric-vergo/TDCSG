# The critical radius of two-disk compound symmetry groups for n = 5, 8, 10, 12: an open problem

Authors: Eric Vergo, Claude

**Problem and status.** Prove that the two-disk group $GG_n(r)$ is finite for every radius $r$ below the closed forms $\sqrt{3+\varphi}$, $\sqrt{10-5\sqrt2}$, $\sqrt{4-\varphi}$, $\sqrt{40-22\sqrt3}$ ($n=5,8,10,12$). Infinitude at and above these radii is machine-checked in Lean. Finiteness is proved, modulo certified exact computations, up to radii between $0.002$ and $0.009$ below them. The remaining windows are open.

Status labels used throughout: **machine-checked** (Lean 4 / Mathlib, no `sorry`, standard axioms only); **refereed proof** (a written proof with an independent referee report); **proved modulo a certified computation**; **computed, not certified**; **conjecture**; **heuristic**. Claims from the one unrefereed note (§4.5, §5.4) carry that note's own labels and are marked *unrefereed*.

---

## 1. Setting

Let $n\ge2$, $\zeta=e^{2\pi i/n}$, and let $D_L=D_L(r)$, $D_R=D_R(r)$ be the **closed** disks of radius $r$ centred at $-1$ and $+1$. Let $A(z)=-1+\zeta^{-1}(z+1)$ and $B(z)=1+\zeta^{-1}(z-1)$ be the clockwise rotations by $2\pi/n$ about the two centres. Define $a=A$ on $D_L$ and $a=\mathrm{id}$ off $D_L$, and likewise $b=B$ on $D_R$ and $b=\mathrm{id}$ off $D_R$. Since $A(D_L)=D_L$, $a$ and $b$ are bijections of $\mathbb C$. Put $GG_n(r)=\langle a,b\rangle\le\mathrm{Sym}(\mathbb C)$. It is a group of piecewise isometries, and its pieces are cut out by circles of radius $r$.

Orbits are non-decreasing in $r$ *as sets*. Finiteness of the group passes to smaller radii: if $GG_n(r)$ is finite, so is $GG_n(r')$ for every $r'\le r$ (refereed proof; machine-checked as `orbit_mono` and `finite_GG_of_le`). The proof works at the level of chains of moves applied to a point. No generator-preserving homomorphism between the groups at two radii exists. Hence
$$r_{\rm crit}(n)=\inf\{r:\ GG_n(r)\text{ infinite}\}=\sup\{r:\ GG_n(r)\text{ finite}\}$$
is well defined (`TDCSG.criticalRadius`, an `sInf`). For $r<1$ the group is finite. For $n\notin\{2,3,4,6\}$ it is infinite for large $r$ (paper, Theorem 1). For $\operatorname{lcm}\in\{1,2,3,4,6\}$ it is finite for all radii (refereed proof; machine-checked as `finite_GG`).

## 2. Arithmetic structure

Along any word, the composite of the rotations actually applied to a point is a map $z\mapsto\zeta^jz+t$ with $t\in(1-\zeta)\mathbb Z[\zeta]$. Write $\mathcal T(r)$ for the set of these *word maps*. For $\varphi(n)=4$, $\mathbb Q(\zeta)$ is a CM quartic field over the real quadratic field $K^+=\mathbb Q(\zeta)^+$. Let $\sigma$ be a Galois automorphism with $\sigma(\zeta)=\zeta^k$, $k\ne\pm1$. Then $x\mapsto(x,\sigma x)$ embeds $\Lambda=\mathbb Z[\zeta]$ as a lattice in $\mathbb C\times\mathbb C$, the product of physical and internal space. The translation parts satisfy $|t|\le2+2r$. So $\mathcal T(r)$ is finite iff $\sup|\sigma(t)|<\infty$, and finiteness of $\mathcal T(r)$ implies finiteness of the group (refereed proof). Thus an orbit is finite iff its Galois-conjugate image is bounded: orbits are cut-and-project sets of $\Lambda$, but with a window that depends on $r$ and is not fixed.

Computed evidence, not certified, says the window is not a simple fixed shape. For $n=5$ the internal hull of orbits at $r^2=r_c^2-\delta$ is a round disk of radius $\approx6.49/\delta$. The orbit fills a fractal part of that disk, and the filling fraction decreases as $\delta\to0$. The full-plane group $\Gamma=\langle A,B\rangle\subset\mu_n\ltimes\mathbb Z[\zeta]$ is non-discrete exactly when $n\notin\{2,3,4,6\}$, and it then contains arbitrarily small translations (refereed proof). $GG_n(r)$ is its cut-down to two disks: $GG_n(r)z\subseteq\Gamma z\cap(D_L\cup D_R)$. Finiteness is the statement that the disks cut the dense group down to a bounded internal window. The fundamental units $\varphi^{3}$ (for $n=5,10$), $1+\sqrt2$ and $2+\sqrt3$ act on $\Lambda$ by contracting one coordinate and expanding the other. They govern the observed self-similarity.

## 3. The problem

Write $r_c(n)$ for the closed form:

| $n$ | $r_c^2$ | $r_c$ | minimal polynomial of $r_c^2$ |
|---|---|---|---|
| 5 | $3+\varphi$ | 2.148961 | $x^2-7x+11$ |
| 8 | $10-5\sqrt2$ | 1.711412 | $x^2-20x+50$ |
| 10 | $4-\varphi$ | 1.543362 | $x^2-7x+11$ |
| 12 | $40-22\sqrt3$ | 1.376547 | $x^2-80x+148$ |

**Problem.** Prove $r_{\rm crit}(n)=r_c(n)$, i.e. that $GG_n(r)$ is finite for every $r<r_c(n)$. The Lean propositions are `CriticalRadiusEqFive`, `…Eight`, `…Ten` and `…Twelve` (open).

### 3.1 Proved: infinitude for $r\ge r_c$ (machine-checked)

`infinite_GG_five`, `infinite_GG_eight`, `infinite_GG_ten` and `infinite_GG_twelve` give $1\le r_{\rm crit}(n)\le r_c(n)$ for all four $n$. Each also has a refereed written proof. Every disk test is exact, and the closed-disk convention is used at the points that are tight at $r_c$. Validity at $r_c$ persists for $r>r_c$ because the disks only grow.

- **$n=5$ (also $n=10$).** Let $E=\zeta-\zeta^2$, with $|E+1|^2=3+\varphi$. The chord $[-E,E]$ through $0$ is split at $\pm\varphi^{-1}E$ and $\pm\varphi^{-3}E$. Three explicit words, $a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}$, $ababb$ and $abab^{-1}a^{-1}b^{-1}$, act on three closed sub-segments as translations. Together they induce the rotation $t\mapsto t+2\varphi^{-1}\pmod 2$ of the chord, so the orbit of $0$ is infinite. The endpoints are lattice points on the boundary circles. $r_c$ is also the radius at which the lens corners $\pm i\sqrt{r^2-1}$ become the lattice points $\pm(\zeta-\zeta^{-1})$. For $n=10$ the same mechanism works with the words $bba^{-1}b^{-1}$, $aba^{-1}a^{-1}$ and $aaab^{-1}b^{-1}b^{-1}$ on the chord $\{s\zeta^4:|s|\le\sqrt5\}$. The rotation number there is $1/(\varphi+2)$.
- **$n=8$ (also $n=12$).** The point $p^\ast=-1+(2+i)(1-\zeta)$ lies on $\partial D_L$ exactly at $r_c$, since $|p^\ast+1|^2=5|1-\zeta|^2$. A finite family $\mathcal F$ of partial isometries of a chord through $p^\ast$ is realized by explicit words: 31 words of length $\le12$. $\mathcal F$ is closed under conjugation by the rescaling $t\mapsto\varepsilon t$ about $p^\ast$, $\varepsilon=\sqrt2-1$. Hence the orbit of $p^\ast$ contains $p^\ast+4i\varepsilon^{k+1}$ for all $k\ge0$. For $n=12$, $p^\ast=(2-\sqrt3)(1-2i)$, the family has 30 words of length $\le28$, and $\varepsilon=2-\sqrt3$. The closure data are checked by kernel reduction (`decide +kernel`). These closed forms were derived in the paper from the assumption that a limit point lies on a disk boundary. The proofs here do not use that assumption.

### 3.2 Proved: finiteness up to explicit radii (proved modulo a certified computation)

**Certificate theorem (refereed proof; Lean has it only as the hypothesis `CutSetCertificate n`).** Fix $r$. Let $K$ be a finite union of closed arcs of circles of radius $r$ such that:
- (C1) $\partial D_L\cup\partial D_R\subseteq K$;
- (C2) $A^{\pm1}(K\cap D_L)\subseteq K$ and $B^{\pm1}(K\cap D_R)\subseteq K$;
- (C3) no carrying circle other than $\partial D_p$ is tangent to $\partial D_p$;
- (C4) every endpoint of a maximal arc that lies on $\partial D_p$ is the endpoint of an arc of $K$ entering $\operatorname{int}D_p$ there.

Then $GG_n(r)$ is finite, and by monotonicity so is $GG_n(r')$ for every $r'\le r$.

The proof shows that the singular set of $K$ is finite and invariant. Every group element then permutes the cells of the resulting decomposition by isometries, and there are at most $n$ isometries per pair of bounded cells. The natural candidate is the cut set $K(r)$, the closure of the two boundary circles under the generators. It is computed by a worklist closure.

**How the certificates are produced and checked.** A generator (`tdcsg-orbit certify`, an executable written in Lean) computes $K(r)$. Circle centres lie in $\mathbb Z[\zeta]$, and arc endpoints are symbols naming the intersection of two lattice-centred circles. All disk and tangency tests, equality of points (including triple points), and cyclic order along a circle are decided exactly by signs in quadratic towers over $K^+$. A double-precision filter with rigorous running error bounds is used only when it decides. A separate checker (`check-certificate`) reads only the certificate file and verifies (C1)–(C4). It shares only the exact-arithmetic layer with the generator, and it uses no floating point. Several things agree with it:
- The certificates at the refereed radii agree with independent re-implementations: identical arc sets for $n=5$; identical counts for $n=10$; and for $n=8,12$, floating-point closures with exact tie-breaking whose invariants all agree.
- The four deepest certificates were regenerated byte for byte and re-checked in an independent verification.
- Certificates are deterministic and recorded with SHA-256 checksums.

The checker is a tested program, not a formally verified one. Its correspondence with the Lean predicate `TDCSG.ExistsCertificate` is by inspection of definitions.

| $n$ | refereed range (independently reproduced) | deepest certified $r_*$ ($r_*^2=r_c^2-\delta$) | certificate size | open window $r_c-r_*$ |
|---|---|---|---|---|
| 5 | $\delta=1/10$, $r\le2.125567$ | $\delta=1/55$, $r_*=2.144727$ | $2.19\cdot10^6$ circles, $1.19\cdot10^7$ arcs | 0.004235 |
| 8 | $\delta=1/7$, $r\le1.669154$ | $\delta=1/36$, $r_*=1.703278$ | $5.8\cdot10^5$ circles, $6.5\cdot10^6$ arcs | 0.008135 |
| 10 | $\delta=1/16$, $r\le1.522979$ | $\delta=1/47$, $r_*=1.536454$ | $4.2\cdot10^5$ circles, $3.9\cdot10^6$ arcs | 0.006908 |
| 12 | $\delta=1/20$, $r\le1.358264$ | $\delta=1/180$, $r_*=1.374528$ | $1.08\cdot10^6$ circles, $5.9\cdot10^6$ arcs | 0.002019 |

The paper's numerical estimate for $n=10$, $1.543357$, lies inside the open window. No single computation can close the windows. The cut set grows like a power of $\delta^{-1}$: for $n=5$, roughly $\times20$ in circles and $\times35$–$40$ in arcs per factor $\varphi^3$ in $\delta$. Its internal extent satisfies $\delta\cdot\max|\sigma(c)|\approx19$.

## 4. The reduction obtained for $n=5$, and what transfers

Throughout, $\varepsilon=\varphi^{-3}=2\varphi-3$. It is a unit of norm $-1$ with $\sigma(\varepsilon)=-\varphi^3$. The levels are $r_k^2=3+\varphi-\varepsilon^k/10$.

**4.1 Non-norm radii (refereed proof).** Call $r$ a *non-norm radius* if $r^2\in K^+$ but $r^2\ne|w|^2$ for every $w\in\mathbb Q(\zeta)$. This holds, for example, when $\sigma(r^2)<0$, or when $v_2(r^2)$ is odd. Every level $r_k$ is a non-norm radius. At such radii:
- no point of $\mathbb Q(\zeta)$ lies on a lattice-centred circle of radius $r$;
- no two such circles are tangent;
- no three meet in a point.

Consequently (C3) and (C4) hold automatically, and $GG_5(r)$ is finite iff the closure $K(r)$ terminates. Equivalently, the word maps realized at lattice points are bounded in internal space (lattice window criterion). A finite bootstrap reduces that condition at one radius to finitely many lattice orbits. Since finiteness is monotone, (B) is *equivalent* to termination along $r_k\uparrow r_c$. This is a reformulation, not a reduction to something easier. All of this transfers verbatim to $n=8,10,12$.

**4.2 Critical points (refereed proof).** $3+\varphi$ has norm 11, a split prime, so $|w|^2=3+\varphi$ has exactly 20 solutions in $\Lambda$. The lattice points on $\partial D_L\cup\partial D_R$ at $r_c$ are 38 points (the two lens corners lie on both circles). They fall into 10 classes under $\{\pm z,\pm\bar z\}$. The tight points $\pm E,\pm\bar E$ of the critical words form one class, and the lens corners another. A lattice-centred circle of radius $r_c$ is tangent to $\partial D_p$ only at a critical point. For $n=8$ there are 32 critical points in 8 classes (refereed). The engine's enumeration, computed, gives 38 in 10 classes for $n=10$ and 48 in 12 classes for $n=12$.

**4.3 Relative certificates (refereed proof).** Let $W$ be a union of disjoint small compact convex windows about the critical points, each bounded by four arcs of radius $r_c$. A *restricted closure* is a finite union of arcs of radius $r_c$ that:
- contains $\partial D_L$, $\partial D_R$ and $\partial W$;
- is closed under the four rotations applied to the parts of arcs inside the respective disk and outside $\operatorname{int}W$.

It is computed **at $r_c$**. There $3+\varphi$ is a norm, so tangencies and triple points occur, and they are decided exactly. Theorem: if a restricted closure exists, with $F$ bounded faces outside $W$, then for **every $r<r_c$ simultaneously**, every chain whose intermediate points avoid $W$ has at most $1+100F$ endpoints. The key step is that every non-trivial move at radius $r<r_c$ is a move inside an open disk of radius $r_c$. Corollary:
$$|O_r(z)|\le\beta_W\max\bigl(1,\sup_x|O_r(x)\cap W|\bigr).$$
So $GG_5(r)$ is finite iff orbits visit $W$ boundedly. The induced pseudogroup on $W$ is generated by one finite set of itinerary words, the same for all $r<r_c$, and its partition has constant combinatorics on some interval $(r_c-\eta,r_c)$.

Status of the window computations at $r_c$ (nine window sizes, circumradius $0.292$ down to $0.0166$):
- the largest window is certified by an independent interval-arithmetic checker (`mpmath.iv` trusted);
- the next two are computed by two independent floating-point programs, not certified;
- the remaining six are computed by one program only.

$F$, and hence $\beta_W$, was not computed.

**4.4 From (B) to (R-bulk) and (R-core) (refereed proof).** Two statements together imply (B):
- **(R-bulk)**, about the critical system alone: restricted orbits at $r_c$ avoiding windows $W^{(j)}$ are bounded, along some sequence of window sizes $\to0$;
- **(R-core)**: for some $C$ and $k_0$, $\sup_x|O_{r_k}(x)\cap\bigcup_P\overline B(P,C\varepsilon^k)|<\infty$ for every $k\ge k_0$.

The pair is at least as strong as (B). Whether (B) implies (R-bulk) is not known. The $n=8$ analogue is Conjecture S (refereed implication S $\Rightarrow$ finiteness for $n=8$): (S1) restricted orbits at $r_c$ avoiding small windows about the 32 critical points are finite, and (S2) the innermost induced pseudogroup renormalizes exactly along one geometric sequence of radii.

**4.5 Further reduction to the four tight points (*unrefereed* note `sharp-lower-bound-limit-system.md`, with its labels).**
- *Proved modulo an exact finite computation* (skeleton computation; signs exact, margins in 50-digit arithmetic with a factor 3.6 to spare). For the nine non-tight classes, with $C=3/10$ and $k\ge4$, every first return to the core is a *linear* germ $X\mapsto\zeta^jX$ in zoomed coordinates. This holds for all points, not only lattice points. Hence (R-core) is equivalent, up to a factor 190, to (R-core-t), its restriction to the tight cores at $\pm E,\pm\bar E$.
- *Certified* (the note's label): restricted closures with windows **only** at the four tight points exist for nine window sizes. The two largest are VALID under the interval-arithmetic checker and a second checker, both adapted to four windows by the note's author. The other seven are computed by one program. Consequently, for every $r<r_c$, $GG_5(r)$ is finite iff its orbits meet four small windows at $\pm E,\pm\bar E$ in uniformly boundedly many points.
- *Proved*: (R-bulk-t) and (R-core-t), the tight-class versions, imply (B).

**4.6 Diophantine lune lemma (refereed proof).** Let $P$ be a tight point with $|P-p|^2=3+\varphi$, and let $\ell_P(y)=2\operatorname{Re}((y-P)\overline{(P-p)})$. Then exactly
$$10(|y-p|^2-r_k^2)=\bigl(10\ell_P(y)+\varepsilon^k\bigr)+10|y-P|^2 .$$
The bracket is $\equiv\varepsilon^k\pmod{10}$, so its norm is $\equiv\pm1\pmod{10}$ and it is bounded below by $1/|\sigma(\cdot)|$. Hence, for lattice points with
$$10|y-P|^2\bigl(20|\sigma y-\sigma P||\sigma P-p|+\varphi^{3k}\bigr)<1,$$
the disk test equals the tangent half-plane test: no lattice point lies in the thin lune. In zoomed coordinates $y=P+\varepsilon^k\eta$, the substitution $\Psi_P(y)=P+\varepsilon(y-P)$ carries membership at level $k$ to level $k+1$ exactly. Every isometry $g$ with lattice translation satisfies $g\Psi_P=\Psi_{g(P)}g$. The hypothesis is met, for $|\eta|,|\sigma\eta|\le1$, only from level $k_0=4$, and for $\le2$ from $k_0=6$. At levels $0$–$2$ only $y=P$ satisfies it in the tested window, so any induction built on the lemma needs a base deeper than every certified level. The certified level is about 1.3: $\delta=1/55$ lies between levels 1 and 2. The unrefereed note extends the lemma to all 38 critical points with one constant ($20|\sigma w|=30.87$).

## 5. What fails, and what is observed (exact data)

**5.1 The cut set has no stable limit** (evidence, $n=5$ and $n=8$). Rescaled about a critical point, $K(r)$ refines everywhere. Already at level 0, 1 743 distinct arcs pass within rescaled distance 1.5 of $0$, in many directions. The renormalizable objects are orbits and first-return germs, not the arc arrangement. A similarity of ratio $\varepsilon$ cannot map radius-$r$ arcs to radius-$r'$ arcs with $r'\approx r$. Any 2-D renormalization can therefore be at best combinatorial and asymptotic, with curvature errors of size $O(\varepsilon^{2k})$ over regions of size $\varepsilon^k$.

**5.2 Literal $\varphi^{-3}$ self-similarity of core orbits is false** (refuted; exact; refereed and confirmed by independent exact implementations, including the referee's code and the repository engine). Take $P=(0,1,2,2)$, $\eta=(-3,-3,0,-5)$ and $P'=(-2,-1,-2,0)$, $\eta'=(-8,-6,-1,-11)$, in the basis $1,\zeta,\zeta^2,\zeta^3$, and put $y=P+\varepsilon^k\eta$.
- At level 2 ($10r^2=17+18\varphi$), $y_A=(-55,-54,2,-87)$ and $y_B=(-146,-111,-23,-199)$ lie in **one** orbit of 102 425 points.
- At level 3 ($10r^2=85-24\varphi$), $y_A=(233,234,2,379)$ lies in an orbit of 258 339 points and $y_B=(608,465,87,843)$ in a **different** orbit of 1 315 339 points.

Both points violate the lune hypothesis. On the 126 core points that satisfy it at level 2, the partitions at levels 2 and 3 agree (computed, not reproduced). The unrefereed note finds the failure at the tight points at every tested level pair $k\to k+1$, including $3\to4$ and $4\to5$ (*refuted*, exact). First-return sets agree in at most 14 of 811 cases, and in 0 of 2 436, 2 564, 84 and 12 in the other samples. Applying the four symmetries does not repair this. Example: $(E,\eta=(-3,-1,-1,-3))$ has excursions of 21 066, 16 128 171 and 3 473 926 points at levels 3, 4, 5. Its first-return sets have 6, 46 and 6 elements, with levels 3 and 5 equal and level 4 different. Levels 1–3 were re-checked by an independent program.

**5.3 A fixed finite word set gives a trivial limit** (*unrefereed*, *proved*). In zoomed coordinates the induced system of the fixed word set of a certified window converges to a pseudogroup of rotations on half-planes, whose orbits have at most $5\cdot38=190$ points. Every *non-linear* return to the level-$k$ core is a concatenation of at least $\lceil(\varphi^{3k}/2C-6)/T_W\rceil$ first returns to the window, by a norm argument. A useful limit object must therefore be a limit of first-return maps with words of unbounded length.

**5.4 Period two with ratio $\varphi^{-6}$** (*unrefereed*, *conjecture* with exact evidence).
- Agreement of first-return sets between levels $k$ and $k+2$ rises with $k$: 9.5% and 23% ($1\to3$); 62% and 64% ($2\to4$); 100% ($3\to5$, on all $12+117$ tight points that fit in memory at level 5).
- On 1 784 sampled core points whose level-$k$ excursion has no lune point within zoomed distance 3, the sets at $k$ and $k+2$ agree without exception ($k=1,2,3$). With period one, the same criterion fails on 12 of 726 points.
- The infinite orbit of $E$ at $r_c$ was computed to $4\cdot10^7$ points. Near $E$, it is mapped into itself by $y\mapsto E+\varphi^{-6}(y-E)$ on all 3 661 tested points within distance 1 of $E$. Under $\varphi^{-3}$, 22% of points fail. The invariance begins to fail between distance 1 and 1.2.
- For $n=8$, independently, floating-point sampling shows the same parity. Sampled germ sets at $p^\ast$ agree under $\tau\mapsto\varepsilon^2\tau$ for levels $2\to4$ (27 of 27) and $3\to5$ (20 of 23), but only 10 match under $\tau\mapsto\varepsilon\tau$.

**5.5 Bounded window visits** (computed, exact; levels 1–2 reproduced by the referee). For $n=5$, the full orbits of 798 normalized core points were computed. The maximal number of visits to the level-$k$ core per orbit is 1 578, 1 352 and 1 546 at levels 1, 2 and 3, while the largest orbit grows from $7.2\cdot10^4$ to $1.54\cdot10^7$ points (×13–16 per level). For $n=8$, sampled orbit counts in the innermost window stay at 188, 224 and 223 for $m=2,4,6$. This is evidence for the uniform form of (R-core), not a supremum over all points.

**5.6 Computation sizes grow in steps** (computed). Certificate sizes are nearly constant over ranges of $\delta$ and jump in between, roughly one jump per factor of the unit in $\delta$. For $n=12$, for example, there are 37 180, 37 840 and 38 016 circles from $\delta=1/20$ to $1/40$, then a jump to 470 284. Restricted closures behave the same way as a function of window size. Orbit-of-0 thresholds accumulate at $r_c$ with gap ratios $4.167, 4.220, 4.233\to\varphi^3$ ($n=5$) and $2.4065, 2.4110, 2.4129\to1+\sqrt2$ ($n=8$).

**5.7 A possible explanation of period two** (heuristic, unverified). $\varphi^3$ has norm $-1$. The physical rescaling $x\mapsto\varepsilon x$ therefore acts on the internal coordinate as multiplication by $\sigma(\varepsilon)=-\varphi^3$: a point reflection composed with expansion. The level radii see the sign, since $\sigma(r_k^2)=4-\varphi-\sigma(\varepsilon)^k/10$ alternates in sign for large $k$. Only $\varepsilon^2$ preserves the orientation of internal space. If the effective internal window is not centrally symmetric, one would expect exact renormalization only under $\varepsilon^2$. The heuristic predicts period two for $n=8$ ($\sqrt2-1$, norm $-1$) and $n=10$ ($\varphi^{-3}$, norm $-1$), and period one for $n=12$ ($2-\sqrt3$, norm $+1$). The $n=8$ observation of §5.4 predates the heuristic and agrees with it. The tests for $n=10$ and $n=12$, and an independent referee assessment of the limit-system note, are **pending**: no report on that note exists yet.

## 6. Questions for specialists

1. **Existing renormalization theorems.** Is there a renormalization theorem for planar piecewise rotations or isometries with quadratic-irrational parameters (5-, 8-, 10- and 12-fold) that applies to the first-return map on a neighbourhood of a tight point at $r=r_c$, or just below it? Candidates include the self-similar domain-exchange results of Adler–Kitchens–Tresser, Kouptsov–Lowenstein–Vivaldi, Lowenstein–Hatjispyros–Vivaldi and Akiyama–Brunotte–Pethő–Steiner, the $\pi/7$ work of Goetz–Poggiaspalla and Lowenstein–Kouptsov–Vivaldi, Schwartz's PET renormalization and Hooper's corner-percolation PETs. *An answer would give* either step (I)–(II) of the route (a limit system with a proved renormalization) or a precise reason why the two-generator, disk-gated setting falls outside these frameworks.
2. **Off-critical renormalization with curved cuts.** Here a one-parameter family of piecewise isometries has discontinuity curves that are circles of fixed radius $r$. As $r\uparrow r_c$ it converges to a system with an exact 1-D renormalization on a chord (golden rotation for $n=5,10$; a self-similar pseudogroup for $n=8,12$). Is there a framework for asymptotic self-similarity under rescaling by a unit, with curvature corrections of relative size $O(\varepsilon^k)$ controlled uniformly, that yields stability of the combinatorics from some level on? *An answer would give* the matching step (III) with an explicit $k_0$. The lune lemma provides the needed Diophantine margin only for lattice points with bounded normalized internal coordinate.
3. **Uniform bounds on returns.** Finiteness below $r_c$ is equivalent to bounded returns to four small windows at $\pm E,\pm\bar E$ (unrefereed reduction; the 38-window version is refereed). Is there a known mechanism that yields return-count bounds uniform across scales? Possibilities include a Lyapunov or height function in internal space, a substitution or odometer structure on first-return words (cf. the triadic odometer of Adler–Kitchens–Tresser), and bounded-distortion arguments. *An answer would give* (R-core-t) in its uniform form. The data (§5.5) show visit counts near 1 500 while orbits grow ×14 per level.
4. **Period two.** Is renormalization with ratio $\varepsilon^2$, when the fundamental unit has norm $-1$ and acts on internal space with a reflection, a known phenomenon in this literature (round-off rotations, quadratic PETs, model sets with asymmetric windows)? *An answer would give* support for, or a counterexample to, the heuristic of §5.7, and tell us whether to build the induction on $\Psi_P^2$ from the start.
5. **Type of the transition.** Orbits are model sets of $\mathbb Z[\zeta]$ with a radius-dependent window that is not fixed. Infinitude switches on when lattice points ($\pm E$, $\pm\bar E$, the lens corners, or $p^\ast$) reach a boundary circle. Is this a known type of bifurcation? Comparable settings include a window touching a singular point, critical parameters of second-order digital filters with overflow (Chua–Lin), unbounded orbits in outer billiards on kites (Schwartz), and parameter boundaries of renormalizable PET families (Hooper, Schwartz). *An answer would give* a model in which "finite below, infinite at" has already been proved.
6. **Exact self-similarity at $r_c$.** Is there a known technique for proving that the infinite orbit of $E$ at $r_c$ is locally invariant under $y\mapsto E+\varphi^{-6}(y-E)$, by exhibiting a finite set of words that conjugates the dynamics near $E$ at two consecutive even scales (a 2-D analogue of golden induction)? Would such an exact statement at $r_c$, combined with the lune lemma, be expected to yield (R-bulk-t)? *An answer would give* the single-system half of the reduction, which needs no limit in $r$.
7. **A Lagrange-type finiteness theorem.** Boshernitzan–Carroll show that interval exchanges with lengths in a quadratic field have finitely many descendants up to rescaling. Is there a planar or pseudogroup analogue for systems whose cut data lie in $K^+$ but whose cuts are circular arcs of radius $r$ with $r^2\in K^+$? *An answer would give* a finiteness statement for the family of renormalized first-return systems, which is what the induction over levels needs.
8. **Generic points.** The lattice window criterion needs the bound at *all* lattice points, including those of huge internal coordinate. Equivalently, every face of the circle arrangement must contain a lattice point of controlled internal size. Is there a known lower bound on the inradius of faces of an arrangement of radius-$r$ circles centred in a bounded internal window of $\mathbb Z[\zeta]$, polynomial in the window size? *An answer would give* step 4 of the reduction: passage from bounded normalized lattice points to all points.

## 7. What we can supply

- Exact data: the critical points and their classes for all four $n$; the infinite-orbit words and the closure families (31 words for $n=8$, 30 for $n=12$, with exact domains); cut-set certificates for every row cited, with SHA-256 checksums and deterministic regeneration commands; restricted-closure outputs at $r_c$; exact orbit and first-return data at levels 1–5 for $n=5$.
- The Lean development: definitions, monotonicity, infinitude at $r\ge r_c$ for $n=5,8,10,12$, the certificate predicate and the reduction from certificates to finiteness.
- An exact engine (`tdcsg-orbit`, written in Lean): orbits, threshold sweeps, cut-set certificates with an independent checker, and relative certificates. The engine port of relative certificates is being written up.

Repository notes by topic (paths relative to the repository root):
- Results and status of every claim: `README.md`; programme and conventions: `notes/overview.md`.
- Infinitude and initial finiteness: `notes/proofs/critical-radius-n5.md`, `-n8.md`, `-n10.md`, `-n12.md`; certificates: `notes/certificates.md`.
- Reductions: `notes/proofs/sharp-lower-bound-n5.md` (non-norm radii, lattice window criterion, lune lemma), `sharp-lower-bound-n8.md` (nested windows, Conjecture S), `sharp-lower-bound-combined.md` (relative certificates, (R-bulk)/(R-core)), `sharp-lower-bound-limit-system.md` (unrefereed: tight-point reduction, period two).
- Foundations: `notes/proofs/boundary-contact.md` (monotonicity, boundary contact), `theorem1-converse.md` (finiteness for $\operatorname{lcm}\in\{1,2,3,4,6\}$), `analytic-radius.md` and `regularity-scale.md` (invariant functions; $r_A(n)=\sec(\pi/n)<r_c$).
- Referee reports: `notes/proofs/referee-report-*.md`. Lean statements: `TDCSG/Statements.lean`, `TDCSG/CriticalRadius/Statements.lean`.

## 8. References

Bibliographic details were checked against publisher, Project Euclid, zbMATH/MaRDI or arXiv records, except where marked.

1. R. A. Hearn, W. Kretschmer, T. Rokicki, B. Streeter, E. Vergo, *Two-Disk Compound Symmetry Groups*, arXiv:2302.12950.
2. R. L. Adler, B. Kitchens, C. Tresser, Dynamics of non-ergodic piecewise affine maps of the torus, *Ergodic Theory Dynam. Systems* (2001), doi:10.1017/S0143385701001468. (Volume and pages not verified.)
3. K. L. Kouptsov, J. H. Lowenstein, F. Vivaldi, Quadratic rational rotations of the torus and dual lattice maps, *Nonlinearity* 15 (2002), no. 6, 1795ff. (End page not verified.)
4. J. H. Lowenstein, S. Hatjispyros, F. Vivaldi, Quasi-periodicity, global stability and scaling in a model of Hamiltonian round-off, *Chaos* 7 (1997), 49–66.
5. S. Akiyama, H. Brunotte, A. Pethő, W. Steiner, Periodicity of certain piecewise affine planar maps, *Tsukuba J. Math.* 32 (2008), no. 1, 197–251; arXiv:0704.3674.
6. A. Goetz, G. Poggiaspalla, Rotations by $\pi/7$, *Nonlinearity* 17 (2004), no. 5, 1787–1802, doi:10.1088/0951-7715/17/5/013.
7. J. H. Lowenstein, K. L. Kouptsov, F. Vivaldi, Recursive tiling and geometry of piecewise rotations by $\pi/7$, *Nonlinearity* 17 (2004), no. 2, 371ff. (End page not verified.)
8. P. Ashwin, X.-C. Fu, On the geometry of orientation-preserving planar piecewise isometries, *J. Nonlinear Sci.* 12 (2002), no. 3, 207–240.
9. M. Boshernitzan, C. R. Carroll, An extension of Lagrange's theorem to interval exchange transformations over quadratic fields, *J. Anal. Math.* 72 (1997), 21–44.
10. R. E. Schwartz, *Outer Billiards on Kites*, Annals of Mathematics Studies 171, Princeton University Press, 2009.
11. R. E. Schwartz, *The Octagonal PETs*, Mathematical Surveys and Monographs 197, American Mathematical Society, 2014.
12. W. P. Hooper, Renormalization of polygon exchange maps arising from corner percolation, *Invent. Math.* 191 (2013), no. 2, 255–320; arXiv:1105.6137.
13. L. O. Chua, T. Lin, Chaos in digital filters, *IEEE Trans. Circuits Syst.* 35 (1988), no. 6, 648–658.
14. M. Baake, U. Grimm, *Aperiodic Order, Vol. 1: A Mathematical Invitation*, Encyclopedia of Mathematics and its Applications 149, Cambridge University Press, 2013.
