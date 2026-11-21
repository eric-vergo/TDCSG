# Referee report: `sharp-lower-bound-combined.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: a certified bulk bound at the critical radius, and the reduction to the critical windows". Companions consulted: `sharp-lower-bound-n5.md`, `sharp-lower-bound-n8.md`, `boundary-contact.md` (Theorems 3.1, 3.4), `theorem1-converse.md` (Proposition 4.2), and the programs in the session scratch directory `sharp2/`.

## Summary

The note does not prove (B), and says so plainly. Its main new result is the relative-certificate theorem (Theorem 4.2), which turns one finite window-clipped closure at $r_c$ into an excursion bound for every $r<r_c$ at once. The theorem is **correct**. The point that looked delicate is how a certificate at $r_c$ controls chains at a smaller $r$. The proof never compares the two systems' partitions. It uses only an inclusion of chain relations (Lemma 3.3): every non-trivial step at radius $r$ is a strict step at $r_c$, and a point in the lune $D_p(r_c)\setminus D_p(r)$ just has one fewer available move. Since $R^*_W$ is a union over *all* strict chains, nothing more is needed.

The computational inputs are honestly labelled as computed, not certified. For the largest window I re-verified the certificate with my own interval-arithmetic checker, so that row is now certified, subject to the caveats in §3. The refutation of exact rescaling is reproduced exactly, with my own code and with the repository engine. Table 6.1 is reproduced exactly at levels 1 and 2. I found no fatal issues and no gaps beyond the open problem the note itself identifies. The issues below are presentation, status labelling, and one weakness in `chk.py`'s numerical error control.

## 1. Verdicts

| claim | verdict |
|---|---|
| (1) Lemma 2.1: 38 critical points of $\Lambda=\mathbb Z[\zeta]$ on $\partial D_1\cup\partial D_2$, 10 classes, tangency only at critical points | **correct** (cosmetic issue 7) |
| (2a) Lemmas 3.3, 3.4 and Theorem 4.2 (relative certificate, bound $1+100F$, no (C3)/(C4) needed) | **correct after minor fixes** (issues 6, 10) |
| (2b) Theorem 5.2: row $w=(0,2,-1,0)$ | **certified** by the referee's interval-arithmetic recheck (caveats in §3) |
| (2b) Theorem 5.2: rows $(5,-1,4,0)$ and $(-3,4,-4,0)$ | **computed-not-certified** (two independent floating-point implementations; not re-run by me) |
| (2b) Theorem 5.2: the six smaller-window rows | **computed-not-certified** (`rcut.c` alone; log numbers match the table) |
| (3) Corollary 4.3, Propositions 4.4, 4.5 | **correct after minor fixes** (issues 4, 9) |
| (4) Refutation of exact level-independence (levels 2 → 3) | **correct**, reproduced exactly with two implementations |
| (5) Proposition 6.3: (R-bulk) + (R-core) ⇒ (B) | **correct**; the framing should be adjusted (issue 5) |
| (6) Computational claims | see (2b); `chk.py` is independent of `rcut.c`'s decisions but has no rigorous error control (issue 3) |
| (7) Evidence: visit counts 1578, 1352, 1546; agreement 93.5% → 97.6% | **correctly labelled as evidence**. Levels 1 and 2 reproduced exactly; level 3 and the agreement figures not reproduced |
| (8) Title and status | Status is correct and clear that (B) is open. The **title overclaims** "certified" (issue 1) |

## 2. Detailed review

### Claim (1): Lemma 2.1

- **Lattice and points.** The lattice is $\Lambda=\mathbb Z[\zeta]$ itself, not $(1-\zeta)\Lambda$ or a translate. The critical points are $p+w$ with $p=\pm1\in\Lambda$ and $w\bar w=3+\varphi$.
- **Item 1.** $N(3+\varphi)=11$ is prime and splits in $\Lambda$, so $(3+\varphi)=\mathfrak p\bar{\mathfrak p}$ with $\mathfrak p\ne\bar{\mathfrak p}$. Therefore $(w)\in\{\mathfrak p,\bar{\mathfrak p}\}$. A unit of modulus 1 is $\pm\zeta^j$ (Kronecker's theorem, as argued in the note). This gives exactly 20 elements. I confirmed that a search over $[-8,8]^4$ finds exactly 20, with coefficients bounded by 2.
- **Item 2.** There are 38 points ($40-2$). The lens corners are $\pm(\zeta-\zeta^{-1})$; note $|\zeta-\zeta^{-1}|^2=2+\varphi=r_c^2-1$.
- **Item 3.** Under $\{z,-z,\bar z,-\bar z\}$ there are 10 classes: one of size 2 and nine of size 4. Every row of Table 2.1 is correct: the value, the class size, and the exact $|y-1|^2$ with its comparison to $3+\varphi$. The minimal distance between critical points is $\varphi^{-1}$.
- **Item 4.** This concerns *every* lattice-centred circle of radius $r_c$, hence every circle of $K'$, since all of $K'$'s centres are lattice points. Tangency with $\partial D_p$ must be external, with $|c-p|^2=4(3+\varphi)$. Because 2 is inert in $\Lambda$, $c-p=2w$, and the tangency point is the critical point $p+w$. I confirmed by enumeration that all 20 solutions of $|d|^2=4(3+\varphi)$ in a box lie in $2\Lambda$.
- The `rcut.c` hard-coded list `CRIT` equals my independently computed set.

### Claim (2): Lemmas 3.3, 3.4, Theorem 4.2

**Definitions.**
- $W=\bigcup_P(P+W_0)$, with $W_0=\bigcap_{v\in\{\pm w,\pm\bar w\}}D(v,r_c)$ compact and convex.
- A window-avoiding chain is one whose intermediate points $z_1,\dots,z_{L-1}$ lie outside $W$.
- Condition 2 of Definition 4.1 asks that every non-degenerate component of $\alpha\cap D_S\setminus\operatorname{int}W$ is mapped into $K'$ by $S$. Here $\alpha$ is an arc of $K'$, $S\in\{A^{\pm1},B^{\pm1}\}$, and $D_S$ is the closed disk of radius $r_c$.
- $F$ is the number of bounded faces of $\mathbb C\setminus K'$ not contained in $W$.

All of these are precise.

**Lemma 3.3 (the crux).**
- Delete the trivial steps of an $r$-chain. Each remaining step is a rotation applied at a point of $D_p(r)\subset\operatorname{int}D_p(r_c)$, so it is a strict step.
- The remaining intermediate points are among the original intermediate points. A reduced intermediate point sits strictly between two non-trivial steps, so it equals some $z_i$ with $0<i<L$.
- Hence $R^{(r)}_W(x)\subseteq R^*_W(x)$. A point in the lune $D_p(r_c)\setminus D_p(r)$ is fixed by the generator at radius $r$. That is a deleted trivial step, not a discrepancy. So the "different partitions" worry does not arise.
- The remark that $\bigcup_{r<r_c}O_r(x)$ is the strict orbit is also right. A strict chain is an $r$-chain for $r=\max_i|z_{i-1}-p_i|<r_c$.

**Lemma 3.4.**
- The conditions defining a strict chain with intermediate points avoiding the closed set $W$ are open in the starting point. So are the distinctness of finitely many endpoints $g_i(x)$.
- The countable family of circles must include the (finitely many) circles of $K'$. It does, implicitly.
- Correct.

**Theorem 4.2, Step 1.** I checked it line by line.
- Let $y\in S(X)\cap(K'\setminus\operatorname{int}W)$. Then $y\in\operatorname{int}D_S$.
- If $y\notin W$, any arc of $K'$ through $y$ gives a non-degenerate component through $y$.
- If $y\in\partial W$, a boundary arc of $W_P$ through $y$ does. This uses $\partial W\subseteq K'$, together with the convexity and disjointness of the windows.
- Condition 2 for $S^{-1}$ then gives $S^{-1}y\in K'\cap X=\emptyset$, a contradiction.
- So the connected open set $S(X)$ misses $\partial W$, and lies either in $\operatorname{int}W$ or in one face $Y\subseteq\mathbb C\setminus W$. The reverse argument gives $S(X)=Y$.
- Correct.

**Step 2.**
- A face $Y$ and a rotation part $j$ determine the isometry $X_1\to Y$, because a translation cannot map a bounded set onto itself unless it is trivial.
- Per first step this gives at most $5F$ endpoints outside $W$, plus at most $4\cdot5F$ endpoints that enter $\operatorname{int}W$ at the last step. That is $25F$.
- With four first steps and the start, the total is $1+100F$. **The constant 100 is $4\times25$**, and it is correct (crude, but all that is used).
- No (C3)/(C4)-type conditions are needed. Strict chains use open disks, and generic points never lie on $K'$. Tangency points lie on $\partial D_S$ and so never in $\operatorname{int}D_S$, which is why the tangency rule of `rcut.c` (no image for a one-point intersection) is consistent with Definition 4.1.
- Closed disks enter only through Lemma 3.3, and correctly.

**Theorem 5.2** is Theorem 4.2 applied to the program outputs, labelled correctly as conditional. Its status per row is in the table above and in §3.

### Claim (3): Corollary 4.3, Propositions 4.4, 4.5

**Corollary 4.3.**
- Both directions hold. A finite group gives orbits of size at most $|G|$. Conversely, a uniform bound $\beta_W\max(1,N)$ on orbit sizes gives a finite group by `theorem1-converse.md` Proposition 4.2. I checked that this proposition is correctly stated and proved: the kernel is an intersection of finitely many subgroups of index at most $N$.
- Uniformity over orbits is the $\sup_x$. Uniformity over $r$ is not needed for the equivalence at a fixed $r$. Passing to (B) uses group monotonicity (`boundary-contact.md` Theorem 3.4).
- The proof needs a chain *starting in $O\cap W$*; see issue 4.

**Proposition 4.4.** In a shortest chain the intermediate points are distinct, and each of them is in $R^{(r)}_W(x)$. Hence the length is at most $\beta_W+1$, and the finite word set is independent of $r$. Correct. Words should carry their itinerary; see issue 9.

**Proposition 4.5.** The event list is complete for an arrangement of finitely many radius-$r$ circles with fixed centres together with fixed radius-$r_c$ curves:
- tangencies;
- triple points;
- a circle through a fixed vertex;
- tangency with a fixed arc;
- two test circles meeting on a fixed curve.

Each event is a non-trivial equation in $r$ with finitely many roots. The combinatorics are therefore constant on some $(r_c-\eta,r_c)$. Correct as a sketch; issue 9 asks for the standard isotopy step to be stated.

### Claim (4): the refutation

**Decoding.** Coordinates are in the power basis $(1,\zeta,\zeta^2,\zeta^3)$, so $E=(0,1,-1,0)=\zeta-\zeta^2$. The normalized point is $y=P+\varepsilon^k\eta$ with $\varepsilon=\varphi^{-3}=2\varphi-3$. The radius is $10r_k^2=30+10\varphi-\varepsilon^k$, which gives $17+18\varphi$ at $k=2$ and $85-24\varphi$ at $k=3$. The disks are closed.

**My own exact BFS** (`refcomb/cex_ref.py`, new $\mathbb Z[\zeta]$ code, `refcomb/ref_zeta.py`):
- Both $P=(0,1,2,2)$ and $P'=(-2,-1,-2,0)$ are critical. $|\eta|=0.1459$, $|\sigma\eta|=6.854$, $|\eta'|=0.2252$, $|\sigma\eta'|=14.729$.
- **Level 2:** $y_A=(-55,-54,2,-87)$ and $y_B=(-146,-111,-23,-199)$. The orbit of $y_A$ is complete with **102 425** points and contains $y_B$, and conversely.
- **Level 3:** $y_A=(233,234,2,379)$ and $y_B=(608,465,87,843)$. The orbit of $y_A$ is complete with **258 339** points and does not contain $y_B$. The orbit of $y_B$ is complete with **1 315 339** points and does not contain $y_A$.

**Repository engine** (`tdcsg-orbit orbit -n 5 --r2 re:7/2,9/5` and `--r2 re:61/10,-12/5`, read-only): it gives the same four orbit sizes, 102 425 / 102 425 / 258 339 / 1 315 339, all decided exactly.

**Lune quantities** (my computation): 2.52 and 12.87 at level 2; 0.595 (A) and 3.04 (B) at level 3. These agree with the note.

The refutation is **confirmed**. Membership was decided within resources; no caps were hit.

### Claim (5): Proposition 6.3 and the nature of (R-bulk)

**The implication.**
- For $k\ge k_0$, choose $W^{(j)}$ with $\rho_{W^{(j)}}\le C\varepsilon^k$, so that $W^{(j)}\subseteq B_k$ (circumradius about each $P$).
- Corollary 4.3 then gives $|O_{r_k}(z)|\le\beta_{W^{(j)}}\max(1,N)$.
- Monotonicity gives (B).
- The quantifiers are right. $C>0$, $N$ and $k_0$ are fixed. The bound may depend on $k$ through $j(k)$, which is harmless.
- The proof uses only that, for each $k$, $\sup_x|O_{r_k}(x)\cap B_k|<\infty$. Uniformity of $N$ in $k$ is not used (issue 5).

**Is (R-bulk) genuinely infinite?**
- $\beta^*$ is monotone: $W\subseteq W'$ implies $\beta^*(W')\le\beta^*(W)$, because avoiding a larger set is a stronger condition.
- So a bound for a small window implies one for every window containing it. Only arbitrarily small windows matter.
- Monotonicity runs the wrong way to reduce the family to finitely many cases. The note's claim that "(S1) is not a single statement" is **right**, unless a self-similarity argument is supplied (see the Suggestions section).
- (R-bulk) asks for termination of the closure. What Proposition 6.3 actually needs is the weaker $\beta^*(W^{(j)})<\infty$.

### Claim (6): the programs (read in full; read-only)

**`rcut.c`.**
- Exact in the following:
  - disk-membership signs (`sgn4rho`, `__int128`);
  - the exact coincidence test. I re-derived it: the circumradius condition $|u|^2|v|^2|u-v|^2=(3+\varphi)(2+\varphi)m^2$, using $\sin^272^\circ=(2+\varphi)/4$ and $\operatorname{Im}(\zeta^k)/\sin72^\circ\in\{0,1,\varphi-1,1-\varphi\}$, with side signs;
  - tangency. The angle uses $\operatorname{atan2}(\sqrt g,\sqrt{|d|^2})$ with $g=4\rho-|d|^2$ computed exactly, so $g=0$ gives an exact zero offset.
- Orderings use double precision with the underived $5\cdot10^{-15}$ bound.
- Window clipping removes exactly the open arc $\gamma\cap\operatorname{int}W_P$. The relative interior of $\gamma\cap W_P$ lies in $\operatorname{int}W_P$ whenever $\gamma$ is not a window circle, and `rcut.c` skips window circles. The arcs of $\gamma$ inside each $D(e_i)$ are shorter than $\pi$, so their intersection is connected.
- Both prefilters are conservative:
  - `maxd` includes non-corner intersection points (it prints 0.52 versus the true 0.0935), and `WRAD` is $1.5\cdot$`maxd`;
  - under-removal only adds arcs, which is safe.
- Overflow margins are ample (coordinates capped at $\pm15000$).

**`chk.py`.**
- It is new code that recomputes every decision from the arc file:
  - expansion by symmetry;
  - its own merging;
  - (K1)–(K4).
- It shares only the symbol semantics $(e,s)$, the window definition, and `zz.py`. It does not trust any decision of `rcut.c`.
- Its arithmetic is 40-digit `mpmath` *floating point*, not interval arithmetic, and it carries no error analysis. See issue 3 for the tangency weakness.
- So `chk.py` gives a second implementation, not a certificate. The note says exactly this.

**Logs.**
- The table rows match the `rcut` logs:
  - circles, arcs, pieces, coincidences and times;
  - $(2,-5,5,-6)$: 1 939 012 / 6 509 586 / 69 247 467;
  - $(2,6,-2,5)$: 10 960 690 / 36 177 413 / 398 391 927 in 1471.5 s.
- `chk_w1.log` and `chk_079.log` end in VALID with 2 023 476 and 3 192 528 images.
- There was no log for $(0,2,-1,0)$. I re-ran `chk.py` on it: VALID, 22 228 arcs, 51 828 images, 0 uncovered.

**My recomputation** (`refcomb/refchk.py`, a different design):
- There is no merging. Coverage of each image is decided by a greedy sweep over all expanded arcs of the target circle.
- Every ordering uses `mpmath.iv` interval enclosures at 30 digits, refined to 70 and then 150 if they overlap.
- An overlap is resolved by my own exact test. It writes the circumcentre as $z=uv(\bar u-\bar v)/(\bar uv-u\bar v)\in\mathbb Q(\zeta)$, tests $|N|^2=(3+\varphi)|\delta|^2$, and decides the sides by the exact sign of $\operatorname{Im}$ via $(x-\bar x)(\zeta-\bar\zeta)$.
- At exact tangency $\beta$ is exactly 0.
- Results:
  - $w=(0,2,-1,0)$: **VALID**, 22 228 arcs, 51 828 images (the same count as `chk.py`), 0 uncovered; 132 interval overlaps, all exactly equal points, none unresolved. (K4) margin $\varphi^{-1}-2\rho_W=0.0332$.
  - Negative tests: deleting 53 random arcs gives uncovered images (at least 180 already in the first 5000 arcs). Checking against the window $(5,-1,4,0)$ aborts at (K2).
- I also recomputed the window geometry of all nine rows (inradius, circumradius, $|w|<r_c$). It agrees with Table 5.1.
- I did not re-run the closure algorithm itself. Termination and minimality are irrelevant once a valid closure is exhibited.

### Claim (7): evidence

My own BFS (`refcomb/core_ref.py`) uses the starts $y=P+\varepsilon^k\eta$ with $|\eta|^2\le0.09$ and $|\sigma\eta|^2\le64$, tested exactly. This gives 21 starts per critical point and 798 in all. Core visits are tested exactly as $100|y-P'|^2\le9\varepsilon^{2k}$.

| level | orbits | points in all orbits | largest orbit | max core visits per orbit |
|---|---|---|---|---|
| 1 | 387 | 568 459 | 71 817 | 1 578 |
| 2 | 414 | 7 306 570 | 1 150 311 | 1 352 |

Both rows agree exactly with Table 6.1. I did not reproduce level 3 (about $9.8\cdot10^7$ points) or the agreement percentages, the 126 lune-regime points and the 38 blocks. The note does label all of these as evidence, and gives enough detail to reproduce them.

## 3. Status of each computational claim

| claim | status after this report |
|---|---|
| Lemma 2.1 enumerations | certified (exact; re-done) |
| Table 5.1 row $(0,2,-1,0)$ | **certified** by the referee's exact-plus-interval recheck. This assumes `mpmath.iv` is correct; the recheck is not formally verified |
| rows $(5,-1,4,0)$, $(-3,4,-4,0)$ | computed by two implementations, not certified |
| the six other rows | computed by `rcut.c` alone, not certified |
| counterexample (§6.3) | certified (exact; three implementations) |
| Table 6.1, levels 1–2 | exact, reproduced; level 3 not reproduced |

## 4. Numbered issues

1. **Title and §5 heading — minor (status).**
   - The title says "a certified bulk bound". §5 is headed "proved modulo the exact computation". Yet the body says the bound rests on floating-point orderings and is not a certificate.
   - *Repair:* use a title such as "…: a computed bulk bound at the critical radius…". Change the heading to "conditional on the computation". Record that the $(0,2,-1,0)$ row is now independently certified.
2. **Status item 1 and §6.1 (R-bulk), "verified for nine sizes"; §7 item 3, "Done" — minor.**
   - *Repair:* say "computed for nine sizes (one certified, two re-checked by a second floating-point implementation)".
3. **`chk.py` error control (§5.1, "40-digit … tie $10^{-30}$") — minor.**
   - `ang` computes $\beta=\arccos(|d|/2R)$ from a floating-point ratio. At exact tangency, $|d|=2R$, a $10^{-40}$ error becomes a $\sim10^{-20}$ error in $\beta$. That exceeds the tie threshold, so two names of one point are then ordered by noise. I checked that this is conservative for equal points: it can only produce false INVALID verdicts. But there is no separation bound for distinct points. So the "margin of about $10^{-30}$" claim has no basis there.
   - *Repair:* compute $\beta$ from the exact $4\rho-|d|^2$, as `rcut.c` does, and use interval arithmetic (as in `refcomb/refchk.py`). Alternatively, finish the Lean port.
4. **Corollary 4.3 proof — minor.**
   - "Every $y$ is reached from its last visit to $W$" needs a chain that starts at a point of $O_r(z)\cap W$. Such a chain exists because orbits are equivalence classes, but the chain from $z$ itself need not visit $W$.
   - *Repair:* add that sentence.
5. **§6.1 and Status item 3, framing of the remaining gap — minor.**
   - The proof of Proposition 6.3 uses only per-$k$ finiteness. Also, by Corollary 4.3 with any one row of Table 5.1, (B) is *equivalent* to $\sup_x|O_{r_k}(x)\cap W|<\infty$ for all $k$. So (R-bulk) + (R-core) is a sufficient *strategy*, strictly stronger than (B), not "the remaining gap".
   - "(R-bulk) is not implied by (B)" is asserted without proof.
   - *Repair:* say "a sufficient pair of statements" and "is not known to follow from (B)". Optionally weaken (R-bulk) to $\beta^*(W^{(j)})<\infty$.
6. **Lemma 3.3 proof, "together possibly with the start or the end" — cosmetic.**
   - The reduced intermediate points are always original intermediate points.
   - *Repair:* delete the phrase.
7. **Lemma 2.1(4) proof — cosmetic.**
   - "$3+\varphi$ is a unit at 2" is not needed. $2\mid d\bar d$ with 2 prime and real already gives $2\mid d$.
   - Item 1's "a search finds exactly these 20" is a confirmation; the count follows from the algebra.
8. **Table 5.1, row $(-3,-1,-1,-5)$, "`chk.py` not run" — cosmetic.**
   - `chk_063.log` shows a partial run: 300 000 of 1 142 778 arcs, 0 uncovered.
   - *Repair:* say "partial, interrupted", or remove the log.
9. **Propositions 4.4 and 4.5 — minor.**
   - A "word" should carry its itinerary, that is, which letters act non-trivially. Otherwise the same letter string has different germs on different domains.
   - State the standard fact used in 4.5: between consecutive event values the arrangement moves by an isotopy, so its combinatorial type is constant.
10. **Theorem 4.2 / 5.2, $F$ not computed — minor (informational).**
    - $\beta_W$, and with it the word length $\beta_W+1$ of Proposition 4.4, is inexplicit.
    - *Repair:* count the faces of the certified $(0,2,-1,0)$ closure. This is cheap and would make Proposition 4.4 usable for the hybrid certificate of §9.2.
11. **Reproducibility (§8 caveat 4) — minor.**
    - The programs and certificates live in a session scratch directory that a reboot or routine cleanup can clear.
    - *Repair:* copy `rcut.c`, `chk.py`, `zz.py`, `latbfs.c` and the $(0,2,-1,0)$ certificate into the repository, or rely on the Lean port.
12. **§8 table, "proved (not refereed)", and caveat 5 — cosmetic.**
    - Update both after this report.

## 5. Referee's suggestions for closing (R-bulk) and (R-core)

These are suggestions, not verdicts.

1. **Restate (R-bulk) in the weakest usable form.** Ask for $\beta^*(W^{(j)})<\infty$ along one nested sequence $W^{(j)}\downarrow\{P\}$. By monotonicity of $\beta^*$ in $W$, nested windows suffice, and finiteness for each $j$ is all Proposition 6.3 needs; no uniformity in $j$ is required.
2. **Allow windows bounded by arcs of any radius.** The proof of Theorem 4.2 never uses that $\partial W$ has radius $r_c$. Only `rcut.c`/`chk.py` and the Lean port would need the generalization. This permits rescaled windows $P+u_P\varepsilon^j(W_0)$, which are not of the form of §3.
3. **A finite reduction of (R-bulk) via annuli.**
   - Factor $\beta^*(W^{(j+1)})\le\beta^*(W^{(j)})\cdot a_j$. Here $a_j$ bounds the visits of strict chains avoiding $W^{(j+1)}$ to the annulus $W^{(j)}\setminus\operatorname{int}W^{(j+1)}$. This is the note's nested factor.
   - If the face-labelled first-return systems on consecutive annuli have the same combinatorics for $j\ge j_0$, then $a_j=a_{j_0}$, and (R-bulk) follows from one more closure computation.
   - Exact conjugacy under $z\mapsto P+u\varepsilon(z-P)$ is unlikely in 2-D, because circles of radius $r_c$ through $P$ do not rescale. But in coordinates scaled by $\varepsilon^{-j}$ they converge to their tangent lines. So the right statement is structural stability of the *tangent-cone* system (lines through $P$, plus the skeleton returns $g(P)\to P$). That would be:
     - a finite check: no degenerate events in the limit;
     - an explicit $j_0$ from the curvature error $O(\varepsilon^j)$, in the style of Proposition 4.5 but in the window-scale parameter.
   - The exact golden-rotation renormalization of the 1-D chord is what to test first: whether the skeleton points approaching each of the 38 points are $\Psi_P$-invariant.
4. **(R-core) through a limit polygon exchange.**
   - Fix the certified window $(0,2,-1,0)$. By Propositions 4.4–4.5 the induced system on $W$ near $r_c$ is one finite symbolic system with moving faces.
   - In coordinates $X=\varepsilon^{-k}(x-P)$ the collapsing faces converge to the half-plane system $10\,\ell_P(P+X)+1\lessgtr0$ with the finite germ set $G_W$. That is a piecewise isometry with straight cuts and algebraic data.
   - (i) Certify, by the same closure method with lines, that this limit system has uniformly bounded orbits on $B(0,C)$.
   - (ii) Prove, with the Diophantine lune lemma, that from an explicit $k_0$ on the level-$k$ induced system on $B_k$ coincides with the limit system face by face. The exact agreement on the 126 lune-regime points is consistent with this.
   - (iii) Cover the levels below $k_0$ by Lean-engine certificates. Since Proposition 6.3 needs only per-$k$ finiteness, the hybrid certificate of §9.2 is an alternative for each base level.
5. **Cheap next computations.**
   - Count $F$ for the certified row.
   - Port window clipping to the Lean engine (in progress).
   - Run `refcomb/refchk.py`, or a C version of it, on the $(5,-1,4,0)$ row to certify a second window. In Python, the angle cache would need several GB, which is why I did not run it.

## 6. What I did not check

- I did not re-run `rcut.c`, and I did not reproduce any closure from scratch. I verified the given $(0,2,-1,0)$ certificate and compared log numbers for the other rows.
- I did not re-run `chk.py` on rows 2–3; I relied on their logs.
- I did not verify any of the six smaller-window certificates.
- I did not reproduce the level-3 row of Table 6.1, the block-agreement percentages (93.5%, 97.6%, 11 240/11 944), or the 126-point lune-regime agreement. I did not read `latbfs.c` beyond its header, or `cmpcore2.py`, `diffblk.py`, `lunestat.py`, `eqtest.py` beyond its first lines, or `kcut4.c`.
- I did not check the Diophantine lune lemma or the remarks of §6.2 beyond Lemma 6.1, which is correct.
- `mpmath.iv` and my own code are trusted but not formally verified.

## 7. Record of the referee's computations

All files are in `/private/tmp/claude-501/-Users-eric-Github-riemann-hypothesis/8e07d302-d180-4cc0-ac7d-117a36aae2f9/scratchpad/refcomb/`.

- `ref_zeta.py`: new exact $\mathbb Z[\zeta_5]$ / $\mathbb Z[\varphi]$ arithmetic.
- `lemma21.py`: Lemma 2.1, Table 2.1, the tangency enumeration.
- `cex_ref.py`: the counterexample orbits. Cross-checked with `tdcsg-orbit orbit -n 5 --r2 re:7/2,9/5 --start pow:…` and `--r2 re:61/10,-12/5`.
- `core_ref.py` and `core_ref.log`: Table 6.1, levels 1–2.
- `chk_w0_ref.log`: the author's `chk.py` on $(0,2,-1,0)$, VALID.
- `refchk.py` and `refchk_w0.log`: the interval-arithmetic verifier, VALID in 184 s. `neg_del.log` and `neg_win.log` hold the negative tests.
