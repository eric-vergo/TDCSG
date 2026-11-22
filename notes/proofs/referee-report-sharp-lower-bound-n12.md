# Referee report: window reduction, rigidity and the period-one test for $GG_{12}$

Referee: Claude (independent of the authoring agent)

Subject: `sharp-lower-bound-n12.md`. Companions consulted: `critical-radius-n12.md`, `sharp-lower-bound-limit-system.md` and its referee report, `sharp-lower-bound-combined.md`, `sharp-lower-bound-n5.md`, `../certificates.md`, `../relative-certificates.md`. The author's programs (session scratch `sharp12/`) and the earlier referee's programs (`reflim/`) were read and never modified. The repository engine `tdcsg-orbit` was run read-only. All my computations are in the session scratch directory `ref12/`, with my own code. That code uses a different point representation from the author's programs: doubled real and imaginary parts in $\mathbb Z[\sqrt3]$, in place of the $\zeta$-basis.

## Summary

The note does not prove (B₁₂), and it says so in its first lines: finiteness of $GG_{12}(r)$ for every $r<r_c=\sqrt{40-22\sqrt3}$ is still open.

**Every computational claim I tested reproduced exactly with my own engine,** count for count:
- the onset example;
- the first-return statistics on $S_{300}$ at levels $0\to1\to2\to3\to4$;
- the orbit-partition statistics at $2\to3$, and on $S_{100}$ at $0\to1\to2\to3$;
- the partitions at $3\to4$, on a complete run where the note's was partial: 4 changes among all 2 413 points, all of them merges;
- the second example;
- the lune criterion;
- Table 5.1;
- Lemma 2.1;
- the failures of the $\Phi$-invariance test.

The earlier referee's 265/265 still agrees (levels $2\to3\to4$). The refutation of exact period one is therefore established, for both orbit partitions and first-return sets, at $2\to3$ and $3\to4$.

The proved lemmas are correct, with these exceptions:
- the lune constant is rounded the wrong way (issue 4);
- the closed versus open core in the proof of Theorem 5.4 needs a one-line repair (issue 5);
- Proposition 8.1 is correct, but conjecture M₁₂ plays no role in it. L₁₂ as stated already implies (R-core-t₁₂), so "no base level needed" is true only because L₁₂ assumes the bound at every level, including levels 0–2 (issue 3).

The field-norm statement of Lemma 3.1 is right. I found explicit elements $u\in\mathbb Z[\zeta_{12}]$ with $r_m^2=|u/(3+i)|^2$ for $m=1,2,3$.

Two errors of fact:
- §7.4 item 1: the level-3 core orbit set of the onset example has **38** points, not 16 (issue 1). The 16 is the first-return set, and also the part in the tight cores.
- The note presents the general conclusion "no starting level works" as following from the data and from Lemma 6.2. It is an extrapolation (issue 2).

## Verdicts

| claim | verdict |
|---|---|
| (1) Refutation of exact period one (first-return sets, orbit partitions; onset example) | **correct after minor fixes**. Every count I tested reproduced exactly. The refutation holds for $m_0\le3$. "No fixed starting level works for all core lattice points" is a **conjecture**, not a conclusion (issue 2). §7.4's "16" should be 38 (issue 1). No contradiction with the 265/265 of the earlier referee: that sample has internal radius $\le100<124.5$, and I re-ran it (265/265 at $2\to3$ and $3\to4$) |
| (2) Evidence: monotone growth, lune criterion, level-independent core visits, $\Phi$-invariance | **evidence, correctly labelled**; the subset I recomputed reproduced exactly. The monotonicity is **only observed**, and the note says so (§8.3(i)). The "enlarging disks" argument does not prove it (§5 below) |
| (3a) 24 vectors, 48 critical points, 12 classes, 8 tight / 40 rigid (Table 5.1) | **correct**; reproduced by my own exact code. "Two independent programs" is an overstatement (issue 6). "Exactly 8 tight" means "skeleton exceeds the cap" (issue 7) |
| (3b) Lune lemma (constant 176.75), frozen-point lemma, no-parity identity, Lemma 6.1 | **correct after minor fixes** (issue 4: constant rounded down) |
| (3c) Lemma 3.1: lattice non-norm at all $m$; field norms at $m=1,2,3$; non-norm at $0,4,5,\ge6$ | **correct**. Explicit representations are given in §4 below. The remark on the earlier referee's wording is correct |
| (3d) Three relative certificates at $r_c$ | **certified** (repository float-free checker, see §3), with the caveats that follow. The exact checker is a separate module of the same code base, not an independent implementation. I re-ran it on rows 1 and 2: both VALID, and negative tests on row 1 were rejected. My own independent float-guided checker accepts all three rows; that check is computed, not certified |
| (3e) Corollary 4.2 (finite iff bounded window visits), Theorem 5.4 | **correct after minor fixes** (issue 5) |
| (4) Proposition 8.1, "no base level needed" | **correct, but misleading**: M₁₂ is not used, and L₁₂ is (R-core-t₁₂) restated over all levels (issue 3) |
| (5) Base: $\delta=1/180$ covers levels 0–2; level 3 not certified | **correct**: $\delta_2=\varepsilon^2/10=1/139.3>1/180>\delta_3=1/519.8$ |
| (6) Title and status | Status: **correct** in substance. (B₁₂) is said to be open; the refutation, the certified results and the conjectures are labelled. **Minor** fixes: status item 4's last sentence (issue 2), and item 2's "independent" (issue 6) |

## Numbered issues

1. **§7.4 item 1 (and Table 7.2's description). Severity: minor (wrong number).** The note says: "At level 3 that of $p^\ast+\varepsilon^3\eta$ has 16, containing the 8." By the note's own definition (§7.1: $O_{r_m}(x)\cap B_m$ over all 48 cores), the level-3 core orbit set of the onset example has 38 points. My engine gives full orbits of 27 456 points (level 2) and 284 536 points (level 3). The repository engine gives exactly the same sizes. The author's own closure output `CB_k3.txt` also lists 38 core points for this orbit.
   - The 38 points are 16 in the 8 tight cores (two per tight point) and 22 in non-tight cores.
   - 16 is the size of the level-3 first-return set, and of the tight part of the orbit.
   - The containment $8\subsetneq38$ holds, so the conclusion is unaffected.

   *Repair:* write "38 (16 of them in the tight cores)", or define the partition statistic on tight cores and say so.

2. **Status item 4 (last sentence), §8.1 second paragraph. Severity: gap (an extrapolation stated as a conclusion).** What is exact:
   - failures of the partition version at $2\to3$ (28 points) and $3\to4$ (4 points);
   - failures of the first-return version at $2\to3$ and $3\to4$.

   These refute the hypothesis of Proposition 6.4 for every $m_0\le3$. Nothing has been tested from $m_0=4$ on, except $S_{100}$ at $4\to5$ (no change) and 300 annulus points at $3\to4$. "Exactness holds only up to an internal radius that grows with the level; no fixed starting level works" is a conjecture. Lemma 6.2 does not support it as an argument: it gives a *sufficient* condition for lune-freeness, so it cannot show that lunes, and hence changes, persist at every level. The rising onset radii (13.9, 26.9, 124.5, 142.7) and the thinning counts (1 232, 218, 49, 22) fit equally well with eventual exactness from some $m_0\ge4$. §8.1 does say "(conjecture; not tested beyond level 4)", but status item 4 states the general claim without that qualifier. *Repair:* state "refuted for $m_0\le3$; conjecturally for every $m_0$", in the status and in §8.1.

3. **Proposition 8.1 and the remark after it. Severity: minor (logic correct, emphasis misleading).** L₁₂ bounds the *union over all levels* of the zoomed core orbit sets of each $(Q,\eta)$ by $N$. So for every $m\ge0$ and every lattice $y$ whose orbit meets a tight core, $|O_{r_m}(y)\cap\operatorname{int}B_m^{\rm t}|\le N$. That is (R-core-t₁₂) with $m_0=0$, and M₁₂ is not used. Conversely, (R-core-t₁₂) together with M₁₂ and Corollary 5.2 gives L₁₂ with $N$ replaced by $576N$.
   - So L₁₂ is essentially a restatement of the remaining gap, not a reduction of it.
   - "No base level needed" is true only because L₁₂ already contains the bound at levels 0–2.
   - M₁₂ earns its place only if L₁₂ is to be proved through a limit object, the monotone union identified with the classes of a straight-cut or hybrid system (§8.3(ii)).

   *Repair:* "L₁₂ implies (R-core-t₁₂) with $m_0=0$. Under M₁₂, L₁₂ is equivalent to a bound on the classes of the monotone limit, which is the form in which a limit-system certificate could prove it."

4. **Lemma 6.2, status item 3, §10. Severity: minor.** The constant $20|\sigma'w|=20\sqrt{40+22\sqrt3}=176.7542\ldots$ is stated as $176.754$. That value is *below* the true constant, so the hypothesis as printed is very slightly weaker than what the proof needs. *Repair:* state the lemma with the exact constant $20\sqrt{40+22\sqrt3}$, or round up (176.76). The numerical consequence ($1432\,\varepsilon^m<1$ from $m=6$) is unaffected.

5. **Theorem 5.4, proof, third bullet. Severity: minor (gap with an easy repair).** Corollary 5.2 bounds $|O\cap B_m|$ by the *closed* tight cores. Lemma 3.4 transfers bounds only for *open* sets $U$. The sentence "the closed and open cores differ by a null set, which is irrelevant through Lemma 3.4" is not an argument: an orbit can contain points on a core boundary circle. *Repair:* Theorem 5.1's margins have slack: (a) needs $C\le0.19$ and (b) needs $C<0.1387$. So run Theorem 5.1 and Corollary 5.2 with $C'=0.089$. The closed cores $B'_m$ of radius $C'\varepsilon^m$ lie in $\operatorname{int}B_m$, so $|O\cap B'_m|\le576\max(1,|O\cap\operatorname{int}B^{\rm t}_m|)\le576\max(1,N)$ for every $x$, by Lemma 3.4. Then choose $W^{(j)}\subset\operatorname{int}B'_m$.

6. **§5 ("Two independent programs"), status item 2 ("independent float-free checker"), §9. Severity: minor (overstated independence).**
   - `skel12.c` and `rigid.py` were written by the same author, in the same $\zeta$-basis, with the same formulas for $|c|^2$ and for multiplication by $\zeta$. They differ only in language. `rigid.py`'s margin (b) is computed in double precision (`cz`), not to 50 digits.
   - `check-relative-certificate` is a separate module of the same code base as the generator. It shares the exact layer (`Field`, `Ball`, `Tower`, `CirclePoint`; `relative-certificates.md` §2). It is not an independent implementation.

   Both results are now confirmed by my own code (§4). *Repair:* say "two programs (same author)" and "separate float-free checker"; cite this report for independent reproduction. Also, the row-1 checker log (`chk_w1.log`) is missing from `sharp12/`; I re-ran the checker (VALID).

7. **Lemma 2.1 / Theorem 5.1 framing: "exactly 8 critical points are tight". Severity: minor.** "Tight" is used for the critical points whose skeleton is infinite. For all 8 this is only observed: the BFS exceeds a cap ($2\cdot10^6$ in the note, $2\cdot10^5$ in my run). For $p^\ast$ the infinitude of the orbit is Theorem A, but the skeleton stops at critical points, so Theorem A does not give it. Nothing depends on it: the theorems use only that the other 40 are rigid, which is proved. *Repair:* "the other 40 have finite skeleta (proved); the 8 have skeleta exceeding $2\cdot10^6$ points and are treated as tight".

8. **§4 "Every decision of the generator was exact". Severity: cosmetic.** The generator log says "decisions made exactly: 0 halves, 0 orders". That is, every decision went through the certified float filter and none needed the exact fallback. Say "every decision was certified (float filter with proven error bound; 0 exact fallbacks)".

9. **§7.5 "Monotone growth from level 1", §8.2 evidence. Severity: cosmetic.** The 557 and 32 are sums over two classes whose statistics coincide (the multisets of excursion size, return count and lune count are equal at $p^\ast$ and $P_4$, levels 2 and 3, my runs). So they carry roughly half the independent weight their size suggests. Also, the partition statistic counts blocks restricted to the $p^\ast$ sample, not whole core orbit sets; say so.

10. **Title. Severity: cosmetic.** "tested to level five" is accurate, but the main finding is a refutation. Consider "…: the exact period-one step is refuted, monotone growth observed". The status paragraph itself is clear: (B₁₂) open; proved, certified, computed and conjectured results separated.

## 2. Assessment of the refutation (claim 1)

**Reproduced exactly** (my engine `ref12/eng.c`, closure variant `engc.c`; samples generated by my `gen.py`, which equal the author's `s23B.txt` and the earlier referee's `s12.txt` as sets):

| quantity | note | mine |
|---|---|---|
| onset $\eta=-45+11\zeta+71\zeta^2-67\zeta^3$: excursion size, returns, lunes at $m=2$ | 27 456, 8, 10 | 27 456, 8, 10 |
| same at $m=3$ | 284 494, 16, 6 | 284 494, 16, 6, and $R_2\subsetneq R_3$ |
| full orbit $m=2$ / $m=3$ (core points) | 8 / "16" | 27 456 (8) / 284 536 (38), $8\subsetneq38$. The repository engine gives orbit sizes 27 456 and 284 536 |
| $S_{300}$ first-return agreement $0\to1,1\to2,2\to3,3\to4$ ($p^\ast$) | 1 181, 2 195, 2 364, 2 391 | 1 181, 2 195, 2 364, 2 391 |
| same at $P_4$, $2\to3$ | 2 364 | 2 364 |
| changes: growth / shrink | $0\to1$: shrink 1 556 and 92 other (2 classes); from level 1 on, all growth | $0\to1$: 408 growth, 778 shrink, 46 other (one class); $1\to2$: 218/218 growth, $2\to3$: 49/49, $3\to4$: 22/22 |
| smallest internal radius of a change | 13.9, 26.9, 124.5, 142.7 | 13.93, 26.91, 124.45, 142.70 |
| $S_{300}$ partitions $2\to3$ | 1 464 → 1 451 orbits; 2 385/2 413; 1 438/1 464 blocks; 28 merges | identical; all 28 are merges with nested full core sets; max core visits 280 |
| $S_{100}$ $2\to3$, $3\to4$ (first returns) | 265, 265 | 265/265, 265/265 |
| $S_{100}$ partitions $0\to1,1\to2,2\to3$; orbits per level | 187, 253, 265; 136, 171, 165, 165 | identical |
| second example $(-75,48,67,-82)$, levels 0–4 | 332, 3 830, 35 416, 319 222, 9 749 672; returns 16,16,16,16,48; lunes 56,26,2,2,0 | identical |
| $S_{300}$ partitions $3\to4$ | partial: 1 485/1 489, 4 merges, internal radius $\ge246.4$ | **complete run**: 2 409/2 413 points, 1 447/1 451 blocks, 4 changes, all merges (full core sets $30\to38$, $8\to38$), smallest internal radius 246.37; 1 449 distinct level-4 orbits, the largest 17 393 748 points, none capped; max core visits 280 |

**Is the conclusion justified?** The exact statement "the hypothesis of Proposition 6.4 fails at $m_0=2$ and $3$" is justified. A failure at $3\to4$ refutes it for every $m_0\le3$. The stronger reading, that no $m_0$ works, is not established (issue 2).

**No contradiction with the earlier referee.** The earlier referee's 265 points have internal radius $\le100$, and all changes from level 2 on have internal radius $\ge124.45$. I re-ran $S_{100}$: 265/265 at $2\to3$ and at $3\to4$. That report's *mechanism* claim, "period one iff the level unit is totally positive", was explicitly a necessary-condition argument about recurrence of exact cut offsets. A failure of exact period one for return sets does not contradict it. What is refuted is the stronger prediction "period one is confirmed" read as an exact statement on all core lattice points, from level 2.

## 3. Certificates (claim 3d)

Programs:
- Generator: `tdcsg-orbit certify-relative`. It uses certified float decisions with an exact fallback; the logs show 0 exact fallbacks and 0 coincidences.
- Checker: `tdcsg-orbit check-relative-certificate`, a separate float-free module sharing the exact layer.

The SHA-256 of the three files match the note.

| row | $\rho_W$ | repository checker | my float-guided checker `fchk.py` |
|---|---|---|---|
| $(1,1,-5,5)$ | 0.0915 | **VALID**, re-run by me (69 228 K3 images, 40 s, 1 thread). Negative tests: 20 arcs deleted gives REJECTED (K3); the full arc set with the window line changed to the smaller shape $(-13,10,7,-10)$ gives REJECTED (K2) | accepts: 192 K2 arcs + 69 230 images, 0 failures; minimum non-zero slack $4.3\cdot10^{-5}$ rad (tolerance $10^{-9}$); the same two negative tests are rejected |
| $(-13,10,7,-10)$ | 0.0358 | **VALID**, re-run by me (1 250 880 K3 images, 596 s, 1 thread, 0.22 GB) | accepts: 1 251 074 tests, 0 failures, minimum non-zero slack $2.3\cdot10^{-5}$ |
| $(-11,9,5,-10)$ | 0.0197 | log VALID (not re-run by me) | accepts: 3 744 258 tests, 0 failures, minimum non-zero slack $7.7\cdot10^{-5}$ |

My checker parses the files, recomputes the 48 critical points, checks (K1), the 192 window boundary arcs (K2) and every rotated piece (K3). It uses window holes as in `relative-certificates.md` §2 and the symmetric canonicalization under $\pm z,\pm\bar z$. Angles are in double precision. Equal endpoints are decided with tolerance $10^{-9}$, and nearly all images end exactly at a listed endpoint. So it is an independent *computed-not-certified* confirmation. Window disjointness is clear numerically: the minimal critical distance is $0.19615>2\rho_W$.

**Classification:** rows 1–3 are **certified** in the repository's sense (exact checker VALID). Rows 1 and 2 were re-run by me; row 3 rests on the author's log. All three are corroborated by an independent implementation, but only up to floating point. I wrote no exact independent checker. The rows in `relcert/` of the parallel run are not checked; the note labels them so.

**Corollary 4.2** ("for every $r<r_c$, $GG_{12}(r)$ is finite iff its orbits meet the 48 windows boundedly often") is then correct. "Finite ⇒ bounded" is trivial. The converse is Theorem 4.2 of the combined note for general $n$, with Lemma 3.2 and Proposition 4.2 of `theorem1-converse.md`. Its proof never uses where the critical points or tangencies lie (earlier referee, §2).

## 4. Exact record of what I recomputed

All in `ref12/`; exact signs in $\mathbb Z[\sqrt3]$ with `__int128`; floats only as pre-filters with a generous margin before an exact test.

- **Lemma 2.1, Table 5.1** (`skel.py`; doubled coordinates; exact BFS; 60-digit margins).
  - 24 critical vectors, 48 critical points, none on both circles, 12 classes of 4.
  - Minimal distance$^2$ $=(208-120\sqrt3)/4=52-30\sqrt3=2\varepsilon^3$ exactly.
  - Skeleta: 36 points with $|S_P|=3$ (outside); 4 points with $|S_P|=14$ and 3 critical endpoints (inside).
  - Margins (a) 0.227938, (b) 0.277401, (c) 0.720208. The minimum of (c) over the outside class is 0.227938.
  - 8 points exceed the cap $2\cdot10^5$: exactly $\pm p^\ast,\pm\bar p^\ast,\pm P_4,\pm\bar P_4$, with other-disk margins 0.469307 and 0.150751.
  - $|\sigma'w|^2=40+22\sqrt3$.
  - Also checked by hand: Theorem 5.1's thresholds; $r_c-r_m<0.0369\varepsilon^m$; Lemma 3.3's radii 14.74, 24.45, 44.9, 85.5, 164.6.
- **Lemma 3.1** (`norms.py`). $\alpha_m=400-220\sqrt3-\varepsilon^m$ has norms 14 001, 14 521, 14 481, 13 801, 11 121, 1 081 ($m=0,\dots,5$), as stated. Explicit representations $|u|^2=\alpha_m$, $u\in\mathbb Z[\zeta]$ in the basis $1,\zeta,\zeta^2,\zeta^3$:
  - $m=1$: $u=(13,-18,-3,13)$;
  - $m=2$: $u=(16,-16,-8,11)$;
  - $m=3$: $u=(13,-16,-1,13)$.

  Hence $r_m^2=|u/(3+i)|^2$ is a field norm at $m=1,2,3$. I checked the Hilbert-symbol arguments for $m=0,4$: $v_{(\sqrt3)}(\alpha_m)=1$, the residue field is $\mathbb F_3$, and the symbol is $-1$. For $m=5$, $23,47\equiv11\pmod{12}$ split in $K$ with residue fields of order $\equiv3\pmod4$. For $m\ge6$, $\sigma'(r_m^2)<0$. The search finds no integral representation for $m=0,4,5$, which is consistent.

  **What this means.** At $m=1,2,3$, three test circles with centres in $\mathbb Q(\zeta)$ may meet in a point of $\mathbb Q(\zeta)$, and two may be tangent there. Lemma 3.4 (lattice points suffice) is then unavailable. Lattice computations remain exact, since no lattice point lies on a lattice-centred circle of radius $r_m$ (item 1). The earlier referee used these levels only for lattice computations, so its results stand. Its phrase "non-norm radii" is right only in that lattice sense. The note's assessment is correct, and its Theorem 5.4 rightly uses only $m\ge6$.
- **Excursions.** I ran $S_{300}$ at $p^\ast$, levels 0–4 (2 413 starts each; level 4: median 2 581 446, max 17 393 510, none capped), and at $P_4$, levels 2–3. I also ran $S_{100}$ at $p^\ast$, levels 2–4. The results are in the table of §2. Further:
  - lune-free implies no change: $1\to2$ 629/629, $2\to3$ 1 339/1 339, $3\to4$ 1 881/1 881 (one class; the note's 1 258 and 2 678 are twice the first two);
  - every change has a lune at the earlier level: 1 232, 218, 49, 22 of 1 232, 218, 49, 22;
  - lune-freeness persists: 0 of 629 (level 1) and 0 of 1 339 (level 2) have a lune at the next level, and 0 of 1 881 at $3\to4$;
  - stabilization: 206 of the 218 points that change at $1\to2$ agree at $2\to3$ (the note's 412/436 is twice this); 49/49 of the $2\to3$ changers agree at $3\to4$.
- **Closure mode** (full orbits, each core point once). On $S_{300}$, levels 2 and 3, and on $S_{100}$, levels 0–3, every count of Table 7.2 is reproduced (§2), including max core visits 280. On $S_{300}$ at level 4 the run is complete (2 413 starts; the note had a partial run); results in §2.
- **Repository engine cross-checks** (`tdcsg-orbit orbit -n 12`). Onset orbit: 27 456 points at $r^2=$ `re:393/10,-108/5` and 284 536 points at `re:187/5,-41/2`, the same as mine. Two failing $\Phi$-images at $r_c$: exactly 432 points each.
- **§7.7.** I explored the orbit of $p^\ast$ at $r_c$ with my engine to $2\cdot10^7$ points, recording core points within $0.09$ of $p^\ast$. Every $\Phi$-image of an orbit point within $\rho$ of $p^\ast$, with image internal radius below half the maximal explored one, was found: 1 122/1 122 at $\rho=0.05$ and 2 476/2 476 at $\rho=0.088$. My core radius limits $\rho$ to 0.09, so I did not test 0.14. The test set differs from the note's because of the frontier rule. The first failure the note reports, $y-p^\ast=-740+738\zeta+202\zeta^2-544\zeta^3$: $\Phi(y)$ has a finite orbit of 432 points at $r_c$ (mine and the repository engine), so the non-membership is exact. The same holds for the note's second example.
- **Certificates.** See §3.

## 5. Referee's suggestions

1. **On a proof of monotone growth (M₁₂): what the "enlarging disks" idea does and does not give.**
   - *True statement.* Pull the level-$(m+1)$ system back by $\Phi_Q$. The disk $\Phi_Q^{-1}(D_p(r_{m+1}))$ has centre $Q-\varepsilon^{-1}w$ and radius $r_{m+1}/\varepsilon$, and it contains $D_p(r_m)$. Containment is equivalent to $r_c-r_{m+1}\le\varepsilon(r_c-r_m)$. That holds because $r_c-r_{m+1}=\varepsilon\delta_m/(r_c+r_{m+1})\le\varepsilon\delta_m/(r_c+r_m)$. The same containment holds for the other disk at the 8 tight points, all of which lie inside it. In zoomed coordinates the tight test transfers one way: in at level $m$ implies in at level $m+1$ (Lemma 6.1(2)).
   - *Why this does not prove M₁₂.* The pulled-back generators are rotations about $Q+\varepsilon^{-1}(p-Q)$, not about $p$. The orbit-monotonicity theorem (`boundary-contact.md` Theorem 3.1) compares the *same* centres at two radii. So it gives $O_{r_m}(x)\subseteq O_{r_{m+1}}(x)$ for the same physical $x$, never a statement about $\Phi_Q(x)$. $\Phi_Q$ does not commute with $R_p$: $R_p\Phi_Q z-\Phi_QR_pz=(1-\varepsilon)(R_pQ-Q)\ne0$. The note's §8.3(i) says exactly this, and I agree that the note proves nothing here; monotonicity is only observed.
   - *A provable partial statement (suggested lemma, "linear returns persist").* Let $h$ be a word whose chain from $Q$ passes through non-critical lattice points $h_k(Q)$ with test margins $\mu(h)=\min_k\bigl||h_k(Q)\mp1|-r_c\bigr|>0$ and distances $\nu(h)=\min_k\operatorname{dist}(h_k(Q),\text{critical points})>0$, and ends at a critical $Q'=h(Q)$. If $C\varepsilon^m+(r_c-r_m)<\mu(h)$, $2C\varepsilon^m<\nu(h)$, and the chain is valid at level $m$ from $Q+\varepsilon^mY$ ($|Y|\le C$), then it is valid at level $m+1$ from $Q+\varepsilon^{m+1}Y$, with the same zoomed endpoint. The proof: intermediate tests are unchanged, and the only tight test is the first one, which transfers by Lemma 6.1(2). So *linear* first returns persist from a word-dependent level on. The obstruction to M₁₂ is the *non-linear* returns. For those, $h(Q)\ne Q'$ and the zoomed translation $\varepsilon^{-m}(h(Q)-Q')$ forces the word to change with $m$.
   - *Where shrinkage would have to come from.* For a far test with base vector $u$ and zoomed offset $\tilde\delta_m(u)$ (Lemma 6.3), $\tilde\delta_{m+1}-1=\varepsilon^{-1}(\tilde\delta_m-1)$ exactly. So cuts from inner near-misses ($|u|<r_c$, which include the frozen points) move to enlarge the "in" region, and so does the curvature term $10\varepsilon^m|Y|^2$. Only outer near-misses ($|u|>r_c$) shrink it. A proof of M₁₂ by transporting words would have to show that the words realizing level-$m$ returns can be renormalized to level-$(m+1)$ words with the same zoomed germ, and that their outer near-miss tests survive. A cheap test: record, along excursions, whether every cut that affects a change comes from an inner near-miss.
2. **Re-state the remaining gap honestly** (issue 3). The real target is a finite object, the hybrid limit pseudogroup of §8.3(ii), whose classes bound the monotone union. Without such an object, Proposition 8.1 restates (R-core-t₁₂).
3. **Test $m_0=4$ directly.** Run first returns $4\to5$ on the 22 points that change at $3\to4$, and on the $S_{300}$ points of internal radius above 200. A change at $4\to5$ on $S_{300}$ would extend the refutation to $m_0=4$; none would support eventual exactness.
4. **An exact independent checker for relative certificates.** Rows 1–3 rest on one exact checker written with the generator's exact layer. Row 1 is small (31 205 arcs), and an exact Python re-implementation of (K1)–(K3) would make it independently certified.

## 6. What I did not check

- §7.6 (frozen-hit statistics, physical distances).
- Core-visit distributions on the 30 full orbits of $S_{100}$ (§7.3, last paragraph).
- $S_{\rm ann}$ (§7.2, §7.5).
- Level 5 ($S_{100}$, 184/184).
- $\Phi^2$ and $\rho\ge0.09$ in §7.7.
- The parallel `relcert/` rows.
- The exact checker on row 3, which I did not re-run.
- §10 (transfer to $n=5,8,10$), beyond reading it.
- The general-$n$ reading of the combined note's Theorem 4.2 (`../relative-certificates.md` §§2–3), which I took as given from its own review.
- Lemma 3.4's proof, which I read and found sound; I did not re-derive the $n=5$ ingredients.
