# Referee report: the straight-cut limit at the critical points, rigidity away from the tight points, and the period-two obstruction for $GG_5$

Referee: Claude (independent of the authoring agent)

Subject: `sharp-lower-bound-limit-system.md`. Companions consulted: `sharp-lower-bound-combined.md` and its referee report, `sharp-lower-bound-n5.md`, `sharp-lower-bound-n8.md`, `critical-radius-n5.md`, `critical-radius-n12.md`, `../certificates.md`. Author's programs (session scratch `sharp3/`) were read, never modified. All recomputation is in the referee's scratch directory `reflim/`.

## Summary

The note does not prove (B) and says so in its first lines. Problem (B), finiteness of $GG_5(r)$ for every $r<r_c=\sqrt{3+\varphi}$, remains open.

What it proves is correct:
- the fixed-word limit system has orbits of at most 190 points, and non-linear core returns need about $\varphi^{3k}$ window visits;
- the nine non-tight classes are rigid from level 4 on;
- the reduction of (B) to the four tight windows holds.

The crux question was whether the relative-certificate theorem still applies when 34 of the 38 critical points lie outside the windows, so that tangencies occur outside $W$. It does. The proof of that theorem never uses where tangencies happen, and the certificate checkers treat tangencies the same way wherever they occur. With my own exact engine I reproduced every number of the note that I tested:
- the refutation of $\varphi^{-3}$ matching;
- the period-two agreements;
- Table 4.1;
- the invariance test of the orbit of $E$.

I also strengthened that last test: the $\varphi^{-3}$ failures are now *exact* non-memberships, not just points the search failed to find.

The coordinator's norm $-1$ explanation reaches the right conclusion by the wrong mechanism (§3). Its prediction for $n=12$ (period one) is confirmed by an exact computation: 265 of 265 sample points at $p^\ast$ agree between consecutive levels $2\to3$ and $3\to4$, and 147 of these points have non-linear returns.

Main issues:
- The headline evidence for Conjecture 5.1 ("1 784 cases") is mostly non-tight points. For those points the conjecture is a consequence of Theorem 4.2, so they carry no evidence. Only 156 of the cases are tight.
- The rise "to 100%" at $3\to5$ comes from a selected sample.
- A gap in the proof of Proposition 3.1 at window boundaries, which is harmless for the 190 bound.

## Verdicts

| claim | verdict |
|---|---|
| (1) Propositions 3.1–3.2: fixed-word limit $\mathcal S_{\rm lin}$, orbits $\le190$ | **correct after minor fixes**. The 190 bound is correct and trivial; Proposition 3.1's description of the domains has a small gap (issue 3) |
| (2) Proposition 3.3: non-linear returns need $\ge m_k$ window visits; conclusion that the words must grow | **correct**. The conclusion is justified as a statement about the fixed-word system (issue 4) |
| (3) Theorem 4.2, Corollary 4.3: non-tight cores rigid for $k\ge4$, for all points; (R-core) $\iff$ (R-core-t) up to 190 | **correct**. Table 4.1 recomputed exactly by my own code |
| (4) Table 4.2 and Corollary 4.4: four tight windows suffice | Theorem applicability: **correct**, no extra argument needed (§2). Rows $(0,2,-1,0)$ and $(5,-1,4,0)$: **certified** (I re-ran the interval checker on both: VALID; negative tests reject). Other seven rows: **computed-not-certified** |
| (5) Refutation of $\varphi^{-3}$ matching | **correct**. Reproduced exactly; stronger than stated (issue 6) |
| (6) Conjecture 5.1 (period two, $\varphi^{-6}$) | Data **reproduced exactly**. Status correctly "conjecture". The evidence is overstated (issues 1, 2) |
| (7) Remaining gaps, Next steps, base-level remark | **correct after minor fixes** (issues 7, 8) |
| (8) Title and status | Status: **correct**, open problem stated plainly. Title **minor fix** (issue 9) |

## Numbered issues

1. **§5.3 "1 784 cases", Status item 4, §7 table. Severity: gap (evidence overstated).** Of the 1 784 lune-free cases, 1 628 are non-tight points:
   - $k=1$: all 216 points are non-tight; no tight point is lune-free at level 1;
   - $k=2$: 698 of the 718 $S_{21}$ points are non-tight;
   - $k=3$: 714 of the 726 are non-tight.

   For non-tight points the period-two agreement follows from Theorem 4.2; at levels 1 and 2 it also holds with period *one* (216/216 at $1\to2$, 698/698 at $2\to3$, my runs). Conjecture 5.1 concerns the tight cores. The tight evidence is 156 cases: 20 ($S_{21}$, $k=2$), 124 ($S_E$, $k=2$) and 12 ($S_{21}$, $k=3$). The 117 $S_E$ points that are lune-free at $k=3$ and agree $3\to5$, which the note leaves out of this list, bring it to 273. *Repair:* report the tight counts separately, and drop the non-tight ones from the evidence for Conjecture 5.1.

2. **Status item 4, Table 5.2, "rising to 100% ($3\to5$)". Severity: gap (selection bias).** The level-5 sample is the family that fits in memory: 129 points, all with excursions of about $3.47\cdot10^6$. On that same 117-point $S_E$ subset, the earlier rates are $1\to3$: 116/117 and $2\to4$: 53/117. On all of $S_E$ they are 185/811 and 518/811. So $3\to5$ = 117/117 is not the top of a rising trend; that subset already agreed almost perfectly at $1\to3$. *Repair:* compare all level pairs on one fixed sample, and say that the level-5 rows are a selected family.

3. **Proposition 3.1, proof. Severity: minor (gap in a description, not in the 190 bound).** The proof claims each non-critical prefix image $h(Q)$ is at positive distance from $\partial W$. But $h(Q)$ can lie *on* $\partial W$:
   - $\Lambda$ is dense, and $\partial W$ is made of lattice-centred arcs of radius $r_c$;
   - by Lemma 2.1(5) of the combined note, a lattice point lies on such an arc exactly when it differs from the centre by one of the 20 elements;
   - $h(Q)\in\partial W\subset W$ is not excluded, because only $h(x)$ for $x$ in the domain must avoid $W$, not $h(Q)$ itself.

   In that case the zoomed domain carries an extra half-plane cut through $0$, from the tangent of $\partial W$. The germ is still linear, so Proposition 3.2 is unaffected. *Repair:* either add these cuts to the description of $\mathcal S_{\rm lin}$, or check over the finitely many prefixes that no $h(Q)$ lies on $\partial W$. The same applies to endpoint tests $g(Q)\in\partial W$ in case 2. Also say explicitly that "converges" means: for $k\ge k_1$ the zoomed domains are exactly the stated tests, and the curved boundaries converge to their tangent lines locally uniformly. The limit lives on 38 discs of radius $C$; extending it to whole planes is a convention.

4. **Proposition 3.3, constants. Severity: minor.**
   - $C=3/10$ is the core constant. $T_W=\max|\sigma t|$ is taken over the finite germ set $G_W$ of Proposition 4.4 of the combined note. Neither $T_W$ nor $\beta_W$ is computed, so $m_k$ is not explicit; §7 says so.
   - The proof is correct. Its steps: the norm bound $|a|^2|\sigma a|^2\ge1$ applied to $a=G(Q)-Q'\ne0$; $|\sigma t|\le mT_W$, since $\sigma$ of a rotation is a rotation; $s=\max|\sigma Q|=2.52626$, which I recomputed.
   - The conclusion "a useful limit must be built from first-return maps with unbounded words" is justified in the precise sense that $\mathcal S_{\rm lin}$ sees only linear classes, and consecutive classes are joined only through at least $m_k\to\infty$ window visits. It is a statement about which object to study, not a theorem about all limits; the wording should say that.

5. **Corollary 4.3, proof wording. Severity: cosmetic.** "Every linear class other than the one of a fixed base point contains a tight core point." In fact, when there are two or more classes, *every* class, the base class included, meets a non-linear edge, and both endpoints of such an edge are tight. That is what gives the stated bound $190\max(1,|O\cap B_k^{\rm t}|)$ rather than $190(1+|O\cap B_k^{\rm t}|)$.

6. **§5.3, invariance test of $O(E)$, "22% failures". Severity: minor (understated).** `psi.c` reports "not found in a truncated search", which is not proof of non-membership. My `psi5.c` computes, for failing images $z=E+\varepsilon(y-E)$, the orbit of $z$ itself at $r_c$. Results:
   - $\rho=1$: 200 of the first 200 failures have a *finite* orbit not containing $E$;
   - $\rho=0.2$: 65 of 67 do.

   Since $z\in O(E)$ would force $E\in O(z)$, these are exact non-memberships. *Repair:* state that the $\varphi^{-3}$ failures are exact, and that the $\varphi^{-6}$ successes are memberships found in a finite search, hence exact as memberships.

7. **§6 table row (V), §1 Status closing paragraph: "level $\approx1.3$". Severity: minor.** The certified base $\delta=1/55$ corresponds to $\varepsilon^k=10/55$, that is $k=\log(2/11)/\log\varphi^{-3}=1.18$. "About 150 GB at level 3" is an extrapolation taken from the combined note, not a measurement; say so. The claim that a period-two induction from $k_0=3$ needs bases at levels 3 and 4 (one for each parity) is right as a statement about an induction. It should add that the base is not the only missing piece. Conjecture 5.1 is stated for lune-free lattice points with bounded internal coordinate, while an induction needs the return relation on the whole tight core (gap 2 of §7), and needs the lune points controlled.

8. **§5.3 "Why period two is plausible", second bullet. Severity: minor (incorrect statement).** "Multiplication by $\varepsilon$ reverses the orientation of internal space" is false for the 2-dimensional internal space $\sigma(\mathbb C)$: multiplication by $\sigma\varepsilon=-\varphi^3$ is a rotation by $\pi$ composed with an expansion, which preserves orientation. It is true for the 1-dimensional internal line of $\mathbb Q(\sqrt5)$, where the squared radii and the test values live. The "internal window that is not centrally symmetric" is a half-line in that line (§3). *Repair:* replace the bullet by the argument of §3.

9. **Title. Severity: minor.** "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: …" reads as if finiteness were proved. Suggested: "Towards finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: …" or "Reductions for the finiteness of …". The status paragraph itself is clear: (B) is open, and proved, computed and conjectured results are kept separate. The one blur is that item 2 groups Theorem 4.2, which rests on an exact computation now reproduced, with Corollary 4.4, which rests on a certified closure and checkers. Both labels are accurate.

10. **§7 gaps item 5 ("Not refereed"), Appendix A. Severity: cosmetic.** Update it to point to this report. Table 3.1's "two of them contain the tight class and the lens corner" was not checked by me.

## 2. The crux: four windows (claim 4)

**Does the proof of Theorem 4.2 (combined note) survive with 34 critical points outside $W$?** Yes, with no extra argument. I re-read the proof line by line:
- Lemma 2.1(4), "tangency only at critical points", is never used in it. It is used only to explain the implementation's rule for tangencies.
- In Definition 4.1 an external tangency of $\alpha$ with $\partial D_S$ is a one-point, hence degenerate, component of $\alpha\cap D_S\setminus\operatorname{int}W$. It needs no image wherever it lies. Circles of equal radius have no internal tangencies.
- In Step 1, a point $y\in S(X)\cap K'\setminus W$ lies in $\operatorname{int}D_S$, so a neighbourhood of $y$ on any arc through it lies in $\operatorname{int}D_S\setminus W$, and the component is non-degenerate. Nothing depends on where tangency points are.
- Generic points avoid $K'$ (Lemma 3.4), and strict chains use open disks.
- The finiteness of the face count $F$ follows from $K'$ being a finite union of arcs.

So the remark in §1 of the note, that the proofs "never use which critical points carry windows", is correct. It deserves one sentence of justification (above), because it is the crux of the reduction.

**Do the checkers treat tangencies outside $W$ correctly?** In `refchk.py`, and therefore in `refchk_tight.py`, step (K3) skips every circle $c$ with $|c-p|^2\ge4r_c^2$, an exact test. This is independent of the windows and implements "no image for a one-point intersection". `intersect_arc` keeps only non-degenerate pieces. The four-window adaptation is a three-line diff that filters the window list to the four tight points (I diffed both `refchk_tight.py` and `chk_tight.py` against their originals). The `rcut_sel` logs report `tangent_circles=2` and 45 or 44 `tangent_skips` for rows 1 and 2.

**Classification of Table 4.2:**
- $(0,2,-1,0)$ and $(5,-1,4,0)$: **certified**.
  - I re-ran `refchk_tight.py` on both arc files: VALID, with 50 612 and 618 044 images and 0 uncovered, 48 s and 565 s.
  - Negative tests on row 1: deleting 20 random arcs gives INVALID (216 uncovered). The *38-window* closure `sharp2/rc_w0.txt`, checked against the four-window checker, gives INVALID (4 788 uncovered). So the window restriction is really enforced.
  - The logs of `chk_tight.py` say VALID for both; I did not re-run it.
- The seven other rows: **computed-not-certified**. They rest on `rcut_sel` alone, with floating-point orderings and the run-time margin. The table counts match the logs.

I did not write an independent closure generator, so "my own exact implementation" of the certificate is not provided. Certification rests on the earlier referee's interval checker, which is independent of `rcut`.

Hence Corollary 4.4 holds as stated, modulo the certified row: for every $r<r_c$, $GG_5(r)$ is finite if and only if its orbits meet the four windows at $\pm E,\pm\bar E$ in uniformly boundedly many points. Theorem 6.1 is correct.

## 3. Assessment of the norm $-1$ explanation and the $n=12$ prediction

**The two embeddings.** Write $\sigma\colon\zeta\mapsto\zeta^2$. The real subfield $\mathbb Q(\sqrt5)$ has the conjugation $\varphi\mapsto-1/\varphi$.
- A germ $\zeta^jz+t$ becomes $\zeta^{2j}\sigma z+\sigma t$ internally, so a rotation by $2\pi j/5$ becomes a rotation by $4\pi j/5$. This is harmless.
- Multiplication by $\varphi$ is: physically $\times1.618$; internally $\times(-0.618)$, a contraction composed with the rotation by $\pi$.
- Multiplication by $-1/\varphi$ is: physically a contraction composed with the rotation by $\pi$; internally $\times\varphi$, a pure expansion.
- Multiplication by $\varepsilon=\varphi^{-3}$ is: physically $\times0.236$; internally $\times(-4.236)$.

The coordinator's first claim is therefore true: $z\mapsto P+\varepsilon(z-P)$ acts on internal coordinates as an expansion by $\varphi^3$ composed with the point reflection through $\sigma P$.

**Where the mechanism as proposed goes wrong.**
- In the plane, a point reflection is the rotation by $\pi$. It preserves orientation, and it preserves the Hermitian quantities $|\sigma u|^2$.
- The half-plane tests near $E$ are *physical*: $\lambda_Q(Y)<0$ with $\lambda$ independent of $k$ (Lemma 2.1). Since $\varepsilon>0$ they are preserved exactly by $\varepsilon$.
- There is no tangent-line or half-plane test in internal space whose side a point reflection could flip.

So "side of a tangent line, not invariant under point reflection" is not the mechanism.

**What the mechanism is.** All tests are signs of real numbers in $\mathbb Z[\varphi]$, whose internal space is the *line* $\mathbb R$. On that line $\sigma\varepsilon=-\varphi^3$ does reverse orientation. Two facts make this matter:
- **Total positivity:** $\sigma(|u|^2)=|\sigma u|^2\ge0$ for every $u\in\Lambda$;
- **alternating level defect:** $\sigma(r_c^2-r_k^2)=(-\varphi^3)^k/10$.

For a test at a far point, $u=h(Q)-p$, write the zoomed offset as $\tilde\delta=\varepsilon^{-k}\cdot10(|u|^2-r_k^2)\in1+10\mathbb Z[\varphi]$. This is physically $O(1)$ exactly when the cut meets the zoomed core. Exactly,
$$\sigma\tilde\delta-1=(-\varphi^{3})^{-k}\bigl(10|\sigma u|^2-10(4-\varphi)\bigr),$$
so $\operatorname{sign}(\sigma\tilde\delta-1)=(-1)^k\operatorname{sign}(|\sigma u|-|\sigma w|)$.

Every near miss that is internally larger than the critical vectors ($|\sigma u|>1.5434$) therefore has $\sigma\tilde\delta-1$ of sign $(-1)^k$. There are only finitely many totally positive $|u|^2$ near $3+\varphi$ with $\sigma|u|^2<4-\varphi$, so for large $k$ every non-critical near miss is of this kind.

Hence, for large $k$, no non-critical cut offset occurs exactly at two consecutive levels. The only common offset is $\tilde\delta=1$, the tangent half-plane of the critical tests. The condition is invariant under $\varepsilon^2$, which is totally positive. The 1-dimensional internal "window" of offsets is a half-line pointing in direction $(-1)^k$; this is the precise form of "a window that is not centrally symmetric".

What the argument does and does not show:
- It is a necessary-condition argument about exact cut offsets. It does not prove that period-one matching of return *sets* fails, since cuts need not recur for the combinatorics to recur.
- It does not prove period two either: §5.4 of the note finds that lines do not recur at period two, which the argument permits but does not force.
- An extra check: the unit $-\varepsilon$ (internally a pure expansion, physically a point reflection about the critical point) also fails. Comparing $R_{k+1}(Q,-\eta)$ with $-R_k(Q,\eta)$ on $S_E$ gives 34/811, 64/811 and 80/811 at $1\to2$, $2\to3$ and $3\to4$. This fits the requirement that the unit be positive in *both* real embeddings.

**Verdict: partially correct.** The conclusion (period one exactly when the level unit is totally positive, that is has norm $+1$ for a positive unit; otherwise period two) and the role of $N(\varepsilon)=-1$ are right. The geometric mechanism (point reflection in the 2-dimensional internal plane flipping half-plane sides) is not. The correct mechanism is the orientation reversal on the 1-dimensional internal line of the real field, combined with total positivity of Hermitian norms. The predictions follow:
- $n=8$ (unit $\sqrt2-1$, norm $-1$): period two;
- $n=10$ (unit $\varphi^3$, norm $-1$): period two;
- $n=12$ (unit $2-\sqrt3$, totally positive): period one.

**The $n=12$ test (exact, my code `r12.c`).** Setting:
- $\zeta=e^{i\pi/6}$, $\zeta^4=\zeta^2-1$;
- levels $r_m^2=40-22\sqrt3-\varepsilon^m/10$ with $\varepsilon=2-\sqrt3$. These are non-norm radii, since $\varepsilon^m/10\notin\mathbb Z[\sqrt3]$;
- 48 critical points, minimal distance 0.196, core constant $C=0.09$;
- 265 starts $p^\ast+\varepsilon^m\eta$ with $|\eta|\le0.09$ and $|\sigma'\eta|\le100$, where $\sigma'\colon\zeta\mapsto\zeta^5$;
- first-return sets compared in zoomed coordinates.

Excursion medians are 332, 3 382, 31 406, 284 116 and 2 581 034 at $m=0,\dots,4$. They grow by about 9 per level, so the dynamics at $p^\ast$ is not rigid.

| | $m\to m+1$ | $m\to m+2$ |
|---|---|---|
| $0\to$ | 134/265 | 130/265 |
| $1\to$ | 233/265 (lune-free at 1: 72/72) | 233/265 |
| $2\to$ | **265/265** | 265/265 |
| $3\to$ | **265/265** | |

At levels 2–4, 147 of the 265 starts have at least one non-linear return (2 816 non-linear returns in all), so the agreement is not the trivial rigidity of the non-tight $n=5$ classes. For $n=5$, consecutive levels at the tight point give 0–14 agreements out of 811 at every level pair. **The prediction (period one for $n=12$) is confirmed on this sample, levels 2–4.** The engine's level-1 orbit of one start, 23 292 points, matches the repository engine `tdcsg-orbit orbit -n 12` exactly. Not done: other $n=12$ critical points, levels $\ge5$, and $n=8$ and $10$.

## 4. Exact record of what I recomputed

My own programs in `reflim/`. Everything is exact in $\mathbb Z[\varphi]$ or $\mathbb Z[\sqrt3]$, with `__int128` signs; floating point is used only as a filter, with a $10^{-6}$ relative safety factor before the exact test.

- **Engine cross-checks.** The full orbit of $E+\varepsilon(-3,-1,-1,-3)$ at level 1 has 71 817 points, both in my `r5n` and in the repository `tdcsg-orbit orbit -n 5 --r2 re:41/10,4/5` (run read-only). For $n=12$ see §3.
- **Samples.** `gen5.py` reproduces $S_E$ (811 points) and $S_{21}$ (798 points) exactly, the same as the author's start files.
- **Example $(E,(-3,-1,-1,-3))$.**
  - Excursions: 156, 60 861, 21 066, 16 128 171 and 3 473 926 at levels 1–5.
  - Return sets have 6, 36, 6, 46 and 6 points.
  - Levels 1, 3 and 5 are equal; levels 2 and 4 differ. Level 3 is lune-free.
- **$S_E$, all 811 points, levels 1–4.** The largest level-4 excursion is 18 097 966 points, with no cap reached.
  - Consecutive levels: $1\to2$ 0, $2\to3$ 14, $3\to4$ 14. Among the 244 points that are lune-free at level 3, 14 agree $3\to4$.
  - Two levels apart: $1\to3$ 185, $2\to4$ 518. Lune-free at level 2: 124/124 agree $2\to4$.
- **$S_E$ level 5 (the author's 117 starts).**
  - $3\to5$: 117/117, all lune-free at 3. $4\to5$: 0/117.
  - One point needed a cap above $6\cdot10^6$ (9 221 015 points) and still agrees.
- **$S_{21}$ tight (84 points).**
  - $3\to4$: 0/84, including 0/32 among the points lune-free at 3. $2\to4$: 52/84, with lune-free 20/20.
  - Level 5: 12 points are uncapped (excursions of about 3 473 924). For them $3\to5$ is 12/12 and $4\to5$ is 0/12.
- **$S_{21}$, all points, levels 1–3.**
  - Non-tight: 610/714 agree at $1\to2$ and $1\to3$, and 714/714 at $2\to3$. The lune-free counts are 216 at level 1 (all non-tight) and 718 at level 2 (20 of them tight). These are the note's numbers.
  - An early version of my program, which stopped scanning critical points at the first core hit, under-counted lunes. The note's lune definition, which tests all critical points within zoomed distance 3, is the one used above.
- **Table 4.1.** `skel.py`, exact BFS at $r_c$ and 50-digit margins:
  - classes of size 559, 42, 5 and 3 with 3, 2, 4 and 2 critical endpoints;
  - binding margins 0.011682 (giving $k_0=4$) and 0.07966 ($k_0=2$); the outside classes have margin $\ge1.755$;
  - the tight class exceeds a cap of $2\cdot10^5$;
  - also checked: $0.0236\varepsilon^k\ge r_c-r_k$, and $|\sigma w|=1.5434$, $1/(20r_c)=0.02327$, the arguments $\pm9.7323^\circ+36^\circ j$, and $s=2.52626$.
- **Invariance of the orbit of $E$** (`psi5.c`; orbit of $E$ at $r_c$ to $2\cdot10^7$ points; images tested only when their internal radius is below $0.5\times$ the minimal frontier radius):

  | $\rho$ | $m=1$ ($\varphi^{-3}$): found | $m=2$ ($\varphi^{-6}$): found |
  |---|---|---|
  | 0.2 | 308/375 | 26/26 |
  | 1.0 | 49 428/63 013 (21.6% fail) | 4 711/4 711 |
  | 1.2 | | 5 910/5 986 |

  The failures at $m=1$ are exact (issue 6).
- **Certificates.** `refchk_tight.py` re-run on rows 1 and 2 (VALID) and the two negative tests, all in §2.

## 5. Referee's suggestions

1. **Make Conjecture 5.1 sharper and test it where it can fail.** Restrict the evidence to tight points and use one fixed sample across all level pairs. The cheapest new test is level 6 on the 129-point family against level 4. A stronger test is level 5 on a *random* subset of the 72 large $S_{21}$ tight points, with a disk-backed hash.
2. **Prove the parity obstruction.** The identity of §3 gives a short exact lemma: for large $k$, the set of exact zoomed cut offsets at consecutive levels meets only in $\tilde\delta=1$. It belongs in §5.3 in place of the orientation bullet. It also gives a concrete target for period two: show that the map $\tilde\delta\mapsto\varepsilon^2$-conjugate on offsets lifts to a germ correspondence $h_k\mapsto h_{k+2}$.
3. **Use $n=12$ as the model case.** Period one holds there from level 2 in my sample, and excursions are about 9 times smaller per level than for $n=5$. A renormalization proof of the return relation, the referee's route of the combined note, step (III), should be attempted for $n=12$ first, where no parity complication arises. Run the same rigidity computation (Table 4.1) for the 48 critical points of $n=12$, to see which points carry infinite skeleta.
4. **Test the $n=8$ and $n=10$ predictions** with the same engine: change $\Phi_n$, the unit and the critical points. Period two is predicted for both. A period-one result for either would refute the norm explanation.
5. **Close the Proposition 3.1 gap** by the finite check of issue 3, and **compute $T_W$ and $\beta_W$** for the certified four-window row, so that $m_k$ becomes explicit.
6. **Certify more rows of Table 4.2.** The C or Lean checker would make rows 3–9 cheap. Rows with smaller windows matter for (R-bulk-t).

## 6. What I did not check

- The closure samples $S_{\rm cl}$ of Table 5.2: $1\to2$ 0/2 436, $2\to3$ 0/2 564, $1\to3$ 308/3 256.
- The closure-mode validation against Table 6.1 of the combined note.
- The claim "0 matches for each of the four symmetries".
- §5.4 (cut-line statistics) and the growth exponents of §5.3.
- Table 3.1's cycle structure.
- The $\rho_W$ column of Table 4.2.
- `chk_tight.py`, which I did not re-run.
- The rows of Table 4.2 other than the first two.
- Whether $\varphi^{-6}$ invariance of $O(E)$ near $E$ holds exactly, which is open.
- The $n=12$ test covers one critical point, one sample of 265 points and levels up to 4; $n=8$ and $n=10$ were not run.
