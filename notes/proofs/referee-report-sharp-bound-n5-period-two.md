# Referee report: `sharp-bound-n5-period-two.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Period-two renormalization at the tight points of $GG_5$: exact tests on large
samples, a positivity lemma, and the remaining gap" (`sharp-bound-n5-period-two.md`, commit
`445e35a`). Companions consulted: `sharp-lower-bound-limit-system.md` §§1–2, 5–6 (tight points,
cores, first-return sets, lunes, levels, Conjecture 5.1, (R-bulk-t), (R-core-t)) and its referee
report, `sharp-lower-bound-n5.md` (Lemma 6.1, Theorem 4.3), `sharp-lower-bound-n12.md`
(Propositions 6.4, 8.1), `boundary-contact.md` (Theorems 3.1, 3.4), and the parallel notes
`sharp-bound-n5-conjugate.md`, `sharp-bound-n5-critical-orbits.md`, `sharp-bound-n5-invariant.md`.

## Summary

The proofs are correct. Every proof was checked line by line and every constant was re-derived
to at least 20 digits. The defects:

- constants rounded the wrong way: in Lemma 3.2(1) ($15.37\,\varepsilon\le3.628$ is false; it is
  $3.6284$) and in the list of Lemma 3.5 (each listed value is slightly above the true bound);
- a missing exception in the statement of Proposition 3.3(1) (it is in the proof);
- the remark after Lemma 3.6 about a "norm equation" is misstated, and summary item 5 called
  it proved;
- the summary called the independence of the statistics from the internal radius "explained
  (proved, Lemma 3.5)". Lemma 3.5 is proved; that it is the reason is a heuristic;
- a wrong remark in §5 item 2 (Conjecture 4.2 "in full generality" would bound all word maps);
- **a wrong conclusion in §6.6 and after Propositions 4.4 and 4.5.** The note compared orbit
  sets on all 38 cores. The relation $\sim_k$ of Propositions 4.4 and 4.5 lives on the four
  tight cores. Restricted to them, the author's own level-1 and level-3 partitions give, at
  $1\to3$, 711 agreements and 100 growths, with no shrinking at all. I computed the level-4
  partition of $S_E$, which the note says was out of reach. At $2\to4$ it gives 746 agreements
  and 65 growths, again with no shrinking. So hypothesis (M$_5$) of Proposition 4.5 is
  *supported* on the sample, not unsupported. The hypothesis of Proposition 4.4 is refuted at
  $k_0=1,2$, but by these partitions, not by the first-return data of §6.2 that the note cited.

I fixed all of these in the note and added a status line at its top. I wrote my own
exact-arithmetic program from the description in §2, without reading the author's code first.
It reproduced every first-return and partition figure I tested, count for count: all of $S_E$
(811 starts) at levels 1–4, $E$ at levels 1–5, and a random 30 at level 5 (§4).

On the line itself, I agree it is not closed. "Repairable in principle" is too generous for the
first-return formulation: Theorem 4.3 starts only at level 9, where no base can be computed or
certified. I recommend closing the first-return/lune-criterion formulation. Two things should be
carried forward. One is the monotone tight-orbit-relation formulation (Proposition 4.5), which
the new data favour. The other is the chord-run coordinate of the parallel notes, in which the
same problem has a proved uniform cut-off (§5).

## 1. Verdicts

| result | verdict |
|---|---|
| Lemma 3.1 (zoomed disk test (3.1)) | **correct** |
| Lemma 3.2 (positivity) | **correct after a constant fix**: $|D|\le15.37\,\varepsilon^k\le3.629$ (was $3.628$). The summary's sign statement now names $\sigma(\tilde\delta_k-1)$, not "the Galois conjugate of the offset" |
| Proposition 3.3 | **correct after a missing exception**: for $s=-1$ and $\lambda(\eta)>2$ the tests disagree only if $-\eta$ is not a lune point at level $k+m$ (as in the proof). The conclusion "totally positive, least $\varepsilon^2$" is right, and is correctly labelled a necessary condition for matchings induced by cuts |
| Lemma 3.4 (rescaled inclusion) | **correct** |
| Lemma 3.5 (lune lemma at low levels) | **correct**; listed bounds rounded down ($0.0835$, $0.4585$, $2.047$, $8.777$, $37.28$, $158.0$; were $0.084$, $0.459$, $2.05$, $8.78$, $37.3$, $158$). "Explains the independence from the internal radius" is downgraded to a heuristic reading |
| Lemma 3.6 | **correct** (the identity is elementary). The remark after it was **misstated**: exact cut arcs at levels $k$ and $k+2$ never coincide, and "$D(u')=\varepsilon^2D(u)$" is not the condition for equal limit lines. Rewritten and marked heuristic; summary item 5 adjusted |
| Conjectures 4.1, 4.2 | statements consistent with all data, mine included (§4) |
| Theorem 4.3 | **correct (conditional)**. Hypotheses are exactly what is used; persistence of lune-freeness in Conjecture 4.1 is not needed. "$\mathcal D_k$ non-empty only from level 9" is right for every $c_0$ compatible with the data (§3) |
| Proposition 4.4 | **correct (conditional)**; the conclusion is (R-core-t) **on lattice points** (now said). The remark "refuted for $k_0=2$ (§6.2)" cited the wrong evidence; refutation at $k_0=1,2$ now rests on tight-core orbit partitions (§4.4) |
| Proposition 4.5 | **correct (conditional)**. The remark "(M$_5$) not supported" is **wrong** for the tight relation; corrected (§4.4) |
| §5 item 2 | **wrong remark, fixed**: Conjecture 4.2 bounds one excursion; drifts add along an orbit |
| §6.2–§6.5 tables | **reproduced** exactly where re-run (§4); two statistics corrected (mean lune count at level 1 is $93.8$, not $94.0$; maxima "nearly", not exactly, the same on every band) |
| §6.6 | conclusion **wrong** (all-core instead of tight-core sets); corrected with the author's own data and my level-4 partition |
| Refutation of unrestricted period two at $2\to4$ | **confirmed**, including at $E$ itself |
| Verdict "repairable in principle, not closed" | not closed: agreed. Recommendation: close this formulation (§5) |

## 2. Issues

1. **Lemma 3.2(1), last constant.** $15.37\,\varepsilon=3.62836>3.628$. The sharper constant
   from the proof, $1.9+6\sqrt{4.618034+0.419821}=15.36710$, gives $3.62768$. Now
   "$\le15.37\,\varepsilon^k\le3.629$", with the intermediate expression written out.
   **Fixed.**
2. **Proposition 3.3(1), statement.** In the case $s=-1$, $\lambda(\eta)>2$, the proof
   correctly says "unless $-\eta$ is a lune point at level $k+m$". The statement omitted it.
   **Fixed.**
3. **Lemma 3.5, listed values.** With the lemma's constant $30.87$ the largest admissible $M$
   is $0.083503$, $0.458554$, $2.0473$, $8.7773$, $37.2861$, $158.0513$ for $k=4,\dots,9$. The
   note listed $0.084$, $0.459$, $2.05$, $8.78$, $37.3$, which are upper roundings of an upper
   limit. With the exact constant $20|\sigma w|=30.86724$ the values are marginally larger
   ($0.083511$, $0.458595$, …). **Fixed** (rounded down). The summary's "below $0.08$ and
   $0.46$" now says "at most $0.0835$ and $0.4585$".
4. **The "norm equation" remark after Lemma 3.6.** The zero set of (3.1) is an arc of a circle
   of zoomed radius $\varepsilon^{-k}r_k$. At level $k+2$ the radius is
   $\varepsilon^{-k-2}r_{k+2}$, so exact coincidence never happens. For the limit lines
   $\{20\operatorname{Re}(Y\bar v)=-\tilde\delta\}$, $v=\zeta^{-J}u$, equality needs $v'=cv$
   with $c\in\mathbb Q(\varphi)_{>0}$ and $\tilde\delta_{k+2}(u')=c\,\tilde\delta_k(u)$. The
   note's "$D(u')=\varepsilon^2D(u)$" (equal offsets) gives the same line only for $c=1$. But
   $c=1$ forces $u'=\zeta^{J'-J}u$, hence $D(u')=D(u)$, which is impossible. Whether the
   general system has solutions was not examined by the author or by me. **Rewritten, marked
   heuristic**; summary item 5 no longer calls it proved. The point that matters, that a
   matching of return relations need not come from a matching of cuts, is unaffected.
5. **"Explained (proved, Lemma 3.5)."** Lemma 3.5 is a sufficient condition for the absence of
   lunes. That it does not apply at levels $\le5$ is consistent with the observed independence
   from the internal radius, but it does not prove it. The dynamics depends only on the
   physical position, and each band is a roughly uniform sample of positions in the zoomed
   disc. That is the likely cause; it is also a heuristic. **Reworded.** The lune decay
   "by a factor close to $\varepsilon$" is a factor between $0.16$ and $0.36$. **Reworded.**
6. **§5 item 2.** The note said Conjecture 4.2 "in full generality (all starts) would by itself
   bound all word maps at lattice points". Conjecture 4.2 is already stated for every zoomed
   tight-core start, and it bounds the internal drift of *one* excursion relative to the start.
   Along an orbit the starts of successive excursions are the returned points, so the drifts add
   and nothing bounds the orbit. **Replaced** by a correct sentence.
7. **Proposition 4.4.** The hypotheses and the proof concern lattice points ($N_k$ is a supremum
   over lattice points). (R-core-t) in `sharp-lower-bound-limit-system.md` is stated with
   $\sup_x$, and no passage from lattice points to all points is given. **Conclusion now says
   "on lattice points"**, as Proposition 4.5 already did. The remark "the hypothesis is refuted
   for $k_0=2$ (§6.2)" used first-return data. A change of $R_k(\eta)$ does not imply a change
   of the orbit class of $\eta$ (I checked: $R_4(\eta)$ lies inside the level-2 tight orbit set
   of $\eta$ for all 811 starts). The hypothesis *is* refuted at $k_0=1$ and $k_0=2$ by the
   tight-core partitions of §4.4. **Fixed.**
8. **§6.6 and the remark after Proposition 4.5.** See the summary and §4.4. **Fixed**, and the
   summary's comparison with $n=12$ (item 1) now says that on tight orbit classes every change
   seen is a growth, as for $n=12$.
9. **Statistics.** The author's program counts a lune point twice when it is a core neighbour of
   the start (`first_return` adds it in the neighbour loop and again in the final loop over
   returned points). This changes the level-1 mean from $93.84$ to $94.0$ (123 starts off by one)
   and one level-2 count. Lune-freeness is unaffected. **Fixed** ($93.8$). The largest excursions
   differ slightly between bands ($103\,340$ on $S_E$, $103\,351$ on $A_{200}$, $A_{400}$), so the
   note's "the same maxima on every band" is now "nearly the same". The near-critical counts
   of §6.4 exclude the start and the returned points; mine include them, which explains a
   difference of about $|R_k|$ in the means. No change needed.
10. **§6.5, "a direct instance of Lemma 3.6".** Lemma 3.6 is the commutator identity. The
    observation illustrates the remark after it. **Reworded.**

## 3. Proof checks in detail

- **Lemma 3.1.** $h(x)-p=u+\zeta^J\varepsilon^kY$; expanding and using
  $10r_k^2=10r_c^2-\varepsilon^k$ gives (3.1) exactly.
- **Lemma 3.2.** (2): $D=10t$, $t=|u|^2-(3+\varphi)\in\mathbb Z[\varphi]\setminus0$, so
  $|D|\,|\sigma D|\ge100$. $\sigma$ commutes with complex conjugation, so
  $\sigma|u|^2=|\sigma u|^2\ge0$ and $\sigma D\ge-10(4-\varphi)=-23.8197$. Negative $\sigma D$
  forces $|D|\ge10/(4-\varphi)=4.198213$. (1): on the zero set,
  $|\tilde\delta|\le6|u|+0.9\varepsilon^k$. For $D\ge4.1982$,
  $(1.9+6\sqrt{4.618+D/10})/\sqrt D$ is decreasing, so the right side is at most
  $3.6287\sqrt{D/4.1982}<D$. (3): $\sigma(\varepsilon^{-1})=\sigma(\varphi^3)=-\varphi^{-3}$. The
  consequence $\mathcal O_k\cap\mathcal O_{k+1}=\varnothing$ follows.
- **Proposition 3.3.** (1) is the case analysis of $\lambda+10\varepsilon^k|\eta|^2$ against
  $\lambda+10\varepsilon^{k+m}|\eta|^2$ and $\lambda(-\eta)=2-\lambda(\eta)$. (2) is Lemma
  3.2(3). The offset condition does not depend on $s$, since negating $Y$ maps a cut with base
  $u$ to one with base direction $-u$ and the same offset. (3): $s\varepsilon^m$ is totally
  positive iff $s=+1$ and $m$ is even, because $\sigma\varepsilon<0<\varepsilon$.
- **Lemma 3.4.** $Q+\varepsilon^k\eta=Q+\varepsilon^{k+j}(\varepsilon^{-j}\eta)$ with
  $|\varepsilon^{-j}\eta|\le0.3$, and $r_k<r_{k+j}$, so `boundary-contact.md` Theorem 3.1
  applies.
- **Lemma 3.5.** $\lambda=1+10t$ gives $N(\lambda)\equiv1\pmod{10}$, so $|N\lambda|\ge1$, and
  $|\sigma\lambda|\le20|\sigma w||\sigma Y|+1$. A lune at $|Y|\le3$ has $|\lambda|<90\varepsilon^k$.
- **Lemma 3.6.** Both sides expand to the stated difference; $\Psi R_p\Psi^{-1}$ is the
  rotation by $\zeta^{-1}$ about $\Psi(p)$.
- **Theorem 4.3.** $|\sigma Y|=\varphi^{-3k}|\sigma z-\sigma Q'|\le|\sigma\eta|+c_0+5.06\varphi^{-3k}$,
  and $5.06\varphi^{-3k}\le1$ for $k\ge2$ ($\varphi^6=17.94$). With $|\sigma\eta|\le M_k$ this is
  exactly the bound of Lemma 3.5 at equality. $M_{k+2}>M_k$ gives the induction. Non-emptiness:
  $\mathcal D_k\ni0$ iff $M_k\ge0$. $M_8\ge0$ needs $c_0\le36.29$, but the data force
  $c_0\ge47.1$ (largest drift $47.16$ at level 4, minus $|\sigma E|\varphi^{-12}<0.01$). And
  $\mathcal D_9\ne\varnothing$ for every $c_0\le157.05$. So "non-empty only from level 9" holds
  for every $c_0$ consistent with the data and with the observed bound $48$:
  $M_9=109.05$, $M_8=-11.71$. The growth rate $\varphi^{3k}/2778.3$ is right.
- **Proposition 4.4.** Exact period two gives, for $k\ge k_0$, the class of a tight core point
  at level $k$ equal (in zoomed coordinates) to its class at level $k_0$ or $k_0+1$. Finiteness
  of $GG_5(r_{k_0+1})$ gives $N_{k_0+1}<\infty$, and group monotonicity
  (`boundary-contact.md` Theorem 3.4) gives $N_{k_0}<\infty$.
- **Proposition 4.5.** Under (M$_5$) the relations on each parity class increase, the eventual
  relation is their union, and each class at level $k\ge k_1$ lies in an eventual class.
- **§5 item 3.** The covering argument of `sharp-lower-bound-n5.md` Theorem 4.3 puts a lattice
  point with $|\sigma\eta|<4\varphi^3/f=16.94/f$ in every disc of radius $f$, so "inradius at
  least about $16.9/M_k$" is right.

## 4. Independent computation

**Program.** `ref.c` (scratch, not committed), written from §2 of the note before I read the
author's programs. Points are integer 4-vectors. $|w|^2=A+B\varphi$ is computed exactly. Signs of
$x+y\varphi$ are decided with 128-bit integers. Disk, core and lune tests are exact; floating point
only preselects candidate critical points, with margin $10^{-8}$. First returns are found by
breadth-first search from the start, recording core points and not expanding them. There is no
component cache: each start is searched from scratch. That is an independent route to the same
sets. The "within $3\varepsilon^k$" test of the lune count is exact. Orbit partitions come from
**plain orbit enumeration** (all of $O_{r_k}(x)$, then its core points), not from closing the
first-return graph. Samples: my own enumeration of $\{\eta:100|\eta|^2\le9,\ |\sigma\eta|\le50\}$
gives 811 points, as stated. The critical points come out in the same lexicographic order:
$E$ is 19 and $\bar E$ is 7.

**Validation.** $R_k(E+\varepsilon^k(-3,-1,-1,-3))$ has $6,36,6,46$ points, with excursions
$156$, $60\,861$, $21\,066$, $16\,128\,171$. The level-1 orbit of that point has $71\,817$ points.
At levels 1–3 every first-return set and every excursion size of $S_E$ is identical to the
author's files, start by start. The level-1, 2 and 3 orbit partitions of $S_E$ (on all cores)
are identical to the author's closures: 154, 150, 148 blocks, with at most 1 936, 1 406, 1 582
core points.

### 4.1 The counterexample (task a), all of $S_E$

| comparison | agree | growth / shrink / incomparable |
|---|---|---|
| $1\to2$ | 0/811 | |
| $2\to3$ | 14/811 | |
| $3\to4$ | 14/811 | |
| $1\to3$ | 185/811 | 9 / 379 / 238 |
| $2\to4$ | **518/811** | **62 / 223 / 8** |
| $-\varepsilon$: $R_{k+1}(-\eta)=-R_k(\eta)$, $k=1,2,3$ | 34, 64, 80 of 811 | |

At $E$ itself, $R_2(0)$ has 12 points and $R_4(0)$ has 10, and $R_2(0)=R_4(0)\cup\{(8,(-10,-4,-4,-10)),(20,(-6,4,-6,0))\}$.
So unrestricted period two fails at $E$, exactly as stated. Changed points at $2\to4$: 1 600, of
which 1 566 are non-linear; 17 changes involve linear returns. By type and size: shrink by 2:
157, shrink by 4: 66, grow by 10: 36, grow by 34: 10, all as in §6.2.

### 4.2 Non-monotonicity (task b)

On all 811 starts (not only a sample), both growths (62), shrinkings (223) and incomparable
changes (8) occur at $2\to4$. Confirmed.

### 4.3 Lune criterion (task c)

- $2\to4$, all 811 starts: 124 are lune-free at level 2, and all 124 agree at $2\to4$ (none
  agrees at $2\to3$). All 124 are still lune-free at level 4. All 293 changes have a lune at
  level 2. 394 of the 687 starts with lunes still agree.
- Lune-free counts at levels 1–4 are $0$, $124$, $244$, $571$. Mean lune counts are $93.8$,
  $18.3$, $6.54$, $1.04$. The largest drift $\max_z|\sigma z|\varphi^{-3k}-|\sigma\eta|$ is
  $46.78$, $47.08$, $47.15$, $47.16$. Median excursions are $2\,254$, $32\,783$, $436\,912$,
  $5\,761\,134$; maxima $7\,674$, $103\,340$, $1\,341\,227$, $18\,097\,966$.
- **Level 5, my own random sample** (30 starts of $S_E$, seed 11, cap $9\cdot10^7$ points):
  19 capped, 11 uncapped. All 11 uncapped agree at $3\to5$: 5 were lune-free at level 3 (and
  are still lune-free at level 5) and 6 had lunes. None agrees at $4\to5$, and 6 agree at
  $1\to5$. **The selection bias the note describes is real and strong.** The capped starts
  had on average 11.8 lune points at level 3, against 3.7 for the uncapped ones, and 0 of 19
  agreed at $1\to3$, against 6 of 11. So the level-5 evidence says only that small level-5
  excursions are period-two stable. The note states this correctly in §6.3. Summary item 2
  ("349 lune-free starts … no failure") is correct as a count, but its $k=3$ part (54 starts)
  is a size-selected sample.

### 4.4 Orbit partitions on the tight cores (new)

I computed the level-4 orbit partition of all of $S_E$. It has 148 blocks, the largest orbit
has $2.09\cdot10^8$ points, and no orbit was capped. Orbit sets of the starts, intersected with
the cores:

| comparison | all 38 cores: agree (g/s/i) | **tight cores only**: agree (g/s/i) |
|---|---|---|
| $1\to2$ | 0/811 | 14/811 (51/45/701) |
| $2\to3$ | 14/811 | 14/811 (49/45/703) |
| $3\to4$ | 14/811 | 14/811 (45/45/707) |
| $1\to3$ | 124/811 (6/534/147) | **711/811 (100/0/0)** |
| $2\to4$ | 342/811 (4/404/61) | **746/811 (65/0/0)** |

The $1\to3$ tight-only figures also follow from the author's own closure files. Tight classes met
by $S_E$: 154, 150, 148, 148 at levels 1–4, largest 552, 552, 552, 560 points. Growth sizes at
$2\to4$: 8 points (60 starts), 88 (1), 540 (4, a small class merging into the largest).

So on this sample the tight orbit relation is exactly what Proposition 4.5 assumes: a monotone
coarsening with period two, $\sim_k\subseteq\sim_{k+2}$, with class sizes flat over four levels.
Exact period two of the relation (Proposition 4.4) fails at $k_0=1$ and $k_0=2$, but the
failures are growths, and their number falls (100, then 65; 52 starts change at both steps).
This is the same picture as for $n=12$. The non-monotone behaviour seen in §6.2 and in the
all-core sets comes from first-return sets and from the non-tight cores, which drop out of
$\sim_k$.

### 4.5 The identities at $E$ (task d)

Excursions of $\eta=0$ at levels 1–5: $1\,713$, $21\,091$, $258\,837$, $3\,681\,037$,
$49\,301\,326$, with lune counts 42, 10, 8, 0, 0. Exactly: $R_1=R_3=R_5=A$ (10 points),
$R_4=-A=-R_3$, and $R_2=-A\cup\{$the two non-tight points above$\}$. Level 6 was not attempted:
the note reports more than $1.8\cdot10^8$ points, which my 10 GB limit does not allow.

Geometry of $A$, not in the note: apart from $\eta=0$ at $E$ and at $\bar E$, the eight points
of $A$ lie on lines through the tight point in the directions $\zeta^jE$ (or $\zeta^j\bar E$ at
$\bar E$), at $|\eta'|=\varphi^{-5}|E|$ or $\varphi^{-4}|E|$. One of them is on the chord line
itself, $\eta'=-\varphi^{-5}E$. The $\bar E$ half is the complex conjugate of the $E$ half. The
$-\varepsilon$ identity does **not** extend to other chord-direction starts. On the 60 starts of
$S_E$ with $\eta\in\mathbb R\zeta^jE$ it holds for 2, 3, 4 of 60 at $1\to2$, $2\to3$, $3\to4$.
It is special to $\eta=0$.

## 5. Assessment

**Is the verdict right?** "Not closed" is right. "Repairable in principle" overstates it for this
formulation. The note's gap list, item by item:

1. *Renormalization step (Conjecture 4.1).* This is the whole problem, and the note offers no
   mechanism for it. Lemma 3.6 shows that it cannot be a conjugacy of generators. Proposition
   3.3 gives only a necessary condition.
2. *Internal drift.* Plausible and well supported (drift $\le47.2$ on 811 starts at four
   levels), but not by itself useful (issue 6).
3. *Generic points.* This is the face-inradius problem, open since `sharp-lower-bound-n5.md`.
   No progress.
4. *Bases.* Theorem 4.3 starts at level 9, because $\mathcal D_k$ is empty below. Excursions
   grow by a factor of about 13.5 per level, so level 9 is about $10^{12}$ points per
   excursion. Certified finiteness is available only to level $\approx1.18$. This item cannot be
   met by computation, and the route has no other way to meet it.
5. *(R-bulk-t).* Untouched.

So the first-return/lune-criterion route needs a proof of item 1 at all levels from a small
one, plus items 3 and 5. **I recommend closing this formulation.** Keep Lemma 3.2 and Lemma 3.5
as tools: they are clean and correct.

**What survives.** Section 4.4 changes the picture. On the tight cores the orbit relation is
monotone with period two on all data, with class sizes flat at about 552–560. That is
hypothesis (M$_5$) of Proposition 4.5, and Proposition 4.5 needs no base level and no lune
criterion. The two inputs are monotone coarsening (M$_5$) and bounded eventual classes
(L$_5$). This is the formulation that worked as a reduction for $n=12$
(`sharp-lower-bound-n12.md` §8). If work continues on renormalization at the tight points, it
should continue there: a proof attempt for (M$_5$), and the level-5 partition test at $3\to5$
on a sample, which needs larger memory than 10 GB.

**The identity at $E$.** Period one by $-\varepsilon$ at $\eta=0$ alone, with returns on the
chord directions at $\varphi^{-4}$ and $\varphi^{-5}$ scales, matches the self-similarity of the
golden chord rotation. In the conjugate note the exit index is $(F_{3k+7}-1)/2$, exactly at
levels 0–6, and the exit side alternates with the parity of $k$. That is the same
"$-\varepsilon$, with a flip" behaviour. A provable target is a single-orbit statement like
Theorem 6 of the conjugate note: "$R_k(0)=(-1)^{k-3}A$ for all $k\ge3$". A proof would have to
control the whole excursion of $E$, of which the chord is a small part (millions of points at
level 4). Since the identity fails for other chord-direction starts, it would not extend to the
tight core. It is a good test case, not a route to (B).

**Comparison with the parallel lines.** `sharp-bound-n5-invariant.md` proves that every chord
run, at any offset, ends within $5.86/\delta$ steps. Its gap is the number of runs a word can
chain through the $\delta$-windows at the breakpoints. `sharp-bound-n5-critical-orbits.md`
gives the holes in closed form, of width $\delta/\sqrt5+O(\delta^2)$. In that coordinate:

- the window size $\delta_k=\varepsilon^k/10$ is the zoom of this note;
- the dynamics between windows is a one-dimensional golden rotation with an exact
  $-\varphi^{-1}$ self-similarity;
- the cut-off is already proved for every start, which this note lacks (its item 3).

The open problem there, bounding chaining by first returns to breakpoint windows, is the same
renormalization question. But it is posed on a one-dimensional skeleton with explicit
renormalization, rather than on 811-point samples of a two-dimensional core. I think that is
the better coordinate. The natural bridge is to test whether the 8- and 88-point growths of
§4.4 are produced by chord-run chaining.

## 6. What I did not check

- The bands $A_{100}$, $A_{200}$, $A_{400}$ (I compared maxima against the author's files
  only).
- The $S_{21}$ closure in §2.
- The author's level-5 runs on 150 + 40 starts. My own level-5 sample is smaller (30) and has
  a lower cap ($9\cdot10^7$).
- Level 6 anywhere.
- The cited results (orbit monotonicity, Theorem 4.2 of the limit-system note, `sharp-lower-bound-n12.md`
  Propositions 6.4, 8.1) were taken as refereed.
- Floating point in my program only preselects candidates and computes the drift and
  $|\eta|$-direction statistics. Every decision that enters a set comparison is exact.
