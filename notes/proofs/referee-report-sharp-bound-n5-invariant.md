# Referee report: `sharp-bound-n5-invariant.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: conserved quantities, the
chord-strip mechanism, and a uniform $1/\delta$ cut-off" (`sharp-bound-n5-invariant.md`, commit
`a3ff765`). Companions consulted: `sharp-bound-n5-conjugate.md` ("line 1") and its referee report,
`sharp-bound-n5-critical-orbits.md` (Theorem 2, Proposition 2.3, Table 2.1, Theorem 4),
`critical-radius-n5.md` §§3–4 (Lemma 4.1), `boundary-contact.md` Theorem 3.4, and `../engine.md`.

## Summary

The proofs are sound. Every line of Propositions 1–3, Lemmas 4–6, Theorem 7 and Corollary 11 was
checked. Every exact identity was recomputed in $\mathbb Z[\zeta]$, and every constant was
re-derived to at least 20 digits. The new theorem, the uniform cut-off of chord runs (Theorem 7),
is correct. Its key identity, that the two binding test centres at the breakpoint $-\varphi^{-1}$
are symmetric about it (Lemma 5), holds exactly.

The defects are of three kinds.
- **Small gaps and constants.** One constant was rounded down. One proof step was missing (Lemma 6).
  The domain of the theorem was stated as "every point of the plane", but runs are defined only
  for $s_0\in[-1,1)$. The case $\delta>2/5$ of "no run is infinite" needed one sentence. All are
  fixed in the note.
- **Corollary 11 overstated.** Conjecture B$^\ast$ gives Conjecture A only for $0<\delta\le\delta_0$,
  not on all of $r<r_c$. That is enough for (B), and the chain to (B) is now written out. Fixed.
- **Conjecture B$^\ast$ was weaker than intended.** As written, the $D_i$ could be *any* chord runs.
  In that form B$^\ast$ is equivalent to Conjecture A for small $\delta$, so it reduced nothing.
  The structural form the evidence supports (the runs are segments of a word that realizes the
  map) is now the statement. In the same spirit, item 4 "one run is not enough" rules out only
  the constant $1$ in a single-run form of Conjecture B. Wording fixed.

I re-implemented the lifted search, the exact diameter, the shortest-word decomposition and the
run-length computation independently. Everything reproduces at the radii checked
($1/10,\ 1/30,\ 1/55,\ 1/80$, level 2). I then went one and two renormalization steps deeper
($\delta\mapsto\varphi^{-3}\delta,\varphi^{-6}\delta$). The chained extreme words persist with
the same number of runs (5–7), the same ratio to the best single run (1.45 and 1.11), and the same
$\delta M$. So the number of runs did not grow with depth in any case I could compute (§4).

## 1. Verdicts

| result | verdict |
|---|---|
| Proposition 1 (conserved squared radii) | **correct** |
| Proposition 2 (ambient group, $K=2(1-\zeta)\Lambda$, 20 classes) | **correct**; agrees with Theorem 4 of `sharp-bound-n5-critical-orbits.md` |
| Computation 2.1 (no finer congruence invariant) | **reproduced exactly** (all seven residue counts, both orbits) |
| Proposition 3 | **correct after a wording fix**: item 3 said "an unbounded set of lattice points"; the points $t_kE$ are physically bounded, their *conjugates* are unbounded. Item 2 is a correct but tautological meta-statement |
| Lemma 4 (tokens are translations) | **correct after a constant fix**: $2\varphi^2|\sigma E|=9.95959\ldots$, stated as the upper bound $9.959$; now $<9.960$ |
| Lemma 5 (bad interval at every offset) | **correct**; every identity checked exactly |
| Lemma 6 (golden-rotation gaps) | **correct after a missing step**: the arcs between consecutive indices are the gaps only because each has positive length, which needs $\varphi^{-m}<1/F_m$; now stated |
| Theorem 7(1) run length $\le F_m-1\le5.86/\delta$ | **correct after two domain fixes**: "every $X_0$ in the plane" is now "every $X_0=s_0E+hN$ with $s_0\in[-1,1)$"; the case $\delta>2/5$ of the closing sentence now uses monotonicity of $L$ in $r$ |
| Theorem 7(2) internal translation $\le58.4/\delta+9.6$ | **correct** (with the Lemma 4 constant, $9.960\cdot5.86=58.37$) |
| Theorem 7(3) the other three classes | **correct** |
| Corollary 11 | **correct after restricting the conclusion**: B$^\ast$ gives $M(r)\le c_0+N_0(58.4/\delta+9.6)$ for $0<\delta\le\delta_0$, and (B) follows by `critical-radius-n5.md` Lemma 4.1 (valid at every radius) and group monotonicity. Conjecture A on all of $r<r_c$ does not follow (issue 4) |
| Conjecture B$^\ast$ | **restated** (issue 5); plausible on the evidence (§4) |
| Computation 8 ($\sup L$, $\Sigma_1$) | **reproduced** at all ten radii ($\sup L$ for $h=0$ and over $h$); double precision, as labelled |
| Computation 9 ($M(r)$ lower bounds) | **reproduced** at $1/10$, $1/30$, $1/55$, $1/80$, level 2 (diameters exact) |
| Computation 10 (decomposition) | **reproduced** at $1/10$, $1/30$, $1/55$, $1/80$, level 2; two descriptive sentences corrected (issue 7) |
| item 4, "one run is not enough" | the numbers are right; the conclusion is now stated as "constant $C'\ge1.45$ needed" (issue 6) |

## 2. Issues

1. **Lemma 4 constant rounded down.** $2\varphi^2|\sigma E|=9.959593\ldots>9.959$. The bound
   "at most $9.959k$" was false for large $k$. **Fixed** to $<9.960k$. Theorem 7(2) survives:
   $9.960\cdot5.86=58.366\le58.4$. Other constants check: $2\sqrt5|\sigma E|=8.506508$,
   $|\sigma E|=2\sin72^\circ=1.902113$, $1-0.6181/\sqrt5=0.723577\ge0.7235$,
   $1/(\sqrt5\cdot0.7235)=0.618125\le0.6188$, $1.6188\sqrt5=3.61975\le3.620$,
   $3.620\varphi=5.85728\le5.86$, $5|\sigma E|=9.5106\le9.6$, $2\cdot0.4/\sqrt5=0.357771<\varphi^{-2}=0.381966$,
   and $5-3\varphi=0.1459<\rho$.
2. **Lemma 6, a missing step.** The proof lists the $q$ arcs from index $i$ to $i+1$ and concludes
   that they are the gaps between consecutive points. That holds only if every such arc has
   positive length, $1/q+e_{i+1}-e_i>0$. This follows from $|\epsilon|=\varphi^{-m}<1/F_m$
   (because $F_m<\varphi^m$). **Fixed.**
3. **Theorem 7, domain and range.** A chord run is defined only from $X_0=s_0E+hN$ with
   $s_0\in[-1,1)$, because $i(s)$ and $T$ are defined only there. So "every $X_0$ in the plane"
   was wrong as stated. The closing claim "no chord run is infinite at any $r<r_c$" also needed
   $\delta>2/5$. The test centres $P_m$ do not depend on $r$, so $L(X_0;r)$ is non-decreasing in
   $r$, and the bound at $\delta=2/5$ ($m=7$, $L\le12$) covers larger $\delta$. **Fixed**, with a
   sentence saying what the theorem does *not* cover: tokens applied where $T$ does not assign
   them. The domains overlap a lot: along the line at $r_c$, $w_1$ acts for $s$ in about
   $[-2.24,-0.62]$, $w_2$ in $[-0.62,1.0]$ and $w_3$ in $[-0.24,1.0]$. Such tokens do occur in
   shortest words. I found one per word at $1/10$ (at a point with $s<-1$), at level 2 and at
   $1/320$; the note counts 6 in 1 798.
   On the questions in the brief: the bound covers every offset $h$, including offsets where the
   words act on only part of the line. Lemma 5 gives $J_h\subseteq\mathcal B_h$ for every $h$, and
   a larger bad set only shortens runs. The convex domains are right: each is an intersection of
   closed disks about the test centres. I recomputed the centres exactly, and they agree with
   Table 2.1 of `sharp-bound-n5-critical-orbits.md`.
4. **Corollary 11 claimed all of Conjecture A.** B$^\ast$ is a statement for
   $0<\delta\le\delta_0$, so it bounds $M(r)$ only there. For (B) that is enough. At those radii
   $M(r)<\infty$, and `critical-radius-n5.md` Lemma 4.1(2)–(3) gives finiteness. That lemma is
   the "if" direction of the conjugate criterion, proved at every radius, norm radius or not.
   Group monotonicity (`boundary-contact.md` Theorem 3.4, Lean `finite_GG_of_le`) then gives every
   smaller $r$. Conjecture A on all of $r<r_c$ would also need $\sup_{\delta>\delta_0}\delta M(r)<\infty$.
   That does not follow: the "only if" direction is proved only at non-norm radii and gives no
   uniformity, and $M(r)$ is not known to be monotone in $r$. **Fixed** (statement, proof, opening
   item 5, the gap paragraph).
5. **Conjecture B$^\ast$ as written was equivalent to Conjecture A.** The original statement
   allowed each $D_i$ to be the internal translation of *any* chord run at radius $r$. Line 1,
   Theorem 6(2) (refereed) gives, for $\delta\le1/20$, a chord run from $0$ with internal
   translation above $0.50202/\delta-11.862$. So if $M(r)\le C/\delta$, the inequality holds
   with $N_0=\lceil C/0.50202\rceil$ copies of that run and $c_0=11.862N_0$. Conversely
   B$^\ast$ implies Conjecture A for small $\delta$ by Corollary 11. So B$^\ast$ was not a
   reduction. The note's own description ("bound the number of chord runs that one word can
   chain") and its evidence (runs of shortest words) are structural. **Fixed**: B$^\ast$ now says
   that every word map at $z$ is the map at $z$ of a word made of at most $N_0$ chord-run segments
   and connector letters of total effect at most $c_0$. A remark records why the unstructured form
   is empty. Corollary 11 holds for the new form by the triangle inequality, since a segment of a
   chord run is a cut-short chord run. The authors may prefer another structural formulation;
   any one in which the runs come from the word will do.
6. **"One run is not enough" overstated.** Line 1's Conjecture B has a constant $C'$. A ratio
   of $1.45$ between $M(r)$ and the best single run rules out only $C'=1$. My data show the ratio
   is stable under renormalization (1.452 at $1/55$ and at $\varphi^{-3}/55$; 1.129, 1.107, 1.108
   at $1/30,\varphi^{-3}/30,\varphi^{-6}/30$), so they *support* a single-run form with
   $C'\approx1.5$. **Fixed** in item 4 and §5. Two further cautions:
   - $\Sigma_1=8.507\sup L$ is an approximation. The exact extent of a run of $k$ steps is
     $(2k\varphi+2n_k)|\sigma E|$, and $2\sqrt5|\sigma E|=8.5065$, so the table's last digits
     (e.g. $842.2$ against $842.1$) are rounding.
   - $\sup L$ is a sampled supremum over offsets in double precision. It is a lower estimate of
     the true supremum, so the ratios $1.12$, $1.45$ are not rigorous: a narrow window of
     offsets with longer runs could have been missed. The rigorous single-run bound (Theorem 7)
     is $3\,221$ at $1/55$, far above $1\,223$. My finer scan (8 001 offsets in $[-0.1,0.1]$ at
     $1/55$) also gives $99$.
7. **Two descriptive sentences in Computation 10.**
   - "6 or 7 runs alternating between the lines $\mathbb RE$ and $\mathbb R\bar E$". At $1/55$ my
     shortest word is exactly the note's (runs $66,10,21,11,10,54$, 963 of 975 letters,
     alternating lines). At $1/30$ my two extreme words have 5 and 7 runs, and at $1/80$ most
     consecutive runs lie on $\mathbb R\bar E$ in opposite directions (classes $\iota$ and $\iota\nu$).
   - "The run on the new line starts at offset $|h|\le2\delta$". At $1/55$ a 10-token run starts
     at $|h|=0.0373=2.05\delta$; at $\varphi^{-3}/55$ a 44-token run starts at $2.08\delta$; and
     single tokens act at $|h|\approx0.95$.
   - "So the runs are chord runs": runs containing one of the 6 non-$T$ tokens are not.

   **Fixed** (wording).
8. **Cosmetic, not changed.** The letter $\kappa$ means $2(1-\zeta)$ here (§3.2), $3.789$ in line 1,
   and $1.106$ in `sharp-bound-n5-critical-orbits.md`. The letter $F$ is both the vector
   $\varphi^{-1}E$ and a Fibonacci number in §3.7. The exponent $m$ is used both for test indices
   and for Fibonacci indices.

## 3. Checks of the proofs

- **Proposition 1.** Item 1: $a(y)+1=\zeta^{-1}(y+1)$ on $D_1$, and $\sigma$ is a ring
  homomorphism commuting with conjugation. Item 2: $\alpha-\beta=4\operatorname{Re}y$,
  $\alpha+\beta=2|y|^2+2$. Item 3 is the triangle inequality. Correct.
- **Proposition 2.** I checked $\tau=B\circ A^{-1}=z+2(1-\zeta^{-1})$. The normal closure is
  generated by the $A$-conjugates, because $\tau$ commutes with translations. The quotient is
  generated by the image of $A$, of order 5. $|\Lambda/K|=16\cdot5$, the fixed classes are
  $2\Lambda/K\cong\Lambda/(1-\zeta)$, and the density argument is right. I also checked the
  counts of Computation 2.1 from the ideals: $K+m\Lambda$ is $2\Lambda$, $\Lambda$, $2\Lambda$,
  $(1-\zeta)\Lambda$, $2\Lambda$, $\Lambda$, $2\Lambda$ for $m=2,\dots,8$, giving
  $5,81,80,125,405,2401,1280$. An exact closure of residues reproduces them, and so does the
  level-1 orbit of $0$ (30 165 points from the engine). The level-0 orbit fills them for
  $m\le5$ only ($397$, $1\,005$, $874$ classes for $m=6,7,8$), as stated.
- **Proposition 3.** Item 1: $\iota A\iota=A^{-1}$, $\nu A\nu=B$, and the disks map correctly.
  Item 3 needs both line-1 Theorem 6(1) (membership for $r$ close to $r_c$) and Theorem 4(1)
  (unbounded conjugates). The citation now names both.
- **Lemma 4.** The composites were recomputed exactly: $(2,-2,2,-2)=2F$ for $w_1$ and $w_2$, and
  $(2,-4,4,-2)=-2\varphi^{-2}E$ for $w_3$. The map $T$ needs no reduction modulo 2 on any $I_i$,
  so $s_k-s_0=\sum v$. The conjugate sum $-(2k\varphi+2n_k)\sigma E$ is correct.
- **Lemma 5.** Checked exactly in $\mathbb Z[\zeta]$: the test centres of all three words; $b^\ast E=-F$;
  $P+P'=-2F$; $u=(0,1,1,-1)$; $|u|^2=3+\varphi$; $\bar uE+u\bar E=-1+2\varphi=\sqrt5$;
  $-\bar F=(-2,-1,0,-2)$; $|{-\bar F}+1|^2=5-3\varphi$; $A(-\bar F)=-F$. The three cases
  $|c|\le\delta$, $c>\delta$ and $c\le-\delta$ are right, and the ends stay in $I_1\cup I_2$ for
  $\delta\le2/5$. One point is worth noting for later use. On $\{s:|\ell|<\delta\}$, which is an
  interval of length $2\delta/\sqrt5$ centred at $b^\ast-c/\sqrt5$, *both* $w_1$ and $w_2$ fail,
  whatever word $T$ assigns. This is the starting point of suggestion S1 below.
- **Lemma 6.** I checked Binet's identity $F_m\varphi^{-1}-F_{m-1}=(-1)^{m-1}\varphi^{-m}$. The
  index bijection uses $\gcd(F_{m-1},F_m)=1$. The positivity step is added.
- **Theorem 7.** I checked that $m\ge3$ (so the minimality inequality at $m-1$ is available), the
  Binet estimates, and $F_m=\varphi F_{m-1}+\psi^{m-1}$. The prefix estimate: each acting letter
  changes $|\sigma t|$ by at most $|\zeta^{\mp2}-1|=1.9021$, and at most 5 letters act before the
  failing test. The symmetry step: conjugating the piecewise maps by $\iota$ or $\nu$ preserves
  the pattern of acting letters, and $|\sigma\bar t|=|\sigma t|$. All correct. Numerically the
  bound holds with room at every radius computed: $\sup L$ against $F_m-1$ is $22/33$,
  $33/54$, $44/88$, $77/143$, $99/143$ (level 1 and $1/40$), $99/232$ ($1/50$, $1/55$),
  $188/376$, $420/609$, $798/1596$ ($1/320$), $1785/2583$ (level 3).
- **Corollary 11.** See issue 4.

## 4. Independent computation

**Method.** All code is my own and is described here so it can be redone. It is throwaway
scratch code, not part of the repository.
- A C program does the lifted breadth-first search over states $(y,j)$. Points are integer
  4-vectors. The disk tests are exact sign tests of $\rho-|y\pm1|^2$ in $\mathbb Z[\varphi]$, in
  128-bit integers. For $V=\{\zeta^{-2j}\sigma y\}$ it takes the convex hull in double precision
  and evaluates all hull-vertex pairs. The pairs within $10^{-9}$ of the largest are then
  compared exactly in $\mathbb Z[\varphi]$. A second breadth-first search from the first extreme
  state gives a shortest word.
- A Python program replays the word letter by letter with exact disk tests and checks that it
  reaches the second state. It tokenizes greedily (6-letter, then 5-letter tokens among the
  twelve), computes each piece's contribution to $\sigma t$ exactly, and splits runs at
  connectors and at class changes. It checks $T$-assignment exactly, by comparing $s$ with the
  breakpoints in $\mathbb Q(\varphi)$.
- $\sup L$ is computed by iterating the survivor set $S_{n+1}=\mathcal B_h^c\cap T^{-1}S_n$ as
  a union of intervals. This is a different algorithm from the note's doubling and bisection.
  Good sets come from the exact centres, in double precision.
- Seeds were drawn as in §6 of the note (uniform physical point in $D_1\cup D_2$, uniform internal
  point of modulus at most $25/\delta$, rounded in the basis), plus the 5 429 small lattice seeds.
- The engine `tdcsg-orbit` (copied binary, `orbit` subcommand only) confirms: 111 107 points and
  conj $1299.43$ for the $1/55$ witness; 793 605 and $6927.03$ for the level-2 witness; 793 108 for
  $-\varphi$ at level 2; 30 165 at level 1; 5 279 for the $1/10$ witness. My own search gives the
  same sizes.

**Table R.** Extreme words. Exact: $M\ge$ (diameter of $V$, the pair compared exactly), letters,
runs, $T$-checks. Double precision: $\sup L$ and $\Sigma_1=2\sqrt5|\sigma E|\sup L$. Rows marked
"new" are radii not in the note.

| $\delta$ | witness seed | $M(r)\ge$ | $\delta M$ | token letters | runs (tokens per run) | connectors $\sum|\cdot|$ | $\sup L$ | $M/\Sigma_1$ |
|---|---|---|---|---|---|---|---|---|
| $1/10$ | $(93,-61,97,-3)$ | 196.74 | 19.67 | 129/131 | 2 (1\*, 22) | 3.80 | 22 | 1.05 |
| $1/30$ | $(437,-36,293,235)$ | 739.75 | 24.66 | 533/546 | 5 (10,34,10,21,20) | 24.73 | 77 | 1.13 |
| $1/30$ | $(406,-109,317,143)$ | 739.75 | | 542/553 | 7 (10,34,10,26,2,4,10) | 20.92 | | |
| $1/55$ | $(470,202,166,493)$ | 1223.05 | 22.24 | 963/975 | 6 (66,10,21,11,10,54) | 22.83 | 99 | 1.45 |
| $1/80$ | $(-483,46,-326,-252)$ | 1624.71 | 20.31 | 1411/1424 | 7 (1,9,11,54,44,44,88) | 24.73 | 188 | 1.02 |
| level 2 | $(1818,-1259,1899,-135)$ | 3582.41 | 19.96 | 2365/2367 | 2 (420, 1\*) | 3.80 | 420 | 1.00 |
| $1/320$ (new) | $(819,-861,1039,-357)$ | 6789.37 | 21.22 | 4483/4485 | 2 (797, 1\*) | 3.80 | 798 | 1.00 |
| level 3 (new) | $(2315,2587,-168,4015)$ | 15187.64 | 19.98 | 10028/10032 | 1 (1785) | 7.61 | 1785 | 1.00 |
| $\varphi^{-3}/30$ (new) | $(972,705,164,1305)$ | 3127.08 | 24.61 | 2299/2308 | 7 (1,87,89,44,144,43,1\*) | 17.12 | 332 | 1.11 |
| $\varphi^{-6}/30$ (new) | $(947,-233,731,353)$ | 13258.57 | 24.63 | 9770/9782 | 5 (377,377,188,610,187) | 22.83 | 1407 | 1.11 |
| $\varphi^{-3}/55$ (new) | $(3873,830,1882,3226)$ | 5185.89 | 22.26 | 4099/4111 | 7 (232,44,44,88,44,276,1) | 22.83 | 420 | 1.45 |

(\* a token not assigned by $T$. Connectors: sum of the moduli of their contributions to
$\sigma t$.) In every word the pieces' contributions add up exactly to $\sigma t$.

**What this confirms.**
- The $M(r)$ values and witnesses of Computation 9 at $1/10$, $1/30$, $1/55$, $1/80$ and level 2.
  At $1/30$ the witness seed is not given in the note; my random search found it among 10 340
  orbits.
- The $\sup L$ columns of Computation 8 at all ten radii: $12/22$, $33/33$, $43/44$, $44/77$,
  $99/99$, $55/99$, $99/99$, $99/99$, $188/188$, $420/420$. My offset ranges were wider than the
  note's $[-4\delta,4\delta]$ ($[-0.4,0.4]$ at $1/10$, $1/30$, $1/55$), so the note's narrower
  scan lost nothing.
- Computation 10's main claims at these radii. Token fraction $\ge97.6\%$ on extreme words;
  at most 7 runs; connectors at most $24.73$ (exactly the note's maximum, attained at $1/30$ and
  $1/80$); chord steps times $\delta$ between $2.3$ and $3.2$.
- The 6–7-run chains that beat the best single run, at $1/30$ and $1/55$.

I did not reproduce the strip-graph column $\Sigma_1^{\rm g}$, the cut-set column (cited), the
count of 146 multi-index orbits, or the 75 random orbits of Computation 10.

**Exact versus double precision in the note.** Exact: orbit membership, orbit sizes, the extreme
pairs (confirmed here by an exact comparison), the words and tokenization, and Computation 2.1.
Double precision, correctly labelled: Computation 8 (all of $\sup L$, $\Sigma_1$,
$\Sigma_1^{\rm g}$) and therefore the ratios $1.12$ and $1.45$ and the "within $1\%$" claim; the
offsets $h$ of runs; the "about $2.5/\delta$" statement. The $T$-check method is not stated; mine
is exact and agrees on the radii I ran. Nothing presented as proved rests on double precision.

## 5. Consistency with `sharp-bound-n5-critical-orbits.md`

That note's Theorem 2 gives, on the chord ($h=0$), exact holes of width
$h(\delta)=\dfrac{2\delta/\sqrt5}{1+\sqrt{1-\kappa\delta}}$, $\kappa=1.10557$, on *each* side of
$b_1=-\varphi^{-1}$. Here Lemma 5 gives a bad interval of *total* length $2\delta/\sqrt5$. The two
are consistent:
- At $h=0$ (so $c=0$) the interval is $J_0=(b^\ast-\delta/\sqrt5,\ b^\ast+\delta/\sqrt5)$.
- The exact hole is $(b^\ast-h(\delta),\ b^\ast+h(\delta))$, and $h(\delta)\ge\delta/\sqrt5$
  because the denominator is at most 2. So $J_0$ lies inside the exact hole.
- The two agree to first order: $h(\delta)=\delta/\sqrt5+O(\delta^2)$.
- Numerically at $\delta=0.02$, $h=0$: $h(\delta)=0.008994$ against $\delta/\sqrt5=0.008944$, and
  my good-set computation gives $0.0090$ on both sides.
- Lemma 5 uses the binding letters named there (the 4th of $w_1$ and the 2nd of $w_2$, with
  $|f'|$ in the chord parameter equal to $\sqrt5$). Its test centres equal Table 2.1.
- Proposition 2.3 there (the tube) is Lemma 4 here.

The two notes do not contradict each other. Lemma 5 is the uniform-in-$h$ linearization of
Theorem 2's tight tests at $b_1$.

## 6. Conjecture B$^\ast$, the gap, and what to do next

**Does the number of runs grow with the level?** In everything I could compute, no.
- At the level radii (1, 2, 3) and at $1/320$, the extreme words are single runs (plus at most
  one stray token).
- The chained words occur at intermediate radii, and they are self-similar. Under
  $\delta\mapsto\varphi^{-3}\delta$ the $1/55$ chain becomes a 7-run chain. The total number of
  tokens is multiplied by $4.24\approx\varphi^3$ ($172\to729$), and both $M/\Sigma_1=1.452$ and
  $\delta M=22.2$ are unchanged.
- The $1/30$ family keeps 5–7 runs, $M/\Sigma_1\approx1.11$ and $\delta M\approx24.6$ over two
  steps ($1/30$, $\varphi^{-3}/30$, $\varphi^{-6}/30$).
- At $\varphi^{-6}/55$, 1 034 random orbits found only $M\ge15187.6$, with $\delta M=15.4$. The
  chain was not found (the note needed 115 000 seeds at $1/55$), so that test is inconclusive.

Caveats: these are lower bounds from random seeds, extreme words only, and at most two
renormalization steps. Still, the pattern is what a renormalizable mechanism with bounded chaining
predicts, and nothing in it suggests growth. I consider the structural B$^\ast$ plausible.

**How strong is B$^\ast$?** In its structural form it is strictly stronger than Conjecture A.
It would also explain Conjecture A, which is its value. The data suggest an even simpler
intermediate target:

> **(B$_1$)** $M(r)\le C'\,\Sigma_1(r)+c$ with $\Sigma_1(r)$ the largest internal translation of
> a single chord run at radius $r$, for one constant $C'$ (the data give $C'\approx1.46$).

With Theorem 7, (B$_1$) implies Conjecture A for small $\delta$, and hence (B). Like the
unstructured B$^\ast$ it is "Conjecture A with a named constant", so it is a target, not a
reduction.

**Suggestions.**
- **S1. Free-choice cut-off (provable next step).** Strengthen Theorem 7 to cover any forward walk
  of tokens of one class, with the token at each step any of $w_1,w_2,w_3$ whose tests pass. This
  removes the $T$-assignment hypothesis and with it the "non-$T$ tokens" in the evidence. The
  ingredients:
  - every forward token step is the rotation by $2\varphi^{-1}$ modulo $2$ (since
    $-2\varphi^{-2}=2\varphi^{-1}-2$), so positions modulo $2$ follow the same golden rotation
    whatever the choices;
  - on $W_h=\{s:|\sqrt5(s-b^\ast)+gh|<\delta\}$ both $w_1$ and $w_2$ fail whatever is assigned
    (§3, Lemma 5);
  - what remains is to show that $w_3$ does not act on $W_h$, and that no token acts on the lifts
    $W_h\pm2$.

  Numerically, at $r_c$ the domains of all tokens lie in $s\in[-2.256,1.019]$ for every $h$, and
  $w_3$ starts at $s\ge-0.251$. The lifts of an interval of half-length $\le0.18$ about $b^\ast$
  lie outside, with little margin at $\delta=2/5$ and ample margin for $\delta\le1/4$. For large
  $|c|$ the window $W_h$ moves, and that case needs the same care as the case split of Lemma 5. A
  rigorous version needs exact bounds on the extents of the three domains, a finite computation.
- **S2. The window return map in scaled coordinates.** This is the most promising route to
  B$^\ast$. Runs start and end in the $O(\delta)$-windows of the breakpoints
  $\pm F,\pm\bar F,\pm\varphi^{-3}E,\dots$. Write a window point as
  $(u,\eta)=((s-b)/\delta,\ h/\delta)$.
  - The end point of a run started in a window is the first entry of a golden-rotation orbit
    into the moving interval $W_h$. By the three-gap theorem, its return times take at most
    three Fibonacci-type values, and the entry position depends piecewise-affinely on $(u,\eta)$.
  - The connectors between windows are finitely many explicit letters (such as $a(-\bar F)=-F$),
    acting as isometries that are affine in the scaled coordinates.
  - So the chaining is a first-return map $R_\delta$ on a finite union of scaled windows.
  - Conjecture: $R_{\varphi^{-3}\delta}=R_\delta$ up to $O(\delta)$ corrections, exactly along
    each sequence $\delta_0\varphi^{-3k}$. Table R is evidence: run patterns and $\delta M$ are
    unchanged along $1/30\cdot\varphi^{-3k}$ and $1/55\cdot\varphi^{-3k}$.
  - First provable statement: the finite list of window-to-window connector germs and their
    action on $(u,\eta)$, with the error terms bounded uniformly for $\delta\le\delta_0$.
  - Second statement: every orbit of the limiting scaled map $R_*$ leaves the window system after
    at most $N_0$ returns. This is a finite, $\delta$-independent problem that a computer can
    check.

  This is the tight-window renormalization of `sharp-lower-bound-limit-system.md` in a reduced
  form: two real coordinates per window instead of a planar cut set.
- **S3. Runs per offset scale.** A weaker statement that may be within reach: a word whose runs
  all start at offsets $|h|\le\lambda\delta$ has at most $N(\lambda)$ runs of length above
  $\epsilon/\delta$. The long runs in Table R all start at $|h|\le2.1\delta$, and the short ones
  contribute $O(1)$ each.
- **S4. Data to collect** (cheap with the code described in §4): the full table along
  $1/55\cdot\varphi^{-3k}$ for $k=2$, with a targeted seed search near the $k=1$ witness scaled by
  the unit $\varphi^3$ in internal space; and the run counts of *all* orbits with diameter
  $\ge0.9\max$, not only the extreme one, at two consecutive levels.

## 7. What I did not check

The cited results of other notes (Theorem A, `critical-radius-n5.md` Lemma 4.1, line 1 Theorems 4
and 6, group monotonicity) were taken as refereed. Also not reproduced: the strip-graph extents
$\Sigma_1^{\rm g}$, the cut-set column of the table of Computation 8, and the full sets of 107 words
and 65 382 orbit records. I ran no `certify*` subcommand and no Lean build.
