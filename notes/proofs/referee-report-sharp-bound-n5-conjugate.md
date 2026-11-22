# Referee report: `sharp-bound-n5-conjugate.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$ through the Galois-conjugate
coordinate: the escape mechanism and its $1/\delta$ scale" (`sharp-bound-n5-conjugate.md`, commit
`0d64514`). Companions consulted: `critical-radius-n5.md` §§1–4 (Theorem A, Lemma 3.1 and its
trajectory table, Lemma 4.1), `sharp-lower-bound-n5.md` §§3–4 (Lemma 3.0, Theorems 3.1, 4.1),
`sharp-lower-bound-combined.md` §4 (Corollary 4.3, Proposition 4.4),
`sharp-lower-bound-limit-system.md` Corollary 4.4, and `../engine.md`.

## Summary

The mathematics of the note is sound. Every proof was checked line by line and every constant
was re-derived to at least 20 digits. The proofs are complete. The defects are of four kinds:

- several numerical constants in lower bounds were rounded **up** (and one upper bound rounded
  **down**), so the stated inequality is not implied by the proof for small $\delta$;
- the "only if" half of Lemma 1 was cited to a lemma that proves only the "if" half;
- two hypotheses were missing (Corollary 7 needs "containing $(0,0)$"; Theorem 6(4) at level 0
  lies outside the stated range $\delta\le1/20$);
- the "checked exactly" claim for the chord time $K$ in §4 proves only $K(\delta)\le K$.

All are fixed in the note, with a status line at its top. No mathematical claim needed more than
that. I re-ran the engine on all ten radii of Table 4.1 and at $r_c$, and wrote an
exact-arithmetic simulation of the chord words. All computed values I checked agree, and the
chord times are now exact at every radius of the table and at levels 4, 5 and 6.

On the assessment of §5.3: the equivalence "bounded invariant region $\Leftrightarrow$ finite
group" is correct (at non-norm radii, which suffice), but it is a tautology that would make
*any* route to (B) look like a reformulation. What the note actually shows is a set of
constraints on the region, not an obstruction. Section 5 below lists what I think is still worth
doing along this line, with three concrete, provable-looking extensions of Theorem 6.

## 1. Verdicts

| result | verdict |
|---|---|
| Lemma 1 (conjugate criterion) | **correct at non-norm radii after a citation fix** (issue 2). The "if" half is `critical-radius-n5.md` Lemma 4.1; the "only if" half is `sharp-lower-bound-n5.md` Theorem 4.1 and holds only at non-norm radii as proved. §3.0 (the bounded invariant set $W_r$) is correct |
| Proposition 2 | **correct** |
| Proposition 3 | **correct** |
| Theorem 4, items 1–3 | **correct**; one digit of the rate fixed ($1.51414$, not $1.51416$) |
| Proposition 5 | **correct**; last clause restated without the expression $1/((m+1)^2-4+\varphi)$, which is meaningless when $(m+1)^2\le4-\varphi$ |
| Theorem 6(1) lower bound on $K$ | **correct after a constant fix**: $0.05901/\delta-1.171$ (was $0.05902$) |
| Theorem 6(2) conjugate reach, orbit size | **correct after constant fixes**: $0.50202/\delta-11.862$ (was $0.50203$), $|O_r(0)|>0.05901/\delta-0.171$ |
| Theorem 6(3) exact point, exit, $K\le k_j$, chord part $<18.02/\delta+1.91$ | **correct**; $<2.1181/\delta$ (was "$=2.1180/\delta$", which is below $\varphi^3/2=2.118034$) |
| Theorem 6(4) levels | **correct after a range fix**: the exit argument does not use $\delta\le1/20$, so $k=0$ ($\delta_0=1/10$) is covered; the note now says so |
| Corollary 7 | **correct after a missing hypothesis**: "no bounded set *containing $(0,0)$* is invariant at every $r<r_c$" ($\{(5,0)\}$ is bounded and invariant at every $r$) |
| Corollary 8 | **correct, conditional, and honestly stated** (issue 5) |
| Conjectures A, B | statements consistent with the data; evidence reproduced |
| §4 Table 4.1, Observations 1–5 | **reproduced** where re-run (§3); one generation index off by one ($892$, not $893$) |
| §5.3 assessment "dead in its direct form" | the equivalence is correct but carries less weight than claimed (§4) |

## 2. Issues

1. **Constants rounded the wrong way.** A lower bound $c/\delta-d$ with $c$ rounded up is not
   implied by the proof once $1/\delta$ is large enough. Exact values:
   $1/(2\sqrt5\kappa)=1/(4\varphi^3)=0.0590169944\ldots$ (stated $0.05902$ and $0.059017$,
   both above it; the stated bound fails to follow for $1/\delta>60$);
   $|\sigma E|/\kappa=0.5020285397\ldots$ (stated $0.50203$; fails to follow for
   $\delta<0.005$, which includes levels 2 and 3);
   $|\sigma E|(2+\varphi^3)=11.86170617\ldots$ (stated $11.8616$ in the proof, $11.862$ in
   the statement, which is fine);
   $\varphi^3/2=2.1180339887\ldots$ (stated "$=2.1180/\delta$" as an upper bound);
   $1/(2r_c)=0.2326705636\ldots$ (stated $0.2327$ in a lower bound).
   The rate $2\sqrt5|\sigma E|/(4+\varphi)=1.5141432\ldots$ was given as $1.51416$.
   All other constants check: $\kappa=3.788854$, $(1+\varphi^3)/(2\sqrt5)=1.170820$,
   $|\sigma E|\sqrt5\varphi^3=18.017073$, $|\sigma E|=1.902113$, $\sqrt5\varphi^{-4}=0.326238$,
   $\sqrt5\varphi^{-7}=0.077014$, $20/\kappa=5.27864>1+\varphi^3=5.23607$,
   $\varphi^7/(20\sqrt5)=0.649230$. **Fixed.** The rounded forms in the opening summary
   ($0.0590/\delta-1.18$, $2.12/\delta$, $0.502/\delta-11.87$) were already safe.
2. **Lemma 1, "only if".** `critical-radius-n5.md` Lemma 4.1 proves $M(r)<\infty\Rightarrow$
   finite, not the converse. The converse is `sharp-lower-bound-n5.md` Theorem 4.1, at non-norm
   radii, where Lemma 3.0 shows every word map is realised on an open set. At a norm radius a
   word can have a germ at an isolated degenerate point that no open set carries, and I found no
   argument in the repository bounding those. By group monotonicity (B) needs only non-norm
   radii, and no result of the note uses the converse at a norm radius. **Fixed** (citation and
   the scope of the §5.3 sentence).
3. **The exact check of $K$ in §4 is one-sided.** The lookup "$t_kE\in O_r(0)$ for $k\le K$ and
   $t_{K+1}E\notin O_r(0)$" proves $K(\delta)\le K$: if no word failed up to $K$, then
   $t_{K+1}E$ would be in the orbit. It does not prove $K(\delta)\ge K$, because $t_kE$ may be
   reached by another route after a chord word has failed. My exact simulation (§3) closes this:
   the values of $K$ are exact. **Wording fixed.**
4. **Missing hypotheses.** Corollary 7, second sentence, and the abstract's "every invariant
   region" need "containing $(0,0)$". Theorem 6(4) at $k=0$ is outside $\delta\le1/20$; the exit
   half of item 3 needs no condition on $\delta$, and the size half needs only
   $\delta<\sqrt5\varphi^{-4}$. **Fixed** (statement remark in item 3, range in item 4).
5. **Corollary 8 is honest.** It is labelled "proved modulo the certified four-window relative
   certificate", and $T_W$ is declared finite and not computed. The proof is right: a sub-chain
   of a shortest chain is shortest between its endpoints, so its length is at most $\beta_W+1$
   and its germ lies in the finite set $G_W$ of `sharp-lower-bound-combined.md` Proposition 4.4;
   the conclusion "no uniform bound on window visits" does not depend on the value of $T_W$. The
   proof chose $y^\ast$ "attaining $M_0(r)$", which presupposes a finite orbit; it now uses
   $y^\ast=t_{K_0+1}E$ directly. **Fixed.** Note that the corollary is weak against the data:
   window visits grow like the orbit ($84$ to $19\,408$), not like $1/\delta$.
6. **Smaller wording points, fixed.** Proposition 5 controls lattice points only (the abstract
   now says "on lattice points"). Where §5.1 and §5.3 said the systems agree up to conjugate
   modulus $\delta^{-1/2}$, the proved threshold is $\sqrt{4-\varphi+1/\delta}-1$, which is
   below $\delta^{-1/2}$ for small $\delta$; the text now says $\delta^{-1/2}-1$. §5.2 said
   $18.1/\delta$ for the chord bound, which is false for $0.042<\delta\le1/20$; it now gives
   $18.02/\delta+1.91$. "Compact invariant region" in §5.3 became "bounded invariant region
   containing $(D_1\cup D_2)\times\{0\}$": closure of $W_r$ is not shown invariant (the gate is
   discontinuous), as `critical-radius-n5.md` §4.1 already warns. The chord share $85\%$ is
   $84.5\%$. The level-2 maximum is at generation $892$.

## 3. Proof checks in detail

- **(1.1), Theorem 4.** $T$ adds $2\varphi^{-1}$ or $2\varphi^{-1}-2$, so
  $t_k=2k\varphi^{-1}-2m_k$, and $\sigma(t_k)-t_k=-2\sqrt5k$ follows from
  $\sigma(\varphi)=1-\varphi$. Conjugates $\sigma(\varphi^{-1})=-\varphi$,
  $\sigma(\varphi^{-2})=\varphi^2$; the pieces $[-1,-\varphi^{-3})$, $[-\varphi^{-3},1)$ have
  lengths $2\varphi^{-2}$, $2\varphi^{-1}$; mean $-2\sqrt5$. Item 3 needs only Weyl
  equidistribution of $k\varphi^{-1}$ modulo 1.
- **Proposition 5.** $\alpha=|y-p|^2\in\mathbb Z[\varphi]$, $0\le\beta<\delta$, $|N\beta|\ge1$
  and $\sigma\beta\le4-\varphi<1/\delta$ force $\sigma\beta<-1/\delta$. The orbit statement: with
  $O_r(x)\subseteq O_{r_c}(x)$ and identical generator action on $O_{r_c}(x)$, each orbit is
  closed under the other system's generators.
- **Theorem 6, Steps 1–2.** $f_m$ minus its chord interpolation is $-(3-\varphi)(s-b)(b'-s)$;
  $d(|I|-d)\ge d|I|/2\ge d\varphi^{-2}/2$; $2\varphi^2/(3-\varphi)=2\varphi^3/\sqrt5=\kappa$
  because $3-\varphi=\sqrt5/\varphi$. Induction over the letters is valid because the prefix at
  radius $r$ is the prefix at $r_c$ while all tests pass.
- **Step 3.** $t_k-b\ne0$ by parity (for $b=1-\varphi$ both parts are odd, not only the
  $\varphi$-part as stated; harmless). $\sigma(B)=\{\pm1,\varphi,\varphi^3\}$, so (3.2) holds.
- **Item 3.** Binet gives $F_j\varphi^{-1}-F_{j-1}=(-1)^{j-1}\varphi^{-j}$; parity of $F_j$,
  $F_{j-1}$ for $j\equiv1\pmod3$; both sides in an interval of length 2. The tight letters: in
  $w_1$ the fourth letter $a^{-1}$ at $-(\zeta-\zeta^{-1})=(-1,-2,-1,-1)$ (the table of
  `critical-radius-n5.md` §3.2), with $u\bar v=2\zeta-\zeta^2-\zeta^{-1}$ and derivative
  $\sqrt5$; in $w_2$ the second letter $b$ at $E'=-E$, derivative $-\sqrt5$. Both give
  $f(b^\ast\pm d)=r_c^2-\sqrt5d+(3-\varphi)d^2$. Which side occurs alternates with the parity of
  $j$ ($w_2$ for odd $j$, $w_1$ for even $j$); my simulation confirms the failing letter is
  exactly this one at every level (second letter of $w_2$ at levels 0, 2, 4, 6; fourth letter of
  $w_1$ at levels 1, 3, 5). Size of $k_j$: minimality of $j$ and $j\ge7$.
- **Corollaries.** Corollary 7 is immediate from Theorem 6(2). Corollary 8: see issue 5.

## 4. Reproduction

Engine: the repository's `tdcsg-orbit` (built 2026-11-22 from commit `d377623`, with
`--conj-points`), copied to a scratch folder. Every run used `--format lines --conj-points`;
a stream filter of my own computed the size, $M_0$ from the exact conjugate coefficients
(cross-checked against the engine's printed modulus), the exact membership of the chord points
$t_0E,\dots,t_{K+1}E$ (coefficient comparison), the per-generation maxima, and, where marked,
the number of points in the four tight windows $W^{\rm t}$ with **exact** disk tests.

| radius | $|O_r(0)|$ | $M_0$ | $t_0E..t_KE$ in orbit, $t_{K+1}E$ not | $|O\cap W^{\rm t}|$ |
|---|---|---|---|---|
| $1/10$ | 1 433 | 53.746 | yes ($K=6$) | 84 |
| $1/20$ | 9 513 | 143.069 | yes ($K=16$) | — |
| $\varepsilon/10$ | 30 165 | 273.210 | yes ($K=27$) | 1 496 |
| $1/40$ | 30 153 | 273.210 | yes ($K=27$) | — |
| $1/80$ | 112 567 | 612.112 | yes ($K=72$) | 5 512 |
| $\varepsilon^2/10$ | 400 519 | 1 164.996 | yes ($K=116$) | 19 408 |
| $1/160$ | 400 467 | 1 164.996 | yes ($K=116$) | — |
| $1/320$ | 1 504 173 | 2 592.946 | yes ($K=304$) | — |
| $\varepsilon^3/10$ | 5 673 561 | 4 933.192 | yes ($K=493$) | — |
| $1/640$ | 5 253 049 | 4 933.192 | yes ($K=493$) | — |

All agree with Table 4.1 and Observation 5. The level-2 maximum is at $844+2\zeta+522\zeta^2+522\zeta^3$, next to the lens corner $(1,2,1,1)$, with $\lambda=(843,0,521,521)$, $|\lambda|\,|\sigma\lambda|=5.00$, as in Observation 3.

**Exact chord simulation.** A separate program applies $w_1,w_2,w_3$ letter by letter to
$t_kE\in\mathbb Z[\zeta]$, with $|z\mp1|^2$ computed as $A+B\varphi$ and its comparison with
$r^2$ decided exactly by integer arithmetic; the word assigned by $T$ is also chosen exactly; at
$r_c$ every word acts for the first 3 000 steps and lands exactly on $t_{k+1}E$. Results:

| radius | $K$ (exact) | exit word, failing letter | $[K_0+1,k_j]$ | chord reach |
|---|---|---|---|---|
| $1/10$ | 6 | $w_2$, 2nd | $[-,6]$ | 52.15 |
| $1/20$ | 16 | $w_3$, 5th | $[1,27]$ | 136.53 |
| $\varepsilon/10$ | 27 | $w_1$, 4th | $[2,27]$ | 230.87 |
| $1/40$ | 27 | $w_1$, 4th | $[2,27]$ | 230.87 |
| $1/80$ | 72 | $w_3$, 2nd | $[4,116]$ | 610.57 |
| $\varepsilon^2/10$ | 116 | $w_2$, 2nd | $[10,116]$ | 987.93 |
| $1/160$ | 116 | $w_2$, 2nd | $[9,116]$ | 987.93 |
| $1/320$ | 304 | $w_3$, 5th | $[18,493]$ | 2 586.43 |
| $\varepsilon^3/10$ | 493 | $w_1$, 4th | $[44,493]$ | 4 194.88 |
| $1/640$ | 493 | $w_1$, 4th | $[37,493]$ | 4 194.88 |
| $1/1280$ | 1 292 | $w_3$, 2nd | $[75,2\,090]$ | 10 988.51 |
| $\varepsilon^4/10$ | 2 090 | $w_2$, 2nd | $[189,2\,090]$ | 17 779.78 |
| $\varepsilon^5/10$ | 8 855 | $w_1$, 4th | $[804,8\,855]$ | 75 326.30 |
| $\varepsilon^6/10$ | 37 512 | $w_2$, 2nd | $[3\,409,37\,512]$ | 319 097.31 |

So the Fibonacci exit $K(\delta_k)=(F_{3k+7}-1)/2$ is **exact** for $k=0,\dots,6$ (the note
had $k=3,4,5$ in double precision only), $\delta_kK(\delta_k)\to0.6492$ and
$\delta_k\cdot$reach$\to5.52$. The exit sites agree with §4 ($-\varphi^{-1}$, $-\varphi^{-3}$,
$1$ where stated). Chord reach is a double-precision evaluation of exact data, as the note says.

**Observation 2.** At $r_c$ (cap $4\cdot10^6$, `--conj-min 200`, so generations from 132 on) the ratio lies in $[1.5070,1.5227]$ for every generation recorded and in $[1.5131,1.5155]$ for $g\ge1\,000$, as stated. My run's last (partial) generation is 2 437 rather than 2 432; where the cap cuts the last generation depends on the run, and the ranges are unaffected. At level 2 the ratio (largest conjugate modulus in generation $g$)$/g$
lies in $[1.5070,1.5268]$ for $100\le g\le640$, as stated; the maximum is $984.5$ at $g=650$ and
then jumps down to $851$ at $g=660$.

**What rests on floating point.** In the note as published: the chord times at levels 3–5 and
at $1/640$ (now exact, above); chord reach, $M_0$ and $\delta M_0$ (double evaluations of exact
points; the decisions are far from ties, and the claims are inequalities with wide margins); the
window counts of Observation 5 (now exact at the four radii, same numbers). Nothing presented as
exact rests on floating point, apart from issue 3.

Not re-run: Observation 4 (sector maxima), the
cut-set statistic quoted in Conjecture A.

## 5. The assessment, and what is salvageable

**Is "bounded invariant region $\Leftrightarrow$ finiteness" right?** Yes, at non-norm radii:
$W_r$ of §3.0 is bounded and invariant when $M(r)<\infty$, and a bounded invariant set containing
$(D_1\cup D_2)\times\{0\}$ bounds $M(r)$. Compactness is not available (issue 6). But the
equivalence is also true, in the same tautological way, of every reformulation of (B); it does not
show the line is dead. What Propositions 2, 3 and Corollary 7 show is that the region must be
fibred, $r$-dependent and of internal size at least $0.5/\delta$. These are design constraints.
Proposition 2 in particular only rules out *strict* Lyapunov functions on an invariant set, which
nobody would use; it says nothing against functions that may increase by a bounded amount per
window visit.

I agree with the conclusion that a region cannot be written down from the conjugate coordinate
alone. I disagree that nothing provable is left. Suggestions, in order of how directly they build
on Theorem 6:

1. **Theorem 6 for every lattice seed on the chord.** Steps 1–2 do not use the seed. For a seed
   $s_0E$ with $s_0\in\mathbb Z[\varphi]$, (3.2) becomes
   $\operatorname{dist}(t_k,B)\ge1/(2\sqrt5k+|\sigma s_0|+1+\varphi^3)$ unless the orbit hits a
   breakpoint exactly, which is a finite parity/norm check. The upper bound does not need the
   Fibonacci identity: since *both* sides of $b^\ast$ are tight (Step "Exit"), any $k$ with
   $|t_k-b^\ast|\le\delta/\sqrt5$ ends the chord, and the three-distance theorem for rotation by
   $\varphi^{-1}$ gives such a $k\le C/\delta$ for every seed, with explicit $C$. Result: for
   every lattice seed on the chord, the chord part of its orbit has conjugate growth between
   $0.5/\delta-|\sigma s_0|\cdot{\rm const}$ and $C/\delta$. This makes Theorem 6 a statement
   about the chord, not about one orbit.
2. **A tube of width of order $\delta$ around the chord.** (3.1) has slack
   $(3-\varphi)(s-b)(b'-s)-\delta$, and each $f_m$ is Lipschitz in the physical point. So every
   point within physical distance $c\,\delta$ of $sE$, with $\operatorname{dist}(s,B)\ge
   C\kappa\delta$, follows the same chord words, and every lattice point there drifts in the
   conjugate coordinate by the same vectors $-2\varphi\sigma E$, $-2\varphi^2\sigma E$. This
   gives an explicit fibred piece of the region of Conjecture A: over the tube, internal extent
   $\Theta(1/\delta)$, proved. It is the natural first block of "an $r$-dependent fibred region
   of radius $C/\delta$".
3. **Conjecture A for the orbit of $0$ alone.** $M_0(r)<\infty$ is equivalent to finiteness of
   $O_r(0)$ (lattice discreteness), which is open and weaker than (B). The data suggest exact
   self-similarity across levels: $M_0(\delta_{k+1})/M_0(\delta_k)=4.264,\ 4.2345$ for
   $k=1,2$ against $\varphi^3=4.236$, the maxima sit at $P+\lambda$ with $\lambda$ shrinking by
   $\varphi^3$, and $\delta_kM_0(\delta_k)=6.45,6.49,6.49$. A target statement: the level-$(k+1)$
   orbit of $0$, near the tight points, is the image of the level-$k$ orbit under the
   renormalization (physical zoom by $\varphi^{-3}$ about the tight point, hence internal
   multiplication by $\sigma(\varphi^{-3})=-\varphi^3$) up to a bounded set. That is the orbit-of-$0$ case of (R-core-t), and it is directly testable with
   the existing `--conj-points` output by matching extremal points across levels.
4. **A Lyapunov function that may grow at window visits.** Combine Corollary 4.3 of the
   combined note with the conjugate coordinate: $V(z,u)=|u|$ grows by at most $T_W$ between
   visits to $W^{\rm t}$ (the proof of Corollary 8). A bound on the *conjugate gain per tight
   excursion*, rather than on the number of visits, would give $M\le C/\delta$ if the number of
   *independent* excursions is bounded. The note's third bullet of §5.3 already points there;
   computing $T_W$ (the face count $F$ of the certified row) is the first concrete step.
5. **Rescaled limit.** Plot the rescaled lifted orbits $\{(y,\delta\sigma y)\}$ at levels 1–4. If
   the internal hull converges (the round hull of Observation 4 at radius $\approx6.49/\delta$
   suggests it does), the limit set and its dynamics are a candidate for the renormalization
   fixed point in conjugate form.

## 6. What I did not check

The cited results (Theorem A, Lemma 3.1, `sharp-lower-bound-n5.md` Theorem 4.1, the four-window
certificate, Proposition 4.4) were taken as refereed. I did not re-run Observation 4, the cut-set
figure quoted in Conjecture A, or any certificate. The Lean file
`TDCSG/CriticalRadius/FiveConjugate.lean`, added to the repository after the note, was not
examined.
