# Referee report: `sharp-bound-n5-orbit-of-zero.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$, conjugate coordinate II: every chord seed, the tube, and the orbit of $0$" (`sharp-bound-n5-orbit-of-zero.md`, commit `5c644e8`). Companions consulted: `sharp-bound-n5-conjugate.md` ("Part I") and its report; `sharp-bound-n5-invariant.md` (Lemmas 4–6, Theorem 7, Proposition 2) and its report; `sharp-bound-n5-critical-orbits.md` (D4, Table 2.1, Theorems 2 and 4, Corollary 2.1) and its report; `sharp-bound-n5-period-two.md`; `boundary-contact.md` Theorems 3.1 and 3.4; `../engine.md`.

## Summary

The mathematics is sound. Every proof was checked line by line and every constant re-derived to at least 10 digits (60-digit arithmetic). The defects are small:

- the upper bound of Theorem 9(3), and with it Theorem 11(1)–(2), was stated "for every $\delta>0$", but the proof only works for $\delta\le\sqrt5\varphi^{-2}=0.854$ (for larger $\delta$ the hole $J$ leaves the two intervals on which the tight tests were computed);
- the summary stated the forward lower bound for the backward passage too (the backward bound is one step less), and stated the level-to-all-radii transfer of Proposition 12(2) "at every $r<r_c$" where the proposition gives it for $\delta\le1/10$;
- Table 6.2 ("the first lines") skipped the line at $d/\delta=2.0163$, Table 6.1 had $\delta_4M_0=6.4924$ for $6.4923$, and the summary's radius $1.07$ for the scaled copies fails at $k=3$ ($1.0678$);
- Conjecture E claimed full conjugate segments over the chord for every chord-parallel line, which the note's own §6.3 contradicts for the lines whose window is not a rectangle.

All are fixed in the note, together with two clarifying remarks (the exceptional seeds of Theorem 9 are exactly the chord points of the congruence class of $E$, so they never occur in the orbit of $0$; the critical-orbits note has the better lower-bound constant). I reproduced, with the engine and independent exact code, the orbits at levels 0–4, the chord-line model set at levels 0–4, the 24 line pairs within $8\delta$ and their counts at levels 1–4, the period-two cores ($S_1=S_3$ and $S_2=S_4$) at all 38 critical points, the scaled-copy fractions, and the passage lengths. Nothing that the note calls exact rests on floating point, apart from the selection of candidate points by approximate coordinates, which was done with margins and followed by exact tests.

On the conjectures: Conjecture D has a provable half and a hard half. The data rule out a *regular* model-set description of the whole orbit (a fixed rescaled window with interior), but support a weaker and more useful one: each chord-parallel line near the chord is a finite union of passage windows. §5 gives the provable next statements.

## 1. Verdicts

| result | verdict |
|---|---|
| Theorem 9(1) exact hits | **correct** |
| Theorem 9(2) lower bound | **correct**; summary fixed (backward bound is one step less). Not the best available constant (§2, issue 5) |
| Theorem 9(3) upper bound $<\varphi^3/\delta$ | **correct after a range fix**: $0<\delta\le\sqrt5\varphi^{-2}$; for larger $\delta$ the note now gives $L^\pm\le4$ by monotonicity |
| Theorem 9(4) conjugate reach | **correct** (inherits the range of item 3) |
| Theorem 9(5) symmetric images | **correct** |
| Theorem 10 (coordinates, $dd'=N(m)/4$, Table 2.1) | **correct**; Table 2.1 recomputed exactly |
| Theorem 11(1)–(2) passage length and conjugate gain | **correct after the same range fix** |
| Theorem 11(3) long passages in the tube | **correct** |
| Theorem 11(4) boundedly many lines | **correct** |
| Proposition 12 | **correct**; summary range fixed ($\delta\le1/10$) |
| Proposition 13 | **correct** |
| §6 computations | **reproduced** (§3 below); Table 6.2 completed, one value of Table 6.1 and the radius of §6.4 in the summary corrected |
| Conjecture C | consistent with the data through level 4; not provable with present tools (§4) |
| Conjecture D | consistent with the data through level 4; the lower inclusion is provable in principle, the upper inclusion is as hard as bounding the orbit on the line (§4) |
| Conjecture E | consistent near the chord after the restriction to rectangle lines; evidence at odd levels is thin (§4) |
| §7 assessment | fair; one clarification added (passages of all four symmetric classes) |

## 2. Issues

1. **Range of Theorem 9(3) and Theorem 11(1)–(2).** The proof places the open hole $J=(b_1-\delta/\sqrt5,\,b_1+\delta/\sqrt5)$ in $I_1\cup I_2$, where the assigned words are $w_1$ and $w_2$ and the tight-test formula $r_c^2-\sqrt5d_*+(3-\varphi)d_*^2$ applies. That needs $\delta/\sqrt5\le\varphi^{-2}$, i.e. $\delta\le\sqrt5\varphi^{-2}=0.8541$. Beyond it, $J$ reaches $I_3$ (word $w_3$), and the parenthetical "if $j<3$ then $J$ contains $t_0$ or $t_{-1}$" did not repair this. The statement is still true for larger $\delta$ on the chord (my exact runs: $L^\pm\le1$ at $\delta=0.85$, $L^\pm=0$ for $0.9\le\delta\le4.5$ on 62 seeds), and the note now proves the weaker $L^\pm\le4$ there: the tests have fixed centres, so $L^\pm$ is non-increasing in $\delta$, and at $\delta=\sqrt5\varphi^{-2}$ the proof gives $j=5$, $L^\pm\le F_5-1=4$. (A full proof of $L^\pm<\varphi^3/\delta$ for all $\delta$ follows from the exact holes of critical-orbits Theorem 2: for $\delta\ge0.6525$ the tight letters of $w_1,w_2$ fail on all of $I_1\cup I_2$, and for $\delta\ge0.86$ those of $w_3$ fail on all of $I_3$. Nothing in the repository needs this range, so I did not add it.) The same restriction applies to the half-open arcs in the proof of Theorem 11(1), where it is now stated.
2. **Summary, backward lower bound.** Theorem 9(2) gives $L^-\ge\min(K_0,k^-_{\rm hit}-1)$, one less than the forward bound, so the summary's "forward and backward, at least $0.05901/\delta-0.2237|\sigma s_0|-1.40$" holds forward only; the backward constant is $2.40$. Fixed ("one fewer backward").
3. **Summary, Proposition 12(2).** The proposition transfers $M_0(r_k)\le C/\delta_k$ to $M_0(r)<\varphi^3C/\delta$ for $\delta\le\delta_0=1/10$ only; for $\delta>1/10$ one gets $M_0(r)\le M_0(r_0)\le10C$, which is not below $\varphi^3C/\delta$ near $\delta=r_c^2$. Fixed in the summary.
4. **Table 6.2.** The table is titled "the first lines" but omits the line at $d/\delta=2.0163$ ($|N(m)|=20$, $|\delta d'|=2.4798$, 2 962 and 12 542 points at levels 3 and 4); the key-norm list in the text does include it. Row added.
5. **Theorem 9(2) is not the best lower bound in the repository.** It uses Part I's safe distance $\kappa\delta$, $\kappa=3.789$. The exact holes of critical-orbits Theorem 2 (width $h(\delta)=\delta/\sqrt5+O(\delta^2)$) give, by the same Diophantine argument, $L^+\ge(1/h(\delta)-c(s_0))/(2\sqrt5)\ge0.4858/\delta-0.2237\,c(s_0)$ for $\delta\le1/10$, about $8.2$ times better, for every non-exceptional seed. For $s_0=0$ this is critical-orbits Corollary 2.1 ($0.97/\delta-3$ chord points, internal extent $4.13/\delta-12$). A sentence saying so is added after Theorem 9; replacing item 2 is left to the authors.
6. **Exceptional seeds and the orbit of $0$** (clarification, added). The exceptional classes $1+2\mathbb Z[\varphi]$ and $\varphi^2+2\mathbb Z[\varphi]$ of Theorem 9(1) are exactly the $s$ with $s=a+b\varphi$, $a$ odd. Since $E=\zeta(1-\zeta)$, the residue of $sE$ modulo $K=2(1-\zeta)\Lambda$ depends only on $s$ modulo $2\mathbb Z[\varphi]$; I checked exactly that $s\equiv0,\varphi$ give the $\Gamma$-class of $0$ and $s\equiv1,\varphi^2$ the class of $E$. So the chord points of $O_r(0)$ are never exceptional, and the condition "$a\in2\mathbb Z$" of the model set in §6.2 is precisely the congruence class, not an extra arithmetic fact.
7. **Conjecture E** (wording). It asserted that the fibre over a chord point contains the full segment $|\tau|\le w_i$ of every line of §6.3. On lines whose window is not a rectangle (most of them: at level 2, 19 of the 24 positive offsets), the conjugate values near a given $s$ fill only part of the range. Restricted to the rectangle lines; and the internal radius $6.492$ is now quoted with the odd levels, which have not settled ($6.4496$, $6.4899$).
8. **Table 6.1 and the summary's item 4(d).** $\delta_4M_0=6.4923$, not $6.4924$ (from the engine's $M_0=20\,905.000$). The scaled-copy radius: at $k=3$ a point with $|y|=1.0678$ has $\varepsilon y\notin O_{r_4}(0)$, so "$|y|<1.07$" was false at the last level computed; now $|y|<1.067$ for $k=0,\dots,3$, with the $k=3$ values added to §6.4.
9. **Minor.** The note cited the critical-orbits note as "not refereed"; it is refereed (fixed). Part I's status paragraph still calls this note "not refereed"; I did not edit Part I.

## 3. Reproduction

**Engine runs.** `tdcsg-orbit` (the repository build at `.lake/build/bin`, copied to a scratch folder), `orbit -n 5 --format lines --conj-points` at the five level radii of §8, the point records reduced on the fly to their exact coefficient vectors.

| $k$ | $|O_{r_k}(0)|$ | `conj 2` ($M_0$) | $\delta_kM_0$ | points on $\mathbb RE$ | $2F_{3k+9}-(-1)^k$ |
|---|---|---|---|---|---|
| 0 | 1 433 | 53.746124 | 5.3746 | 67 | 67 |
| 1 | 30 165 | 273.20980 | 6.4496 | 289 | 289 |
| 2 | 400 519 | 1 164.9963 | 6.4923 | 1 219 | 1 219 |
| 3 | 5 673 561 | 4 933.1920 | 6.4899 | 5 169 | 5 169 |
| 4 | 76 031 321 | 20 905.000 | 6.4923 | 21 891 | 21 891 |

All agree with Table 6.1 except $\delta_4M_0$: $20\,905.000\cdot\varphi^{-12}/10=6.49230$, so the note's $6.4924$ was wrong in the fourth decimal (fixed; the even levels agree, $6.49230$ and $6.49230$). $M_0$ is the engine's double-precision maximum of exact points, as the note says.

**Independent exact code** (Python with integer arithmetic in $\mathbb Z[\zeta]$ and $\mathbb Z[\varphi]$; signs of $a+b\varphi$ decided by integers):

- *Table 2.1 and Theorem 10.* Pull-back centres and $\gamma_{im}$ recomputed: all 16 entries agree. Theorem 10(1), (2) checked on all $13^4$ points with coefficients in $[-6,6]$ ($2s\in\mathbb Z[\varphi]$, $s'=\sigma(s)$, $d=\tfrac\varphi2m$, $d'=\sigma(m)/(2\varphi)$, $4dd'=N(m)$, minimum $|N|=1$ off the chord); Theorem 10(4) checked at 1 000 random real points.
- *Passages.* Letters applied exactly, inverse words applied directly for the backward passage (not via the forward test). From $0$: $L^+=L^-=6,27,116,493,2\,090$ at levels 0–4 and $8\,855$, $37\,512$, $158\,905$, $673\,134$ at levels 5–8, all equal to $(F_{3k+7}-1)/2$. On the 62 chord seeds $a+b\varphi\in[-1,1)$, $|b|\le15$, at $\delta=1/10,1/20,1/40,1/80,1/160,1/320$: Theorem 9(1) (exact hits only in the exceptional classes, within $c(s_0)/(2\sqrt5)$), 9(2) (both inequalities with $\min$, and the numerical forms), and 9(3) hold on every seed; $\max\delta L^\pm=1.2$. Off the chord, 150 orbit points with $0<|d|\le3\delta$ at levels 1 and 2 and 60 at level 3: $\max\delta L^\pm=1.277$ (bound with Lemma 5: $4.236$), the conjugate gain inequality of Theorem 11(2) holds at every step, and the lower bound of Theorem 11(3) holds.
- *Three-gap lemma.* Gaps of $\{k\varphi^{-1}\}$, $0\le k<F_j$, at 60 digits for $3\le j\le23$: maximum $\varphi^{-(j-2)}$, minimum $\varphi^{-(j-1)}$.
- *Constants.* $1/(2\sqrt5\kappa)=0.0590169944$, $1/(2\sqrt5)=0.2236067977$, $(2+\varphi^3)/(2\sqrt5)=1.39443$, $2\sqrt5\varphi^3|\sigma E|=36.0341465$, $|\sigma E|=1.9021130$, $|\sigma E|/\kappa=0.5020285$, $4\sqrt5\varphi^3|\sigma E|=72.0682930$, $2|\sigma E|=3.8042261$, $5|\sigma E|=9.5105652$, $1/(8\sqrt5\kappa)=0.0147542$, $3\varphi-1=3.8541020$, $\varphi^7/10=2.9034442$. Every rounding in the note goes the safe way.
- *§6.2, model set.* All $a+b\varphi$ with $a$ even, $sE\in D_1\cup D_2$ (exact disk test) and $|\sigma s|\le4/\delta_k+10$ enumerated; membership looked up. At every level 0–4 every window point with $|\sigma s|\le\max_{\rm in}$ is in the orbit and none with $|\sigma s|\ge\min_{\rm out}$ is (compared exactly), no orbit point on the line has $a$ odd, and the brackets are $[2.80344,2.94164]$ (level 0, not in the note), $[2.89443,2.92705]$, $[2.89787,2.90557]$, $[2.90294,2.90476]$, $[2.90313,2.90356]$ (level 4). The points of $2\mathbb Z[\varphi]\cap[-1,1)$ in the orbit number $13,55,233,987,4\,181=F_{3k+7}$, exactly the passage of $0$ (Proposition 13).
- *§6.3, lines.* Keys computed exactly; the positive offsets within $8\delta_k$ are 20 at level 0 and the same 24 at levels 1–4; the key set at level $k+1$ is exactly $\varepsilon$ times the key set at level $k$ for $k=1,2,3$ (and contains it for $k=0$); the sign of $N(m)$ alternates with the level. Counts on the lines at $0.3851\delta$ and $0.6231\delta$: $116,493,2\,090,8\,855$ and $288,1\,220,5\,168,21\,892$ (levels 1–4). The Table 6.2 ranges agree to the printed digits. The "full box" lines at level 2 are exactly the chord line and the lines at $0.3851,1.6312,2.4013,2.8773,6.1397$.
- *§6.1, cores.* The 38 critical points found by exact search; zoomed sets compared as sets of exact vectors with the exact test $|\eta|^2\le9/100$. Sizes $26,47,47,47,47$ (tight), $7,35,19,35,19$ (lens corners), $7,25,17,25,17$ (the twelve), $14,1,0,0,0$ (16 points), $28,11,2,0,0$ (4 points); $S_1=S_3$ and $S_2=S_4$ at the 18; $|S_1\cap S_2|=34$ at the tight points; $S_0\subseteq S_2$. At $Q=E$: $|T_k(E,\tfrac12)|=68,120,124,126$ and $126$ (levels 0–4), with $T_1\subseteq T_3$ and $T_2\subseteq T_4$ at $\rho=\tfrac12$ and $4$; at $Q=0$, $|T_k(0,0.3)|=29,49,53,53,53$ and $T_2\subseteq T_3\subseteq T_4$ at $\rho=0.3,\tfrac12,4$.
- *§6.4.* $\varepsilon\cdot O_{r_k}(0)\cap O_{r_{k+1}}(0)$: $67.90\%$, $67.85\%$, $67.97\%$ for $k=0,1,2$ and $68.00\%$ for $k=3$; the smallest $|y|$ of a miss is $1.1927$, $1.1130$, $1.0739$, $1.0678$. For $\varepsilon^2$: $77.39\%$, $77.53\%$, $77.94\%$ ($k=0,1,2$). The summary's "every $y$ with $|y|<1.07$" therefore failed at $k=3$; it now reads $|y|<1.067$, $k=0,\dots,3$, and §6.4 gives the $k=3$ values. I did not redo the 875-map vote.

## 4. The conjectures

**Conjecture C (period two at the cores).** Reproduced through level 4. It is a statement about finitely many points per level ($\le47$), but each is decided by the whole orbit, so a proof needs a correspondence of chains between levels $k$ and $k+2$, which is the open tight-window renormalization. `sharp-bound-n5-period-two.md` shows that period two fails for general first-return sets, so any proof must use features of the orbit of $0$. I see no route to it with the present tools.

**Conjecture D (the chord line is a model set).** It has two halves.

- *Lower inclusion* (every window point is in the orbit). This is provable in principle. On $[-1,1)\cap2\mathbb Z[\varphi]$ it is Proposition 13 plus the exact passage length $L^\pm(0;r_k)=(F_{3k+7}-1)/2$, which I computed exactly up to level 8. That length is provable for all $k$ by a finite argument: the exact holes (critical-orbits Theorem 2) have width $h(\delta_k)$; the approach distances $|t_k-b|$, $|k|<(F_{3k+7}-1)/2$, are non-zero elements $x\in\mathbb Z[\varphi]$ with $|x|$ of order $\delta_k$ and $|\sigma x|$ of order $1/\delta_k$, hence of bounded norm, so they are units times finitely many elements; multiplication by $\varepsilon$ maps the configuration at level $k$ to the one at level $k+1$; so a check at one level, plus the unit scaling, covers all levels. The coset $\varphi+2\mathbb Z[\varphi]$ on $[-1,1)$ is a second single passage in the data (§6.3 run counts below), and the points with $|s|>1$ need explicit routes. Both are finite-pattern statements of the same kind.
- *Upper inclusion* (no other point of the line). This bounds $|\sigma|$ on the chord line of the orbit, so it needs control of every route to the line. It is not easier than Conjecture A for this orbit restricted to one line, and it does not by itself give finiteness.

**Is the whole orbit a model set?** A model-set description in the strong sense, $O_{r_k}(0)=\{y\in\Lambda_0:\ (y,\delta_k\sigma y)\in W\}$ for a fixed compact $W\subset\mathbb C\times\mathbb C$ with interior and boundary of measure zero ($\Lambda_0$ the congruence class), is ruled out by the counts: such a set has about $c\,\delta_k^{-2}$ points, a factor $\varphi^6=17.9$ per level, while the orbit grows by $13.3$–$14.2$ per level ($|O|\sim\delta^{-1.82}$). A product window $\{y\in X,\ \sigma y\in U\}$ is excluded for a second reason, the argument of Part I Proposition 3 applied to lattice points near $0$, whose conjugates are dense in $U$. So the window, if any, must be fibred over physical space and its rescaled limit must have measure zero. The data support a weaker statement line by line, which I checked:

| level | lines (both signs) within $8\delta$ | lines equal to their lattice coset in the convex hull of their points | maximal $T$-runs on $[-1,1)$ per line (positive offsets, in order of $d$) |
|---|---|---|---|
| 1 | 49 | — | 2,1,2,2,2,1,2,1,6,1,4,2,2,4,6,4,8,2,10,1,6,3,2,8,16 |
| 2 | 49 | 11 | 2,1,2,2,2,1,2,1,6,1,4,2,2,4,8,4,8,2,10,1,6,3,2,6,10 |
| 3 | 49 | — | 2,1,2,2,2,1,2,1,4,1,4,2,2,4,6,4,8,2,10,1,6,3,2,6,10 |
| 4 | 49 | — | 2,1,2,2,2,1,2,1,4,1,4,2,2,4,6,4,8,2,10,1,6,3,2,6,10 |

(The first entry is the chord line. A run here is a maximal chain $x,\,x+\tau E,\dots$ of orbit points on the line linked by the steps of $T$, found by lookup; the hull test, exact up to a $10^{-9}$ tolerance in the point-in-polygon test, was run at level 2.) Within $[-1,1)$, every line near the chord is a union of a few maximal runs of the chord rotation, each of which is a parallelogram window in the coordinates $(s,s')$ by the argument of Proposition 13; the numbers of runs agree on all 25 offsets at levels 3 and 4 (and on 23 of them at levels 2 and 3), and the lines with a single run are exactly the "full box" lines of §6.3. On most lines the union is not convex (holes inside the hull), so a window there is a finite union of parallelograms, not a rectangle.

**Conjecture E.** Consistent near the chord with the restriction now in the note. The two parities are not equally supported: $\delta_kM_0=6.4923,6.4923$ at levels 2 and 4 but $6.4496,6.4899$ at levels 1 and 3. Under $y\mapsto\varepsilon y$ the rescaled pair $(y,\delta\sigma y)$ goes to $(\varepsilon y,-\delta\sigma y)$, because $\varepsilon\sigma(\varepsilon)=-1$; with the symmetry $y\mapsto-y$ of the orbit this is $(-\varepsilon y,\delta\sigma y)$. That is the mechanism behind the sign alternation and fits the parity split of E.

## 5. What I recommend next

The most promising provable next statement is a **line-by-line model-set theorem in the tube**:

> For every level $k$ and every key $m$ with $|d(m)|\le c\,\delta_k$, the set $O_{r_k}(0)\cap\{s(x)\in[-1,1)\}$ on the line of key $m$ is a union of at most $N(m)$ maximal passages, each of exact length given by a Fibonacci expression in $k$, so it is a finite union of parallelogram windows; $N(m)$ and the window shapes in rescaled coordinates depend only on $\varepsilon^{-k}m$.

Its ingredients are all of the proved type: exact holes on each line (Theorem 10(4) with critical-orbits Theorem 2 gives the hole on a line of offset $d$ as an explicit quadratic in $d$), the Diophantine estimate of Theorem 11(3), the three-gap lemma, and the $\varepsilon$-scaling of keys (Theorem 11(4)). The first case, the chord line ($m=0$, two runs), would prove the lower inclusion of Conjecture D on $[-1,1)$ for all levels; already its part for the passage of $0$ gives the sharp chord bound $\delta_kM_0\ge|\sigma E|\varphi^7/10-o(1)=5.52-o(1)$ along the levels. The step from there to finiteness is the one the note names: bounding the number of passages, i.e. which lines and which seeds are entered, which is the renormalization problem. A concrete test of it: record, for each run at level $k+1$, the run at level $k$ whose $\varepsilon$-image it extends, and check whether the run graph is the same at every level.

Smaller items:
1. Replace Theorem 9(2) by the exact-hole version (issue 5).
2. State Theorem 11 for the four symmetric classes explicitly (the note now says so in §7).
3. Of the three notes that state cut-off constants, the best proved ones are now: steps of a chord passage, uniformly over all starting points, $<\varphi^3/\delta=4.24/\delta$ (this note, Theorem 11(1) with Lemma 5; better than $5.86/\delta$ of the invariant note's Theorem 7 because the three-gap lemma gives the sharp gap); conjugate gain per passage $<36.04/\delta+13.4$ (this note; the invariant note's $58.4/\delta+9.6$ is weaker for every $\delta\le2/5$); for the orbit of $0$, at most $\varphi^3/(2\delta)=2.12/\delta$ steps forward and conjugate $<18.02/\delta+1.91$ along it (Part I Theorem 6(3)), and at least $0.97/\delta-3$ chord points and internal extent $4.13/\delta-12$ (critical-orbits Corollary 2.1, which supersedes Part I's $0.059/\delta$ and $0.502/\delta$). The three agree: every stated upper bound lies above every stated lower bound, and the computed truth ($\delta L\approx1$–$2.6$, $\delta\cdot$reach $\approx5.5$–$22$) lies between them.

## 6. What I did not check

The cited results (Part I Theorems 4 and 6, the invariant note's Lemma 5 and Proposition 2, critical-orbits Theorems 2 and 4, `boundary-contact.md` Theorems 3.1 and 3.4) were taken as refereed; I re-checked only the parts used here (Lemma 5's identities exactly; the tight-letter derivatives of Part I). I did not redo the 875-map vote of §6.4, the inclusion $T_2\subseteq T_4$ at $\rho=6$ at $Q=E$, or the $\rho\le6$ chain at $Q=0$ beyond $\rho=4$. The level-4 run was filtered by approximate coordinates (margins $1\%$ or more) before the exact tests, as in the note.
