# Referee report: `sharp-bound-n5-critical-orbits.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Orbits of $GG_5$ at the critical radius $\sqrt{3+\varphi}$: the chord, its tube,
and what survives below" (`sharp-bound-n5-critical-orbits.md`, commit `23e1c63`). Companions
consulted: `critical-radius-n5.md` §§1–4 (Lemma 3.1 and its trajectory table, Theorem A, Lemma 4.1,
Theorem 4.2), `sharp-lower-bound-n5.md` §§2–3 (Lemma 2.2, Corollary 2.3, Lemma 3.0, Theorem 3.1),
`sharp-lower-bound-combined.md` §§3–4 (Definition 3.1, Lemma 3.3, Corollary 4.3),
`sharp-lower-bound-limit-system.md` (Table 4.2, Corollary 4.4), `boundary-contact.md` (Lemma 2.1,
Theorems 3.1, 3.4, 5.1, Proposition 3.3), `../relative-certificates.md` §8 and its referee report,
`sharp-bound-n5-conjugate.md` and its referee report, and `../engine.md`.

## Summary

The proofs are sound. I checked each one line by line and re-derived every constant to at least
20 digits. Two statements needed small repairs, and one conjecture is false as stated.

- **Theorem 2** says the domain of each chord word "on the chord" is exactly the interval given.
  That is true only inside each word's own segment: $w_2$ also applies to the right of
  $b_3=-\varphi^{-3}$, on almost all of $[b_3,1]$. The proof and Corollary 2.1 use only the
  segment version. **Fixed** (wording), together with the description of the holes ("three
  one-sided holes … $b_1$ (both sides)" was four holes).
- **The comparison with the conjugate note** is consistent, and the new constants are right. The
  conjugate note's lower bound used the crude safe distance $\kappa\delta$ with $\kappa=3.789$.
  This note uses the exact hole width $h(\delta)\approx\delta/\sqrt5$. That accounts for the factor
  of about 8 (forward steps $\ge0.4858/\delta-1.18$ here, against $0.059/\delta$ there). Both
  lower bounds lie below the conjugate note's upper bound $2.12/\delta$, and below the data
  ($\delta K\to0.649$). One rounded constant in the quotation of the earlier note was **fixed**.
- **Theorem 5** (openness at non-norm radii) is correct. It uses only refereed results:
  Corollary 2.3, Lemma 3.0 and Theorem 3.1 of `sharp-lower-bound-n5.md`, the §8 argument of
  `relative-certificates.md`, and Theorem 4.2 of `critical-radius-n5.md`. Its extension to
  $r_0^2\notin\mathbb Q(\varphi)$ is valid. Corollary 5.1 follows.
- **Conjecture K3 is false as stated.** A lattice point on a line at offset $s\ll\delta$ has an
  orbit with about $1/\delta$ points on that line, because there the chord words act as they do
  on the chord. Computed at levels 1, 2, 3 (§5). This is not a minor fix. I added a flag at K3
  in the note.
- All computed claims I re-ran agree exactly. That covers §4.1, the 19-orbit classification of
  §4.2, the $3\cdot10^7$ runs, every row of the line table §4.3, the distance data, and §4.4.

## 1. Verdicts

| result | verdict |
|---|---|
| Theorem 1 (strict chord rotation; tight parameters; exceptional set $X$) | **correct** |
| Corollary 1.1 | **correct** |
| Theorem 2 (hole formula $h(\delta)$, domains, range $\delta<0.65$) | **correct after a minor fix**: the domains are exact inside each word's segment, not on the whole chord ($w_2$ applies beyond $b_3$); the holes are on both sides of $b_1$, right of $b_3$ and left of $1$ |
| Corollary 2.1 ($0.97/\delta-3$, $0.226/(r_c-r)-3$, $4.13/\delta-12$, $\delta\le1/10$) | **correct**. All constants are safely rounded. The $r$-form needs the sharper $0.9715/\delta-2.35$ of the proof, which the proof states |
| Proposition 2.2 (height drops by $2\sqrt5$) | **correct** |
| Proposition 2.3 (tube domains), Table 2.1 | **correct**; every centre, slack, tight test, $f'(0)$ and $L^2$ recomputed exactly |
| Theorem 3 ($36.26/d^2$), Corollary 3.1 | **correct** ($5\,\mathrm{Area}/\pi=36.25971$) |
| Theorem 4 (80 residues, 20 classes, 7 chord residues in 2 classes) | **correct**; recomputed exactly and derived by hand (§3) |
| Theorem 5, Corollary 5.1 | **correct** (§3) |
| Lemma 6 | **correct** |
| Proposition 6.1 | **correct**; item 2 cited a statement with a supremum over orbits where the per-orbit bound from its proof is used (**fixed**) |
| §4.1–§4.4 computations | **reproduced** (§4) |
| §4.5 "box-counting dimension about 1.8" | **overstated** (not re-run): the counts still grow with the number of points in every column, so they give no dimension estimate. **Wording fixed** |
| Conjectures K1, K2, K4 | consistent with the data; K2's pointer to a first-order computation "in §4.1" pointed to nothing; the computation is in §4 below (**fixed**) |
| Conjecture K3 | **false as stated** (§5); needs a restriction on the starting points |

## 2. Issues

1. **Theorem 2, domain on the chord.** At every $\delta<0.65$ the 2nd letter of $w_2$ has slack
   $-22+14\varphi=0.6525$ at $G'$, so $w_2$ also applies just to the right of $b_3$. In fact at
   $r_c$ it applies on all of $[b_1,1]$ (bisection in 40-digit arithmetic: right end
   $b_3+1.23607$), and at $\delta=10^{-3}$ up to $b_3+1.2356$. There it maps $t$ to
   $t+2\varphi^{-1}>1$, onto the long segment of K4, not by $T$. "The set of parameters $t$ at which
   $w_2$ applies on the chord is exactly $[b_1+h,b_3]$" is therefore false. The intended
   statement, inside the segment, is what the proof shows and what Corollary 2.1 uses.
   **Fixed.** The same remark explains how the orbit of $0$ reaches $\mathbb RE$ beyond
   $\mathcal C$.
2. **Hole description.** "Three one-sided holes of width $h$ next to $b_1$ (both sides), $b_3$
   (right) and $b_2$ (left)" describes four holes, two of them at $b_1$. The abstract said "three
   holes of width $\delta/\sqrt5$". **Fixed** in both places.
3. **Quoted constant.** The note quoted the conjugate note's Theorem 6 as
   $0.059/\delta-1.17<K$. The proved bound is $0.05901/\delta-1.171$, and
   $0.059/\delta-1.17$ does not follow from it for $0.01<\delta\le1/20$. The abstract of that note
   says $0.0590/\delta-1.18$, which is safe. **Fixed.**
4. **Proposition 6.1(2), citation.** Corollary 4.4 of the limit-system note and Corollary 4.3 of
   the combined note are stated with $\sup_x|O_r(x)\cap W|$. The per-orbit bound used here,
   $|O_r(x)|\le\beta\max(1,|O_r(x)\cap W^{\rm t}|)$, is what their proof gives (its first and
   fourth bullets). **Fixed** (one sentence).
5. **"The infinite set is closed"** (§6.1) is conditional: Corollary 5.1 gives it unless
   $r_{\rm crit}$ is a norm radius with a finite group. **Fixed.**
6. **D8 wording.** "This includes every $r$ with $r^2\notin\mathbb Q(\varphi)$" read as if norm
   radii included them. **Fixed.**
7. **§4.2, distinctness of capped runs.** The skip rule makes the 15 finite orbits a genuine
   classification. But two capped runs could a priori belong to one orbit beyond the cap. They do
   not: their starting points lie in four $\Gamma$-classes of four different symmetry types, and
   $z\mapsto-z,\bar z,-\bar z$ normalize $\Gamma$ and every $GG_5(r)$ ($-A(-z)=B(z)$,
   $\overline{A(\bar z)}=A^{-1}(z)$). So "19 orbits up to symmetry" is right. **Sentence added.**
8. **§4.5.** The cell counts at $h=0.02$ and $h=0.01$ grow from $10^6$ to $4\cdot10^6$ points
   ($27\,192\to27\,896$, $90\,676\to94\,508$). Neither the orbit closure nor its dimension is
   reached. Calling the slopes "lower estimates" of a box-counting dimension has no basis.
   **Wording fixed** (summary and §4.5).
9. **K2's pointer.** "By the first-order tube computation of §4.1" refers to a computation that
   is not in §4.1. **Fixed**: it now points to §4 of this report.
10. **K3** (§5). Not fixed beyond a flag in the note, since a correct replacement is a research
    choice.
11. **Summary bullet "organized along lines at offsets $\pm c\varphi^{-m}$"** was selective. At
    cap $4\cdot10^6$ the orbit of $-\zeta^2$ has lines that are not of this form with comparable
    populations between the listed ones (offset $-8.73\cdot10^{-4}$ with 2 158 points, against
    2 458 on the line $m=13$). The orbit of $0$ has lines with keys $2K^{\rm L}_m$, at offset
    $\sqrt5\varphi^{-m}$. §4.3 already said so; the abstract now does too. **Fixed.**

## 3. Proof checks in detail

- **Theorem 1.** Strict convexity: correct. The endpoint tests (Table 2.1, recomputed) are tight
  exactly at $t=b_1$ ($w_1$ letters 3, 4; $w_2$ letters 2, 3), $t=b_3$ ($w_3$ letters 5, 6) and
  $t=1$ ($w_3$ letters 1, 2), and nowhere else. The slacks of $w_1$ at $E'$ are
  $-2+4\varphi,-2+4\varphi,-8+6\varphi,-22+14\varphi,-38+26\varphi$, as stated. The smallest
  non-tight slack anywhere is $-22+14\varphi=0.652476$. $T^k(t)\in t+2\mathbb Z[\varphi]$, and
  $b_1\in\varphi^2+2\mathbb Z[\varphi]$, $b_2,b_3\in1+2\mathbb Z[\varphi]$. Reverse chains are
  strict because rotation preserves the distance to the centre. Corollary 1.1: a strict chain is
  an $r$-chain for $r$ at least the largest of its finitely many step distances; conversely an
  $r$-chain with $r<r_c$ is strict after deleting trivial steps.
- **Theorem 2.** On each segment, each test is a convex quadratic $f$ in the segment parameter.
  The leading coefficient $L^2=|E|^2\ell^2$ is the same for all letters of a word, since rotations
  preserve length: $18-11\varphi$ for $w_1,w_2$ and $28-16\varphi$ for $w_3$. The binding
  derivatives are $4-3\varphi$ ($w_1$ letter 4 and $w_2$ letter 2 at $F'$) and $-6+2\varphi$
  ($w_3$ letters 2 and 5). The other tight letters have $-10+5\varphi$ and $10-10\varphi$, larger
  by $\sqrt5$, so their holes are smaller. Exact identities checked:
  $(2-\varphi)(2\varphi-1)=3\varphi-4$, $(2\varphi-2)(2\varphi-1)=6-2\varphi$,
  $5(18-11\varphi)=(3-\varphi)(25-15\varphi)$, $5\cdot4(28-16\varphi)=4(3-\varphi)(40-20\varphi)$.
  The smaller root is $s_-=2\delta/(|f'|+\sqrt{f'^2-4L^2\delta})$, so $\ell s_-=h(\delta)$. The
  discriminant needs $\kappa\delta<1$ ($\kappa=1.105573$). The $w_1$ domain stays non-empty at
  $\delta=0.65$: $h(0.65)=0.37987<\varphi^{-2}=0.38197$. Independent check: bisection of the four
  domain ends with the words applied as complex maps (40 digits), at $\delta=0.1,0.01,10^{-5}$.
  All four ends match $h(\delta)$ to 20 digits.
- **Corollary 2.1.** $N(b_2)=1$, $N(b_1)=N(b_3)=-1$, and the norm is odd on $b+2\mathbb Z[\varphi]$.
  $\sigma(T^k0)=T^k0-2\sqrt5k$, $|\sigma b|\le\varphi^3$, $1+\varphi^3=5.2361<5.24$. Forward
  steps $N\ge(1/h-5.24)/(2\sqrt5)$, backward $N-1$, total $2N$ chord points. For $\delta\le1/10$,
  $(1+\sqrt{1-\kappa\delta})/2\ge0.9715514$, so the count is
  $\ge0.9715433/\delta-2.3434$ (stated $0.9715/\delta-2.35$). The $r$-form is
  $0.9715433/(2r_c)=0.226049\ge0.226$. The extent is
  $(1/h-6.24)\cdot1.902113\ge4.13225/\delta-11.870$.
- **Propositions 2.2, 2.3.** $\sigma(2\varphi^{-1})-2\varphi^{-1}=-2\sqrt5$ and
  $\sigma(-2\varphi^{-2})+2\varphi^{-2}=-2\sqrt5$. $U_i(r)=\bigcap_jD(h_{ij}^{-1}p_{ij},r)$
  because $h_{ij}$ is an isometry. $U_i(r_c)$ has interior: the midpoint of each segment lies
  strictly inside every disk, by strict convexity.
- **Theorem 3.** The induction (a connected open set missing $K$ lies inside or outside each
  disk), the fact that components go to components, and the count (at most 5 maps per image
  component, since $U$ is bounded) are all correct. The area is
  $2\pi r_c^2-(2r_c^2\arccos(1/r_c)-2\sqrt{r_c^2-1})=22.78265$, so $5A/\pi=36.25971$.
  Corollary 3.1: an arc of a circle meets a segment in at most two points.
- **Theorem 4.** Recomputed (Hermite normal form with rows
  $(2,0,0,8),(0,2,0,8),(0,0,2,8),(0,0,0,10)$, index 80; closure under $A^{\pm1},B^{\pm1}$). The
  result is 20 classes: 15 of size 5 and 5 fixed residues $(1,0,0,2j)$. There are 7 chord
  residues: 3 in the class of $0$ and 4 in the class of $E$. Under $\pm z,\pm\bar z$ the classes
  form 12 types. $-\zeta^2$ and $(-2,-2,-1,-1)$ are in the same chord-free class. A hand
  derivation confirms the count. $\Lambda/L\cong\mathbb F_{16}\times\mathbb F_5$ by the Chinese
  remainder theorem. $\Gamma$ acts trivially on $\Lambda/(1-\zeta)$, since $\zeta\equiv1$. On
  $\Lambda/2$, $A$ and $B$ both reduce to $z\mapsto1+\zeta^{-1}(z-1)$, because $1\equiv-1$. The
  orbits on $\mathbb F_{16}$ are therefore $\{1\}$ and $1+(\text{the three cosets of }\mu_5\text{
  in }\mathbb F_{16}^\times)$, which gives $5\cdot1+15\cdot5$. Chord points lie in
  $(1-\zeta)\Lambda$. **Remark (not a fix):** the coarser invariant $y\bmod(1-\zeta)$, the
  coefficient sum mod 5, already shows that an orbit with non-zero coefficient sum never meets
  $\mathbb RE\cup\mathbb R\bar E$. That follows from Lemma 1.1 of `critical-radius-n5.md` alone,
  covers 16 of the 18 chord-free classes, and covers all four examples of Theorem 4 (sums
  $-1,-3,-7,-6$). The mod-2 part adds the two remaining classes with sum $\equiv0$.
- **Theorem 5.** Corollary 2.3 extends verbatim to $r_0^2\notin\mathbb Q(\varphi)$, because
  $|z-c|^2$, $|c-c'|^2/4$ and squared circumradii of points of $\mathbb Q(\zeta)$ lie in
  $\mathbb Q(\varphi)$. Lemma 3.0 and Theorem 3.1 (1)⇒(2)⇒(3)⇒(C1)–(C4) use only that corollary.
  The closure "algorithm" of step (3) must then be read as the abstract closure procedure, since
  no exact program runs at such a radius; the proof does not use exactness of the program. The §8
  argument (refereed correct in `referee-report-relative-certificates.md`) is mathematical. Each
  (C1)–(C4) decision for a symbolic arc set is a sign of $4\rho-|c-c'|^2$ or an order of named
  points on one circle. Decisions change only at disk events ($\rho=|(c-p)/2|^2$, a norm) or
  triple events ($\rho$ a squared circumradius, a norm). Neither occurs at a non-norm $\rho_0$,
  and the finitely many candidate events give $\rho_1>\rho_0$. Crossing pairs stay crossing as
  $\rho$ grows (equal radii), so the symbols stay defined. Theorem 4.2 then applies to the moved
  arc set, which need not be $K(r)$. Corollary 5.1: $\mathcal I$ is an up-set (Theorem 3.4 of
  `boundary-contact.md`), and the dichotomy follows. Its last sentence ("(B) iff
  $\mathcal I=[r_c,\infty)$") is immediate from Theorem A and does not need Theorem 5.
- **Lemma 6, Proposition 6.1.** Lemma 6 is Lemma 3.3 of the combined note and Lemma 2.1 of
  `boundary-contact.md`, plus Proposition 3.3. In 6.1(3), at a non-norm radius no point of
  $\mathbb Q(\zeta)$ lies on a boundary circle, so case (A) of Theorem 5.1 holds. The statement
  needs $x\in\Lambda$ (or $\mathbb Q(\zeta)$), which the first clause supplies.

## 4. Reproduction

Engine: the repository's `tdcsg-orbit` (`orbit` subcommand only), copied to a scratch folder.
Stream filters of my own computed keys, offsets, chord membership and distances from the exact
coefficient vectors. Separate exact programs in $\mathbb Z[\zeta]$ and $\mathbb Z[\varphi]$
(integer sign tests) produced Table 2.1, the chord chains and the congruence classes. Nothing below
used a `certify` run.

**Chord chains (exact; every letter test exact, each step checked to land on $T(t)E$).**

| $\delta$ | forward | backward | chord points | hole-formula prediction (60 digits) |
|---|---|---|---|---|
| $1/10$ | 6 | 6 | 13 | 6 |
| level 1 | 27 | 27 | 55 | 27 |
| $1/55$ | 27 | 27 | 55 | 27 |
| level 2 | 116 | 116 | 233 | 116 |
| level 3 | 493 | 493 | 987 | 493 |
| level 4 | 2 090 | 2 090 | 4 181 | 2 090 |
| $1/1000$ | 1 292 | 1 292 | 2 585 | 1 292 |
| $1/10000$ | 5 472 | 5 472 | 10 945 | 5 472 |

So the counts are the Fibonacci numbers $F_{3k+7}$ at levels $0$–$4$, as stated (level 4 is new).
The full orbit sizes of $0$ at levels 0–3 ($1\,433$, $30\,165$, $400\,519$, $5\,673\,561$) were
reproduced.

**§4.2 classification** (`--cap 200000`, the note's skip rule): exactly the 19 runs of the table,
with the same sizes, chord counts ($695$, $872$), boundary counts ($10$ for the 643-point orbit,
$20$ for the class of $E$) and $\max|\sigma|$ to the digits given. The four capped runs start in
classes 0, 12, 3, 9 of my enumeration. These belong to four different symmetry types, so they
are four distinct orbits. With `--cap 30000000`: $-\zeta^2$ has $\max|\sigma|=1.4696\cdot10^4$ and
$(-2,-2,-1,-2)$ has $1.3702\cdot10^4$; boundary 0 and capped for both.

**§4.3 lines.** The keys $K_m=(F_m,2F_m,-F_{m-1},F_{m+2})$ and their Lucas analogues satisfy
$\varphi K_m+K_{m-1}=0$ and $|K_m|^2=c^2\varphi^{-2m}|E|^2$ ($c^2=1$, resp. $5$) **exactly** in
$\mathbb Z[\zeta]$, for $2\le m\le37$. So the offsets are exactly $\pm\tfrac12\varphi^{-m}$, resp.
$\pm\tfrac{\sqrt5}2\varphi^{-m}$, with alternating signs; this is stronger than the note's
numerical check. Every row of the table was reproduced with the same counts. That includes the
level-3 runs of $-\zeta^2$ ($11\,123\,374$ points: $m=19,17,15$ with $4\,675$, $8\,361$, $8\,361$)
and of $0$ ($5\,169$; $2\,090$; $5\,168$), and the ratios $s_{\min}/\delta_k$
($0.0658,0.0407,0.0658,0.0407$ and $0.38507$). At levels 0–2 I also ran $-\zeta^2$ with threshold
1: no single-point line is nearer than the listed one. The $m=15$ line of $-\zeta^2$ at $r_c$
(cap $4\cdot10^6$) has $t\in[-2.6159,2.6178]$, with 86–91 points per interior bin. The distance
sequence for $(-2,-2,-1,-2)$ was reproduced, and it is attained on the unit lines
($\tfrac12\varphi^{-m}$ for $m=8,12,14,16,18$).

**K4, direct data.** The $4\,541$ points of $O_{r_c}(0)$ on $\mathbb RE$ at cap $4\cdot10^6$ have
$t\in[-2.6173,2.6173]$, with 86–89 per interior bin of length $0.1$; $2\,806$ of them lie outside
$\mathcal C$.

**Lines at $r_c$ with growing cap** ($-\zeta^2$, $3\cdot10^7$ points; points on the Fibonacci
lines $m$):

| points | 7 | 9 | 11 | 13 | 15 | 17 | 19 | 21 |
|---|---|---|---|---|---|---|---|---|
| $10^6$ | 681 | 698 | 1 477 | 1 271 | 2 253 | 683 | — | — |
| $4\cdot10^6$ | 1 069 | 2 492 | 2 661 | 2 458 | 4 624 | 3 868 | — | — |
| $10^7$ | 2 055 | 3 694 | 2 962 | 3 687 | 6 743 | 6 742 | — | — |
| $3\cdot10^7$ | 2 055 | 6 338 | 8 100 | 3 687 | 11 922 | 11 924 | 8 238 | 6 889 |

The lines $m=7$ and $13$ stop gaining points after $10^7$; the others keep growing. A capped run
cannot say whether any line carries infinitely many orbit points.

**First-order holes on offset lines** (40-digit bisection on the line $tE+s\,iE/|E|$, same sign
convention as D9). At $r_c$ and $s>0$, the domains of $w_1$ and $w_2$ leave a hole of width
$1.6000\,s$ at $b_1$. $w_3$ starts at $b_3+1.7236\,s$, a region still covered by $w_2$, and ends
past $1$ by $0.1236\,s$. For $s<0$ the roles change: $w_1,w_2$ overlap by $1.6000|s|$ at $b_1$, and
$w_3$ ends at $1-1.7236|s|$, so the hole is next to $1$. So at $r_c$ the holes on a line of offset
$s$ have width proportional to $|s|$, as K2 says. At $\delta=10^{-3}$ and $|s|\le10^{-4}$ the hole
at $b_1$ is $8.947\cdot10^{-4}=2h(\delta)$, independent of $s$ to 4 digits. That is the regime
of §5.

**What rests on floating point.** Nothing presented as exact. The offsets of §4.3 were
numerical evaluations of exact keys; they are now exact (above). The hole-formula predictions and
§4.5 are floating point and are labelled as such. The "within $0.0023$ of each of $\pm E,\pm\bar E$"
sentence and §4.5 were not re-run.

## 5. Conjectures and assessment

**K3 is false as stated.** For any $c_1>0$, take a line of offset $s<c_1\delta$ with
$|s|\ll\delta$. On it the chord words act as on the chord, with holes $h(\delta)+O(s)$ (§4). The
lattice points of the line are dense in it, with $t$-coordinates in $t_0+\mathbb Z[\varphi]$. The
set of $t$ whose first $N\approx c/\delta$ rotation steps avoid the holes is open and of positive
measure, so it contains lattice points. Their orbits have about $1/\delta$ points on the line.
Computed (start $y=(1-\varphi)^{m-3}y_3+aE+b\varphi E$ on the Fibonacci line $m$, $t\approx0.1$,
exact orbits):

| radius | line $m$ | $s/\delta$ | orbit size | points on its own line |
|---|---|---|---|---|
| level 1 | 15 | 0.0155 | 19 865 (finite) | 116 |
| level 1 | 19 | 0.0023 | 19 867 (finite) | 116 |
| level 2 | 19 | 0.0096 | 316 304 (finite) | 609 |
| level 3 | 21 | 0.0155 | 7 633 848 (finite) | 4 675 |

$\delta\times$(points on the line) is $2.7$, $3.4$, $6.2$, so no bound uniform in $r$ exists. The
starting points have $|\sigma(y)|\approx27/\delta$ to $46/\delta$. A repaired K3 has to restrict
the starting points (for example to $|\sigma x|\le C$, or to the orbit of $0$ and of $-\zeta^2$),
or count only lines that an orbit reaches through a tight window. The heuristic after K4 and item
3 of §6.3 should be read with that repair.

**K1** is consistent with the data but adds little beyond K2: an orbit with points on lines at
offset $\pm\tfrac12\varphi^{-m}$ for infinitely many $m$, with $t$ spread over $[-1,1]$, has the
chord in its closure. **K2** is consistent as an existence statement. The "cascade of runs"
picture is supported, but the per-line counts above show repeated visits, and lines not of the
form $c\varphi^{-m}$ carry comparable populations. **K4** is well supported, more directly by the
points of $O_{r_c}(0)$ on $\mathbb RE$ than by the evidence the note cites. It also looks
provable by a finite exact computation: $w_2$ alone applies on $[b_1,1]$ at $r_c$, and the
remaining words can be read off the chains to the $t>1$ points of that orbit.

**The question of a second mechanism for $-\zeta^2$.** A mechanism on the long segment
$[-\varphi^2E,\varphi^2E]$ cannot prove that $O_{r_c}(-\zeta^2)$ is infinite. That segment lies on
$\mathbb RE$, and by Theorem 4 (already by the coefficient sum mod 5) the orbit of $-\zeta^2$ never
meets $\mathbb RE$. A single-line mechanism would have to sit on a line of non-zero offset $s$ in
the class of $-\zeta^2$. There the chord words have holes of width about $1.6|s|$, so such a
mechanism would need words that bridge those holes. The capped data show no line with a
self-sustaining run. A finite list of mechanisms in the literal sense is therefore unlikely: each
line seems to carry runs of bounded length, of order $\varphi^m$. A list finite **up to
renormalization** is plausible. The populated lines of $-\zeta^2$ are the odd $m$, and at the
levels $m_{\min}=9,13,15,19$, which is period 6 in $m$ per two levels. That points to
self-similarity under $\varepsilon^2=\varphi^{-6}$ for this class. For the class of $0$ the
pattern $m\equiv0,1\pmod 3$ points to $\varepsilon=\varphi^{-3}$.

**The most promising provable next statements**, in order of directness:

1. **Theorem 2 on offset lines.** Each test on the line $tE+s\,iE/|E|$ is a quadratic in $(t,s)$.
   The tight letters give hole ends $b_j\pm h(\delta)+c_js+O(s^2,\delta s)$, with the first-order
   coefficients above (exact values in $\mathbb Q(\varphi)$ to be derived). This would make K2's
   first-order claim and the K3 counterexample theorems. It is a finite exact computation like
   Theorem 2.
2. **Exact renormalization at $r_c$ at the tight points.** At $\delta=0$, for a lattice point
   $y=P+\eta$ near a tight point $P$, the disk test is
   $x:=2\operatorname{Re}((P-c)\bar\eta)+|\eta|^2\le0$ with $x\in\mathbb Z[\varphi]$. It differs
   from the half-plane test $2\operatorname{Re}((P-c)\bar\eta)\le0$ only if $0<x\le|\eta|^2$.
   The norm bound $|x||\sigma x|\ge1$ excludes that when $|\eta|$ is small and $|\eta||\sigma\eta|$
   is below a fixed constant. The half-plane test is invariant under $\eta\mapsto\varepsilon\eta$,
   which preserves $|\eta||\sigma\eta|$. So, as in `sharp-lower-bound-n5.md` Lemma 6.1 but at
   $\delta=0$, the dynamics of such points commute exactly with the zoom while they stay in the
   normalized window. The statement to prove: the first-return map to the tight window at $r_c$
   commutes with the zoom by $\varepsilon$ (by $\varepsilon^2$ on the class of $-\zeta^2$). The
   excursions out of the window would be controlled by the certified four-window closure. With
   that, infinitude of $O_{r_c}(-\zeta^2)$ would follow from one computed renormalization period
   (a chain from a point on line $m$ to its zoomed image on line $m+6$). The same statement at
   $\delta>0$ is (R-core-t), so this is a genuine first step towards (B), not a side result.
3. **K4 by computation**, as above. It is useful for the orbit of $0$ and the chord classes, but
   it says nothing about the 18 chord-free classes.

On the note's own assessment I agree. The forcing argument is dead as posed: the limit system is
infinite (Theorem 1) and arithmetic excludes only exact contact. The chord-parallel offset is a
good coordinate. But the remaining gap, item 3 of §6.3, rests on K3, which needs the repair above.

## 6. What I did not check

The cited refereed results (Theorem A and Lemma 3.1 of `critical-radius-n5.md`; Corollary 2.3,
Lemma 3.0 and Theorem 3.1 of `sharp-lower-bound-n5.md`; the §8 argument; the four-window
certificate; Theorem 5.1 of `boundary-contact.md`) were taken as refereed. I did not re-run §4.5,
the "within $0.0023$" sentence of §4.3, or the margin bound quoted in §6.2. No Lean file was
examined.
