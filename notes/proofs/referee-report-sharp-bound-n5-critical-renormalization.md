# Referee report: `sharp-bound-n5-critical-renormalization.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "The system $GG_5(r_c)$ at the tight point $E$: the long-segment rotation, offset
lines, and a one-sided renormalization by $-\varphi^{-3}$" (`sharp-bound-n5-critical-renormalization.md`,
commit `6f298ea`), and the parts of `sharp-bound-n5-critical-orbits.md` revised with it (K2, K3,
K4, §6.3). Companions consulted: `referee-report-sharp-bound-n5-critical-orbits.md`,
`sharp-bound-n5-invariant.md` (Theorem 7, Lemmas 5, 6) and its report, `sharp-bound-n5-chaining.md`
(Theorem 1, its Remark, Proposition 2) and its report, `sharp-bound-n5-orbit-of-zero.md`,
`sharp-bound-n5-period-two.md` (Proposition 4.5) and its report,
`sharp-lower-bound-limit-system.md` (§6), `sharp-bound-n5-conjugate.md` (Conjecture A),
`critical-radius-n5.md` (Theorem A, Lemma 3.1) and `../engine.md`.

## Summary

The proofs are sound. I checked each one line by line and re-derived every constant. Several
needed small repairs, applied in the note. One conjecture was false as stated.

- **Theorem 1 (K4)** is correct. The long segment carries the rotation by $2\varphi$ of
  $\mathbb R/2\varphi^2\mathbb Z$, and its first return to the chord is $T$. I checked it on
  1 877 exact points, not only at the segment ends. The "exactly" of Corollary 1.1 is right for
  $t$ outside a countable set. The point $t=0$ is in that set: $O_{r_c}(0)\cap\mathbb RE$ is the
  union of **two** rotation orbits, $2\mathbb Z[\varphi]$ and $\varphi+2\mathbb Z[\varphi]$
  (computed). A sentence was added.
- **Theorem 2 and Corollaries 2.1, 2.2** are correct. The exact domains match letter-by-letter
  evaluation on 3 000 random points. The exact hole is at least $H^\ast$ on a grid of 3 320
  points. Two small fixes were made. The last sentence of Corollary 2.2 needs $|s|\le1/10$. Its
  transfer to the free-token setting of the chaining note needs one more check, which I did and
  which the note now states.
- **The sign dispute is settled for the note.** At $r_c$ the gap between $w_1$ and $w_2$ at
  $-\varphi^{-1}$ is a hole of $\tfrac85|s|$ on both sides of the chord. The overlap described in
  the earlier report (its §4) is an error of that report. The note's guess that the overlap
  belongs to the factor words $u_1,u_2$ is also wrong: their gap is a hole of $\tfrac85|s|$ for
  $s<0$ and a second-order hole of about $0.41\,s^2$ for $s>0$. Neither pair overlaps to first
  order. The 40-digit values quoted in the Remark were wrong in the third and fourth digit.
  **Fixed.**
- **Theorem 3** (K3 is false) is correct after two constant fixes ($2.002\to2.003$,
  $4.37\to4.374$). **Proposition 4** and **Corollary 4.1** are correct.
- **Lemma 6** needed its hypothesis stated: the word must apply at $Q$. For the negative units, the
  image point must be a non-lune point too, which holds on the sets of Lemma 5. **Fixed.**
- **Conjecture RI was false as stated, "for every $\delta\ge0$".** There are exact
  counterexamples at $\delta=1/2$ and $\delta=1$, with both points within $0.7$ of $E$. No failure
  occurs at $\delta\le3/10$ on my samples. Propositions 7 and 8 use only $\delta=0$ and small
  $\delta_k$. The conjecture is now stated for $0\le\delta\le\delta_0$. **Fixed.**
- The defect $\varepsilon\delta$ is **nearly, not exactly, sharp**. At $\delta=1/10$ the inclusion
  still holds at defect $0.024$ and fails at $0.025$ ($\varepsilon/10=0.02361$). The same holds at
  $\delta=\varepsilon/10$ with both defects scaled by $\varepsilon$. **Wording fixed.**
- Every computation I re-ran agrees. That covers Table 4.1 (all eight rows, identical counts), the
  exact non-members, Table 4.3, §4.4, §4.5, §4.6 and the witness of Proposition 7. My sample's
  smallest failing pair at $r_c$ has distance $0.7713$, against $0.7753$ in the note.
- **Nothing in the note moves towards finiteness below $r_c$**, except Corollary 2.2: a linear
  cut-off for walks on one line. The verdict that the descent argument is dead in its stated form
  is right (§5).

## 1. Verdicts

| result | verdict |
|---|---|
| Theorem 1 (K4: rotation of the long segment, first return $T$, $w_i$ as return words, strictness) | **correct** |
| Corollary 1.1 (orbit on $\mathbb RE$, "exactly" off a countable set) | **correct**; a remark added that $t=0$ is exceptional (two rotation orbits) |
| Table 2.1, Theorem 2 (exact domains on every offset line, every $r\le r_c$) | **correct** |
| Corollary 2.1 (first-order holes of $T$ and of $M$) | **correct** |
| Corollary 2.2 (exact hole $\ge H^\ast$, runs $\le\min(5.86/\delta,3.28/\lvert s\rvert)$) | **correct after minor fixes**: the last sentence is for $0<\lvert s\rvert\le1/10$; the claim that this is the chaining note's linear gap needs $w_3$ and the positions $t\pm2$ to miss the interval (checked, now stated) |
| Remark §3.2 (sign of the hole) | **wrong in its last sentence and in its digits**; corrected. The earlier report's overlap is an error |
| Theorem 3 (K3 false) | **correct after minor fixes**: $1.961\to1.9613$, $2.002\to2.003$, $4.37\to4.374$ |
| Proposition 4 ($\lvert s\rvert\lvert\sigma y\rvert\ge1/4$) | **correct** |
| Corollary 4.1 | **correct**; "equivalently" replaced by "in particular" (the second form is weaker) |
| Lemma 5 (no lunes below $0.32396$) | **correct** |
| Lemma 6 (cones; $-\varepsilon$ reflects every fixed word's domain) | **correct after a minor fix** to its hypotheses |
| Conjecture RI | **false as stated** (all $\delta\ge0$); **restricted** to $0\le\delta\le\delta_0$, consistent with all data |
| Proposition 7 (infinitude of $O_{r_c}(-\zeta^2)$ given RI at $\delta=0$) | **correct**; witness memberships verified |
| Proposition 8 (monotone limit; conditional) | **correct**; item 2 is an identity of suprema that holds without RI; (i) concerns lattice points (wording fixed) |
| §4 computations | **reproduced** (§4 below); "sharp" overstated (fixed) |
| `sharp-bound-n5-critical-orbits.md`: K2, K3 (false; corrected form), K4, §6.3 | **correct**; §6.3 item 1 now gives the range of the evidence for RI |

## 2. Issues

1. **The sign of the hole at $-\varphi^{-1}$.** The binding letters are $w_1$'s letters 3 and 4
   ($s_j=-\sigma_1,-\sigma_2$) and $w_2$'s letters 2 and 3 ($+\sigma_2,+\sigma_1$). The right end
   of $w_1$ is $-\varphi^{-1}+\min(-\beta s,-\alpha s)$ and the left end of $w_2$ is
   $-\varphi^{-1}+\max(-\alpha s,-\beta s)$, to first order at $\delta=0$. Their difference is
   $(\alpha-\beta)\lvert s\rvert=\tfrac85\lvert s\rvert\ge0$ for both signs. Direct evaluation (30
   digits, letters applied as complex maps) at $s=\pm0.01$: $w_1$ ends at $-0.63550$ and
   $-0.61682$, and $w_2$ starts at $-0.61925$ and $-0.60056$, a hole of $0.016254$ in both cases.
   For $u_1,u_2$, the right end of $u_1$ is $-\varphi^{-1}-\beta s$ (letters 3, 4, both
   $-\sigma_1$). The left end of $u_2$ is $-\varphi^{-1}+\max(-\alpha s,-\beta s)$. The gap is
   $\max(0,-\tfrac85s)$ to first order: $0.016254$ at $s=-0.01$, and $4.08\cdot10^{-5}$
   ($\approx0.41s^2$) at $s=+0.01$. So the earlier report's "for $s<0$ … $w_1,w_2$ overlap by
   $1.6\lvert s\rvert$" is wrong, and the note's attribution of it to $u_1,u_2$ was wrong too. That
   report's statements about $w_3$ (hole at $-\varphi^{-3}$ for $s>0$, at $1$ for $s<0$) are
   right. **Fixed** in the note. I did not edit the earlier report; this paragraph is the
   correction.
2. **Corollary 2.2, last sentence.** "At $r_c$ every chord run off the line $\mathbb RE$ is finite"
   was stated for all $s$. The proof places the interval inside $I_1\cup I_2$ only for
   $\lvert s\rvert,\delta\le1/10$. **Fixed** to $0<\lvert s\rvert\le1/10$.
3. **Corollary 2.2 and the chaining note.** Theorem 1 of the chaining note concerns free tokens:
   any $w_i$, at any position $t'\equiv t\pmod2$, either direction. Corollary 2.2 shows only that
   the $T$-assigned word fails on the interval. For the transfer, $w_3$ at $t$ and every $w_i$ at
   $t\pm2$ must also fail there. The tangent-plane bounds give this. The left end of $w_3$ is at
   least $-\varphi^{-3}-\beta\lvert s\rvert\ge-0.249$, while the interval ends below $-0.401$. The
   left end of $w_1$ is at least $-\sqrt5+\beta s\ge-2.249$ (letter 5), while $t-2\le-2.401$. The
   right ends of $w_2,w_3$ are at most $1+\beta\lvert s\rvert\le1.013$, while $t+2\ge1.165$. A
   check on the 3 320-point grid found no token applying anywhere on the interval. **Sentence
   added**; the chaining and orbit-of-zero notes are now refereed, so "(not refereed)" was updated in three places.
4. **Theorem 3, constants.** $(4/\sqrt5+\alpha/10)=1.961215$ and $1.961215+0.041=2.0022>2.002$.
   **Fixed** to $1.9613$ and $2.003$. The conclusion is unchanged:
   $N\cdot2.003\delta\le0.99\cdot2.003<2$. Also
   $(\sqrt{r_c^2-0.652476}+0.1)^2=4.37383$, not below $4.37$. **Fixed** to $4.374$; the range
   $\delta<0.24$ still works ($r_c^2-4.374=0.244$). The Taylor remainder ($0.6756\delta^2$ per
   end, so at most $2.72\delta^2$ in total) is safely below the $4.1\delta^2$ used.
5. **Lemma 6, hypotheses.** As stated, "$w$ applies at $Q+\eta$ iff $\eta\in C_w$" is false when
   a test outside $J$ fails at $Q$: then $w$ applies at no nearby point. **Fixed:** the word is
   assumed to apply at $Q$, and the other case is stated. For $u=-\varepsilon^m$ the lune
   condition of $u\eta$ is $0<\ell(\eta)<\varepsilon^m\lvert\eta\rvert^2$, which non-lune
   $\eta$ does not exclude. On the sets of Lemma 5 both hold. **Sentence added.**
6. **Conjecture RI for every $\delta\ge0$ is false.** At $\delta=1/2$ ($r^2=(5+2\varphi)/2$, image
   radius $r^2=9/2$) take $y=(1,-2,2,-3)$ and $y'=(6,1,3,3)$, both at distance $0.6775$ from $E$.
   They lie in one finite orbit of 40 points. $O(\Psi y)$ at defect $\varepsilon/2$ is finite with
   21 points and does not contain $\Psi y'$. At $\delta=1$ the pair $(6,-1,4,1)$, $(-1,-1,0,-3)$
   (distances $0.693$, $0.449$) fails the same way. There are 11, 38 and 110 failing starts of 200
   at $\delta=1,2,3$. Both pairs were confirmed by a separate pure-Python search. **Fixed**: RI is
   now stated for $0\le\delta\le\delta_0$, and both counterexamples are recorded. Propositions 7
   and 8 are unaffected.
7. **"The defect $\varepsilon\delta$ is sharp".** On 300 starts at $\delta=1/10$ the inclusion
   holds at defects $0.0237$ and $0.024$ and fails at $0.025$ (20 starts) and $0.030$ (47 starts).
   This is not just because nothing changed between the radii: $O(\Psi y)$ at $0.024$ is smaller
   than at level 1 on 38 of the 300 starts. At $\delta=\varepsilon/10$, defect
   $0.00567\approx0.024\varepsilon$ passes and $0.0059\approx0.025\varepsilon$ fails (28 starts).
   So the threshold lies between $1.017\,\varepsilon\delta$ and $1.059\,\varepsilon\delta$ at both
   scales. **Wording fixed** to "nearly sharp".
8. **Corollary 1.1 at $t=0$.** In $O_{r_c}(0)$ at cap $4\cdot10^6$, 2 271 of the 4 541 points on
   $\mathbb RE$ have $t\in2\mathbb Z[\varphi]$ and 2 270 have $t\in\varphi+2\mathbb Z[\varphi]$.
   This is the rotation part $j\ne0$ of the proof, hitting a lattice $t$; it is allowed by the
   countable exception. The density and the fraction $\varphi^{-1}$ hold for each orbit separately.
   **Remark added.** For $t=1/3$ and $t=2/7$ (exact points $E/3$, $2E/7$, cap $4\cdot10^6$) every
   point found on $\mathbb RE$ lies in $(t+2\mathbb Z[\varphi])E$, as the corollary says.
9. **Proposition 8.** Item 2 is $\sup_k\sup_x\lvert S_k(x)\rvert=\sup_x\sup_k\lvert S_k(x)\rvert$,
   true without RI. RI adds only that $S_\infty$ is an increasing union. Also, (i) is a supremum
   over lattice points at $E$ only, with core radius $\rho_0\varepsilon^{k-k_0}\ge0.3\varepsilon^k$.
   So it implies (R-core-t) at $E$ on lattice points, not (R-core-t) as defined in the
   limit-system note (all points, four windows). **Wording fixed.**
10. **Abstract, computed item 5.** "$\Psi$ maps the orbits of $0$ and of $E$ near $E$ into
    themselves" rests on capped orbits. The hits are exact, but misses beyond the explored part are
    not decided. **Fixed** to "on every tested point".
11. **Not fixed (a research choice).** The proof route proposed for RI in §6 ("a finite
    verification on the first-return germs at $r_c$") has gaps, discussed in §5.

## 3. Proof checks in detail

- **Theorem 1.** Recomputed exactly (Python, $\mathbb Z[\zeta]$ vectors, sign tests in
  $\mathbb Z[\varphi]$). Table 4.2 is reproduced at all six ends. The tight tests are exactly those
  listed, and every other slack is $-2+4\varphi=2\sqrt5$. The translations are
  $(2,0,0,-2)=2\varphi E$ and $(0,-2,2,0)=-2E$. Item 2: $-\varphi^2+2\varphi=\varphi^{-1}$,
  $\varphi^2-2\varphi=-\varphi^{-1}$, $2\varphi-2\varphi^2=-2$. Item 3: the three case
  computations are right. $b^4$ acts as $\zeta^{-4}=\zeta$, the rotation of $B$, and $A^4$ as
  $\zeta^4=\zeta^{-1}$, that of $a$. So $u_1u_3=AAb^4AB\to AABAB$, $u_2u_1=abA^4bb\to ababb$ and
  $u_2u_1u_3\to abaBAB$. The four tests of $b^4$ are one test, because $b$ preserves the
  distance to $+1$. Item 4: $\{2\varphi,2\varphi^2\}$ is a basis of $2\mathbb Z[\varphi]$, and
  $-\varphi^{-1}\equiv\varphi^2$, $1$, $\pm\varphi^2\in X$. Strict convexity gives strictness on
  open segments. Independent check: 1 877 exact points $t=(a+b\varphi)/q$ with
  $q\in\{1,3,7,11,30\}$ and $\lvert b\rvert\le40$. On each, the $u$-word chosen by $M$ applies, and
  every test is strict except at the four sampled breakpoints ($-\varphi^2$ twice, $-\varphi^{-1}$,
  $1$). The image is exactly $(t+\tau)E$. For the 696 chord points among them, the concatenated
  $u$-word of the first return equals $w_i$'s image exactly, and the return word is $T$'s.
- **Corollary 1.1.** The countable exceptional set is right. A $j\ne0$ element of $\Gamma$ puts
  $tE$ on $\mathbb RE$ only for $t=-\operatorname{Im}(c\bar E)/(\lvert E\rvert^2\sin(2\pi j/5))$,
  with $c\in\Lambda$. For $j=0$, $c\in L\cap\mathbb RE=2\mathbb Z[\varphi]E$, because
  $\Lambda=\mathbb Z[\varphi]\oplus\mathbb Z[\varphi]\zeta$ gives
  $2\Lambda\cap\mathbb Z[\varphi]=2\mathbb Z[\varphi]$. The points with $\lvert t\rvert>\varphi^2$
  lie outside both disks ($\operatorname{Re}E/\lvert E\rvert^2=0.809$), and the inclusion
  "$\supseteq$" is item 4.
- **Table 2.1, Theorem 2.** The centres were recomputed as $h_j^{-1}(p_j)$ in $\Lambda$, and every
  vector and every $(t_j,s_j)$ agrees. Exact identities checked by hand:
  $\sigma_1^2=(3-\sqrt5)/8$, $\sigma_2^2=(23+3\sqrt5)/8$,
  $L_j(0)^2=(15+5\sqrt5)/8=((5+\sqrt5)/4)^2$ and $(3+\sqrt5)/8=(\varphi/2)^2$,
  $\sigma_2/L_j(0)=(7-\sqrt5)/2$, $(7-\sqrt5)/(5-\sqrt5)=(15+\sqrt5)/10$, and
  $(\sigma_1/L_j(0))/\lvert E\rvert^2=(\sqrt5-1)/10$. Also $2\lvert E\rvert^2L_j(0)=\sqrt5$ and
  $5$ for the two kinds. The formula agrees with letter-by-letter evaluation (30 digits) at 3 000
  random (word, $t$, $s$, $\delta$) with $\lvert s\rvert,\delta\le0.3$: no mismatch. The six domains
  at $s=\delta=0$ are as stated. $w_1$ is tight at $-\sqrt5$ (letters 4 and 5), an end outside the
  chord.
- **Corollary 2.1.** All four end expansions were re-derived. $H_{-\varphi^{-1}}$ is the maximum of
  the four differences, the largest two being $2\delta/\sqrt5$ and
  $\tfrac85\lvert s\rvert+(\tfrac15+\tfrac1{\sqrt5})\delta$. For $M$, the three holes and the total
  $\tfrac{16}5\lvert s\rvert$ at $r_c$ are right, and so is $\tfrac{31+\sqrt5}{10}\lvert s\rvert$
  for $T$. The threshold is $(\tfrac1{\sqrt5}-\tfrac15)/\tfrac85=(\sqrt5-1)/8$. The §4.7 values
  were reproduced to all digits given ($2.247570\cdot10^{-4}$, $1.600025\cdot10^{-5}$, …).
- **Corollary 2.2.** Concavity of $\sqrt{r_c^2-\delta-(s-s_j)^2}$ in $(s,\delta)$ is right, so the
  tangent-plane bounds hold for all $(s,\delta)$ in the domain. Grid ($\delta,\lvert s\rvert\le1/10$,
  step $1/400$): exact hole$/H^\ast\ge1.0007$. Run bound: with $\lambda=H^\ast/2$, the minimality
  in Lemma 6 of the invariant note gives $F_{m-1}\le1.6188/\lambda$, and
  $F_m-1\le\varphi F_{m-1}\le5.2386/H^\ast$. Then $5.24\sqrt5/2=5.8585$ and $5.24/1.6=3.275$.
- **Theorem 3.** The first-order total, the Taylor remainder ($x_j\le1.386\delta$,
  $Q_j\ge0.9045$, second derivative $\le1/(\sqrt2Q^{3/2})$) and the counting argument are right.
  Only $T^0,\dots,T^{N-1}$ must avoid the holes, so $N$ preimage sets suffice. The density of lattice
  offsets follows because purely imaginary elements of $\mathbb Q(\zeta)$ form the line
  $\mathbb Q(\sqrt5)(\zeta-\zeta^{-1})$. On a grid with $\delta\le1/100$ and
  $\lvert s\rvert\le\delta/10$ the exact total is at most $1.7948\,\delta$.
- **Proposition 4.** $\kappa\in(1-\zeta)$, $N(\kappa)=\lvert\kappa\rvert^2\lvert\sigma\kappa\rvert^2\in5\mathbb Z_{>0}$,
  $\lvert\sigma\kappa\rvert\le2\lvert\sigma y\rvert\lvert\sigma E\rvert$ and
  $\lvert E\rvert^2\lvert\sigma E\rvert^2=(3-\varphi)(2+\varphi)=5$: correct.
- **Corollary 4.1.** Correct as a consequence of Conjecture A. Its use in the corrected K3 of the
  critical-orbits note needs Conjecture A only where it is conjectured.
- **Lemma 5.** Correct; $1/(2\sqrt{4-\varphi})=0.323961$. On 18 270 lattice points
  $E+\eta$ with $\lvert\eta\rvert\le0.6$, the 530 lune points at $Q=E$ all have
  $\lvert\eta\rvert^2\lvert\sigma\eta\rvert\ge0.3762$.
- **Lemma 6.** Correct with the fixes of §2.5. $\ell_j(u\eta)=u\,\ell_j(\eta)$ for real $u$, and
  $\zeta^{m_j}$ preserves $\lvert\cdot\rvert$ and $\lvert\sigma\cdot\rvert$.
- **Proposition 7.** The induction ($\Psi^{jm}x\sim_0x$, distinct since the moduli
  $\varepsilon^{jm}\lvert x-E\rvert$ differ) is right. $m\equiv0\pmod4$ is forced by the class
  4-cycle (verified, §4).
- **Proposition 8.** (1) is right: RI is applied to $(\Psi^jz,\Psi^jx)$, both within $\rho_0$ of
  $E$, and $\varepsilon\delta_{k_0+j}=\delta_{k_0+j+1}$. For (2), see §2.9.
- **Critical-orbits note.** K2's first-order total and K3's corrected form (with
  $c_1=1/(4\max(C,1))$) follow from Corollaries 2.1 and 4.1. K4 is Theorem 1. §6.3 item 3 is right.

## 4. Reproduction

Own programs, independent of the author's: a C library (exact $\mathbb Z[\zeta]$ vectors, disk
tests as exact signs in $\mathbb Z[\varphi]$ with 128-bit integers, hash-set breadth-first
orbits), and Python for the exact checks of §3 and for an independent pure-Python search used to
confirm every exact failure quoted here. The arithmetic was validated against `sharp-bound-n5-conjugate.md`
Table 4.1: $\lvert O(0)\rvert=1\,433$ and $30\,165$ at levels 0 and 1, with $\max\lvert\sigma\rvert=53.7$ and $273.2$. Random
starts are drawn from a **complete** enumeration of the lattice points with $\lvert y-E\rvert\le\rho$ and $\lvert\sigma y\rvert\le M$
(box from the trace bound $\lvert c_k\rvert\le0.8(\lvert z\rvert+\lvert\sigma z\rvert)$; a first, cruder
box missed points and was discarded). Balls and internal guards are double precision and only
select points; every membership decision is exact. A failure is counted only when the orbit that
should contain the point is finite and does not. No `certify` run, no build.

**Table 4.1** (orbit of $E$, cap $4\cdot10^7$, $\max\lvert\sigma\rvert=17\,443.1$): all eight rows
reproduced with identical counts ($166\,077/166\,077$ for $-\varepsilon$, …,
$23\,423/501\,395$ for $-\varphi^{-2}$). Exact non-members among the first misses: $\varepsilon$
8 of 8, $-\varepsilon^2$ 8 of 8, $\pm\varphi^{-1}$ and $\varphi^{-2}$ 2 of 8 each (cap
$3\cdot10^6$), and $-\varphi^{-2}$ 14 of 60 (the note: 33 of 60, presumably with a larger cap).
Radii $1.3$ and $2$ for $-\varepsilon$: $226\,076/237\,055$ and $450\,113/574\,788$, as stated. The
first misses are exact non-members (finite orbits of 21, 25, 584, 604 points without $E$).

**Table 4.3** rows $(0,3,-2,2)$, $(-5,2,-4,-2)$, $(1,0,0,0)$: identical orbit sizes and window
counts, and $S_0\subseteq S_1\subseteq S_2\subseteq S_3$.

**RI at $r_c$** (forward test; a start is conclusive when $O(\Psi y)$ is finite):

| $\rho$, $M$, starts, cap | conclusive | checks | failures |
|---|---|---|---|
| $0.72$, $80$, 400, $3\cdot10^6$ | 288 | 633 716 | 0 |
| $0.70$, $200$, 120, $3\cdot10^6$ | 87 | 149 647 | 0 |
| $0.76$, $30$, 600, $10^6$ | 378 | 88 715 | 0 |
| $0.80$, $30$, 600, $10^6$ | 397 | 95 314 | 4 starts; failing pairs at $\max$ distance $0.7713$, $0.7753$, $0.7829$, $0.7964$ |

The pair at $0.7753$, $y=(-15,3,-11,-8)$ and $y'=(11,-10,13,-5)$, is presumably the note's.
The new one is $y=(-15,-5,-6,-16)$ at $0.7713$ and $y'=(19,-2,13,8)$ at $0.7274$. In both, $y,y'$
share an orbit of 40 points, and $\Psi y'$ is outside the finite 21-point orbit of $\Psi y$.

**RI between radii** ($\rho=0.7$; every orbit finite):

| $y$ at $\to$ $\Psi y$ at | starts ($M$) | checks | failing starts |
|---|---|---|---|
| level 0 → level 1 | 300 (20) | 39 127 | 0 |
| level 1 → level 2 | 300 (20), 300 (60) | 370 676, 436 611 | 0, 0 |
| level 2 → level 3 | 60 (30; orbits up to $11\,123\,374$ points) | 807 298 | 0 |
| level 0 → $\delta'=0.0237$, $0.024$, $0.025$, $0.030$ | 300 (20) | 39 127 | 0, 0, 20, 47 |
| level 1 → $\delta'=0.00567$, $0.0059$ | 300 (20) | 370 676 | 0, 28 |
| $\delta=1/20,\ 1/7,\ 1/5,\ 3/10$ → $\varepsilon\delta$ | 200 each (20) | 61 046, 15 868, 6 191, 3 449 | 0 each |
| $\delta=1/2,\ 1,\ 2,\ 3$ → $\varepsilon\delta$ | 200 each (20) | 1 766, 670, 593, 586 | 2, 11, 38, 110 |
| $r_c^2+\varepsilon/10$ → level 2 | 200 (20) | — | 102 |

**Reverse inclusion** ($\Psi^{-1}(O_{\rm level\,1}(\Psi y)\cap B(E,0.7\varepsilon))\subseteq O_{\delta'}(y)$,
on starts with $O_{\delta'}(y)$ finite): failures on 158 of 200 starts at $\delta'=1/10$, 100 of
148 at $\delta'=0$, and 13 of 66 at $\delta'=-1/10$. Reverse failures also occur on most starts of
every forward run above. The exact $\Psi^{-1}$ failure of §4.5 is reproduced:
$p=(-107,62,-105,-5)$ has a finite orbit of 596 points without $E$, and
$\Psi p=(-453,260,-441,-21)$ is point 277 165 of $O_{r_c}(E)$.

**§4.6.** At caps $2\cdot10^7$ (same $0.6$ guard):
$\Psi(O(-\zeta^2)\cap B(E,0.7))\subseteq O((-2,-2,-1,-2))$ on $49\,714/49\,714$ tested points, and
$\Psi(O(0)\cap B(E,0.7))\subseteq O(0)$ on $52\,938/52\,938$. Classes (own Hermite basis check,
closure modulo $L$): 20 classes; $\Psi$ maps each class into a single class. It fixes the classes
of $0$ and $E$ and cycles $-\zeta^2\to(-2,-2,-1,-2)\to\zeta^2\to(2,2,1,2)\to-\zeta^2$.
**Proposition 7's witness:** in $O_{r_c}(-\zeta^2)$ (cap $4\cdot10^7$),
$x=(-14,-20,3,-30)$ is point 1 012 and $\Psi^4x=(-4558,-6764,1363,-9582)$ is point 31 025 346.
$\Psi x=(-60,-88,17,-126)$ is point 12 166 of $O((-2,-2,-1,-2))$. $\lvert x-E\rvert=0.5452$.

**What rests on floating point.** Nothing presented as exact, after the fixes. The values of
§4.7 and of the Remark are 50- and 40-digit evaluations of exact formulas, labelled as such. Those
of the Remark were misquoted (fixed). The ball radii and the guards are double precision and only
select points. Claims stronger than capped runs support: "$\Psi$ maps the orbits … into
themselves" (fixed to "on every tested point"), and "the sets $S_k$ stabilize", which is seen for
$k\le3$ only and stated as an observation.

## 5. Assessment

**Is RI true?** Not as first stated: it fails at large defect (§2.6). For small $\delta$ it is
well supported. There are no failures within $0.76$ of $E$ at $r_c$, at three level pairs, or at
four non-level defects up to $3/10$. The threshold in the defect also looks self-similar
(§2.7). Two things make the conjecture plausible:
- *The defect scaling.* By Corollary 2.1 the hole widths are, to first order, homogeneous of
  degree one in $(s,\delta)$. $\Psi$ sends offset $s$ to $-\varepsilon s$ and, near $t=1$,
  reflects $t$ about the tight point. Under $s\mapsto-s$ the holes at $-\varphi^{-3}$ and at $1$
  swap. So in the linear model the hole pattern at $(-\varepsilon s,\varepsilon\delta)$ is the
  pattern at $(s,\delta)$ shrunk by $\varepsilon$ and reflected. The one-line identity
  $R_{\varepsilon\delta}=R_\delta^{-1}$ of the chaining note (Proposition 2, refereed) is the same
  fact for the return map.
- *The domain radius.* The failures beyond $0.771$ involve two small periodic islands, an orbit of
  40 points whose $\Psi$-image orbit has 21. So $\rho_0$ seems to be set by where a particular
  island stops being reproduced at the smaller scale. It is not a smooth loss of the scaling.

**Is the proposed proof route sound?** In principle, for one defect at a time, yes. At a level
$r_k$ (a non-norm radius) the group is finite, no lattice point lies on a circle, and the lattice
orbit relation is the orbit relation of the atoms. So RI between two consecutive levels is a finite
exact check, of the same size as a certificate. As written, though, the route has three gaps.
- It speaks of "finitely many first-return germs at $r_c$". At $r_c$ the group is infinite, and
  that the first return to a window has finitely many pieces is not established. The certified
  four-window closures are for radii below $r_c$.
- One finite check cannot cover all $\delta\in(0,\delta_0]$. Each level pair is its own check. A
  statement for all levels needs a parametric argument, and that argument is the renormalization
  being sought.
- $\Psi$ maps a circle of radius $r_c$ to one of radius $\varepsilon r_c$, not to a circle of the
  system. Lemma 6 shows that no word is its own conjugate. So "exhibit a word realizing
  $\Psi g\Psi^{-1}$ on $\Psi(\operatorname{dom}g)$" must be "cover $\Psi(\operatorname{dom}g)$ by
  the domains of several words". The crescents between the two kinds of arcs are a fixed fraction
  of each domain, of relative size about $\rho/(2r)$. They hold lattice points of large internal
  coordinate, which Lemma 5 does not reach.

**What RI gives.** Only lower bounds: more connections, larger orbits, and with one computed
period, infinite orbits at $r_c$ (Proposition 7). That is new for the chord-free classes, but it
points away from (B).

**Does anything here move towards finiteness below $r_c$?** Only Corollary 2.2. It gives a linear
cut-off, $O(1/\max(\delta,\lvert s\rvert))$, for walks confined to one chord-parallel line, and,
with §2.3, for the chaining note's free-token walks. This sharpens the chaining note's
$\delta+h^2$, but it does not touch the two-dimensional gaps (T) and (K) of that note.
- Theorem 3 is negative.
- Corollary 4.1 is conditional on Conjecture A, which is already (B) with a rate.
- Proposition 8 is an identity of suprema (§2.9). Under RI it restates (R-core-t) at $E$, on
  lattice points, as a bound on an increasing limit. It does not reduce it.

**Is the descent argument dead?** In the stated form, yes, and the note's verdict is right. That
form controls the connections of a deep window by those of a coarse one at a larger defect. The
reverse inclusion fails exactly at every defect tested, including $\delta'=-1/10$. So the
connections pulled back from scale $k+1$ are not connections of the coarse system at any radius
near $r_c$, even with larger disks. What survives is the observation that $S_k(x)$ stops growing
after one to three zooms on every computed start. That is (L), which is equivalent to the open
statement itself.

**The most promising provable next statement** is RI on one line, in the linear model, made exact
on lattice points. On a chord-parallel line near $E$, take the chord-word relation at
$(s,\delta)$ with hole ends replaced by their first-order values (Corollary 2.1). Show that $\Psi$
maps it into the relation at $(-\varepsilon s,\varepsilon\delta)$. This follows from the degree-one
homogeneity above and Proposition 2 of the chaining note. Then bound the second-order deviation
(Theorem 2's exact domains differ from the linear ones by $O((\lvert s\rvert+\delta)^2)$) on
lattice points, using Proposition 4 ($\lvert s\rvert\lvert\sigma y\rvert\ge1/4$) to keep points out
of the thin bands. That would be the first exact instance of RI. It is the one-dimensional case of
item (K) of the chaining report.

Two companion steps:
- An exact finite proof of RI from level 0 to level 1 by atoms. A level-0 certificate already
  exists (`../engine.md`). It would show which cells of level 0 map into which cells of level 1:
  the combinatorics a general proof has to capture.
- The question of why $\rho_0\approx0.77$, by following the 40-point island of §4.

## 6. What I did not check

I did not re-run the 1 500-start rows of §4.3 at full size, the 44-start tower of Table 4.3 beyond
the three rows above, the 110/118 count of `wit` (§4.6), or the radius-$0.9$ row. The cited refereed
results (Theorem A, Lemma 3.1 of `critical-radius-n5.md`, Theorem 7 and Lemma 6 of
`sharp-bound-n5-invariant.md`, Theorem 1 and Proposition 2 of `sharp-bound-n5-chaining.md`) were
taken as refereed. No Lean file was examined.
