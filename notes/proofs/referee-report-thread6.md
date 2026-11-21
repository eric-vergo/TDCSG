# Referee report: the analytic radius of a two-disk system

Referee: Claude (independent of the authoring agent)

Subject: `analytic-radius.md` in this directory (Theorem 4.1, Theorem 8.1, Corollaries 8.2–8.3,
Proposition 9.1, §10). Context read: `../overview.md` (definitions of $GG_n(r)$ and $r_c(n)$),
`critical-radius-n5.md` and `boundary-contact.md` (group monotonicity). Every step of §§1, 3, 5, 6, 8 and 9
was re-derived by hand. The computations are listed in §4 below.

## 1. Verdicts

| claim | verdict |
|---|---|
| (1) Theorem 4.1: for $n=5$ and $n\ge7$, invariant real-analytic / harmonic / holomorphic functions on $\Omega_r$ are all constant iff $r>\sec(\pi/n)$; germ version iff $r\ge\sec(\pi/n)$ | **correct** |
| (2) Non-constant holomorphic invariants for $1<r\le r_A$ (fullness, Hausdorff quotient, Riemann surface, non-compactness, Behnke–Stein) | **correct after minor fixes** (issues 2, 3, 4) |
| (3) Necklace geometry; translation $t$ carried across a triple overlap; contracting multiplier; constancy | **correct** |
| (4) $GG_n(r)$ on $[1,\sec(\pi/n))$ has order $n^2(2n-1)!/2$, the same group throughout | **correct**, including the parity distinction for even $n$. The add-on "first *changes* at $r_A$" is proved only for the orbit structure, not for the abstract group (issue 1) |
| (5) On $(r_A,r_c)$: $GG_n(r)$ finite while the hull has dense orbits | **correct after minor fixes** (issue 5): the hull statement is proved for all $r>r_A$; finiteness on the interval is definitional once $r_c$ is the least infinite radius and group monotonicity is cited; what is only computed is $r_A<r_c$ for $n\ne5$ |
| Theorem 8.1, Corollary 8.2, motion counts $2n^2-2n+1$ / $2n^2-3n+3$, exact values, asymptotics, table | **correct** |

No fatal error and no gap in the proofs of the main theorem was found.

## 2. Checks of the points raised in the brief

**(a) Definition.** Definition 3.1 is unambiguous: $f\in\mathcal C(\Omega_r)$, $f\circ A=f$ on the open
$D_1$, $f\circ B=f$ on the open $D_2$. The threshold statement is exactly what is proved: for open disks,
non-constant invariants exist iff $1<r\le\sec(\pi/n)$, so the endpoint belongs to the non-constant
side. This is right because Lemma 1.1 is a strict inequality: at $r=\sec(\pi/n)$ the three open disks
centred at $-1,1,A(1)$ have empty intersection (their common closure point is the circumcentre, which
lies on all three boundary circles). For germs along closed disks the endpoint switches sides, which
Lemma 3.3(2) handles correctly. The exclusions are justified: $n=5$ needs its own multiplier
$\mu=1+\zeta^2$ and works with equality $\operatorname{mec}\le\sec(\pi/5)<r$ (verified); $n=6$ fails
because $2\tan(\pi/6)=\sec(\pi/6)$ exactly (verified) and, decisively, because $T$ is a lattice; for
$n\in\{2,3,4,6\}$ the $\Gamma$-invariant trigonometric polynomials of §11 item 6 are non-constant
real-analytic invariants for every $r$ (correct up to the $2\pi$ normalisation, issue 6). The
holomorphic threshold for these $n$ is honestly left open.

**(b) Geometry of the threshold.** The upper lens corner is $i\sqrt{r^2-1}$, at distance $r$ from $-1$ and
at angle $\arccos(1/r)$ seen from $-1$. For $r\le\sqrt2$ (which covers every $\sec(\pi/n)$, $n\ge5$)
the corners are the angular extremes of $L$ seen from $-1$, so $L$ subtends $2\arccos(1/r)$ and
consecutive rotated lenses $A^kL$, $A^{k+1}L$ first touch when $\arccos(1/r)=\pi/n$, at the point where
$A$ carries the upper corner $i\tan(\pi/n)$ to the lower corner $-i\tan(\pi/n)$. Independently,
$L\cap AL=D_1\cap D_2\cap AD_2$ and the circumradius of the isosceles triangle $(-1,1,A(1))$ (legs 2,
apex angle $2\pi/n$, acute for $n\ge5$) is $\sec(\pi/n)$. Both descriptions agree. Lemma 1.2 (minimum
over $k$ attained exactly at $k\equiv\pm1$; obtuse cases $\ge\sqrt2$) is correct. Checked to 50 digits
for $n=5,6,7,8,12,13,30$; the triple intersection is empty at $r_A-10^{-6}$ and at $r_A$, non-empty at
$r_A+10^{-6}$, for $n=5,7,8,12$.

**(c) Lower direction.**
- Lemma 5.1 and the domain table are correct; the three-block exclusion is right. (Issue 2: say that
  merging blocks only enlarges the domain, since $\mathrm{Dom}_P$ is a union over all words.)
- Lemma 5.2 (fullness) is correct: each two-block domain is an atom disjoint from the other three
  atoms, each of those intersections being a triple of disks with $\operatorname{mec}\ge\sec(\pi/n)\ge r$;
  for the coincident motions (even $n$) the domain is two such isolated atoms. Coincidences were
  verified exactly in $\mathbb Z[\zeta_n]$ (§4).
- Lemma 5.3 (Hausdorff) is correct: the relation is open, and the graph is closed because there are
  finitely many motions and each domain is a union of components. This is exactly where fullness is
  needed, and it is used correctly. Fixed points are not a problem: the centres $\pm1$ have isotropy
  $C_n$, the chart is $(z\mp1)^n$, and $Q$ is a genuine Riemann surface (the orbifold structure is
  forgotten, which is harmless for holomorphic functions). Second countability is not stated
  (issue 3).
- At $r=r_A$ (open disks) the corner points lie on $\partial\Omega_r$, not in $\Omega_r$, so nothing in
  Lemmas 5.2–5.5 changes. Verified.
- Lemma 5.5 (non-compactness) is correct; the inequalities $r<2\cos(\pi/n)$ and $r\cos(\pi/n)\le1$ were
  checked for $5\le n\le60$.
- Behnke–Stein (1949): every connected non-compact Riemann surface is Stein, in particular carries a
  non-constant holomorphic function. Applied correctly. The Forster section number is unconfirmed
  (issue 4). Real part gives a non-constant harmonic, hence real-analytic, invariant (open mapping).

**(d) Upper direction.** Every step is legitimate.
- $A^{-1}B(z)=z+t$ was verified; $U_{21}=D_2\cap(D_1-t)=B^{-1}L=\mathrm{Dom}_P(A^{-1}B)$; for $z\in U_{21}$,
  $Bz=A(z+t)\in D_1$, so each application of a symmetry is to a point of the right open disk.
- $U_{11}\cap U_{21}$ is the triple intersection with centres $-1,1,1-2\zeta$, non-empty iff
  $r>\sec(\pi/n)$; $U_{11}\cup U_{21}$ is a connected open subset of $\Omega_r\cap(\Omega_r-t)$.
- The "classic gap" (intermediate translates leaving the domain) does not occur. Rule 4 of Step 2 is
  stated with the correct hypothesis $\operatorname{mec}(0,s_1,s_1+s_2)<r$, which makes the set $W$
  non-empty and places $z+s_1$ in $D_1\cap(D_1-s_2)$ for $z\in W$; the identity theorem is then applied
  on the convex set $D_1\cap(D_1-s_1-s_2)$. Step 3 uses rule 4 once per step with a triangle whose mec
  was verified to be $<r$, and Lemma 6.1 needs only a sequence $s_k\to0$ acting on the fixed ball
  $D(-1,r/2)$, not a dense set. The Steinitz argument in Theorem 8.1 also keeps all partial sums
  within $4\varepsilon$, so every application of rule 4 is legitimate.
- Lemma 6.1 is correct: the directional derivative vanishes on the ball, hence everywhere; invariance
  under $A$ rotates the direction; two independent directions give $df=0$.
- Vectors with $|s|\ge2r$ belong to $S$ vacuously (empty domain); this never matters because rule 4's
  hypothesis bounds $|s_1|$ and $|s_1+s_2|$ by $2r$.

**(e) Group order.** Proposition 9.1 is correct, including $r=1$ (closed disks tangent at 0, lens orbit
of 0 with $2n-1$ points). The faithfulness argument, primitivity, the 3-cycle commutator, Jordan's
theorem and the Goursat step are all sound. Parity matters exactly as the note says: for odd $n$ the
group is $C_n\times C_n\times A_{2n-1}$; for even $n$ the $n$-cycles are odd and the group is the
index-2 subgroup $\{(i,j,\pi):\operatorname{sgn}\pi=(-1)^{i+j}\}$ of $C_n\times C_n\times S_{2n-1}$. It
has the same order but is **not** isomorphic to $C_n\times C_n\times A_{2n-1}$ (its centre has order
$n^2/2$, not $n^2$); the note does not claim it is. Geometric computation (§4) gives exactly
$n^2(2n-1)!/2$ for $n=3,\dots,8$ at $r=1$ and at the midpoint of $[1,\text{threshold})$, and for
$n=5,\dots,8$ at $r_A-10^{-3}$. For $n=5$ this is $4\,536\,000=25\cdot9!/2$, matching the paper's
$C_5\times C_5\times A_9$.

**(f) Claim (5).** See issue 5. The title and status are not overclaimed, apart from issue 1.

**(g) Classical theorems.**
- Behnke–Stein: every non-compact connected Riemann surface is Stein (Behnke–Stein 1949). The statement
  is correct. The location in Forster's *Lectures on Riemann Surfaces* is unconfirmed: the published
  table of contents puts Runge approximation in §25 and Mittag-Leffler/Weierstrass in §26, so "§26"
  may be off by one.
- Jordan: a primitive permutation group containing a 3-cycle contains the alternating group. Correct.
  The citation "Wielandt, Thm 13.3" is the referee's recollection too, but was not confirmed;
  Dixon–Mortimer, *Permutation Groups*, Theorem 3.3A is an alternative.
- Steinitz lemma in the plane: the Euclidean planar Steinitz constant is $\sqrt5/2$ (Banaszczyk), and
  the constant is at most $d$ in $\mathbb R^d$ (Grinberg–Sevast'yanov). So "at most 2" is correct.
  Not confirmed from a source in this session.

## 3. Numbered issues

1. **§0 item 3, Proposition 9.1 closing paragraph, §10.1(iv) and §9 last sentence: "$r_A$ is the first
   radius above 1 at which $GG_n(r)$ changes".** Severity: **minor** (overstatement).
   What is proved is that the orbit structure changes: below $r_A$ all orbits have $1$, $n$ or $2n-1$
   points; above it some have $\ge3n-2$. This does not by itself show that the abstract group changes,
   since a group of order $n^2(2n-1)!/2$ can have orbits of size $3n-2$ in principle (for example
   $3n-2=22$ divides $|G|$ for $n=8$). Also "does not depend on $r$" means "constant up to
   isomorphism", since the maps change with $r$. *Repair:* say "the orbit structure of $GG_n(r)$
   changes first at $r_A$" and "is isomorphic, for all $r\in[1,r_A)$, to"; or prove that the order
   changes. §4 item 5 gives floating-point evidence that it does for $n=5,7,8$ just above $r_A$.
   A proof could exhibit an orbit whose size does not divide $n^2(2n-1)!/2$, or exhibit an induced
   permutation group that is larger than it.
2. **Lemma 5.1(2).** Severity: **minor**. $\mathrm{Dom}_P(\gamma)$ is a union over *all* words, including
   unreduced ones and ones with blocks $A^{\pm n}$. The reduction is valid because cancelling adjacent
   letters, merging adjacent powers and deleting blocks that act as the identity only enlarge the
   domain. *Repair:* add that sentence.
3. **Lemma 5.4.** Severity: **minor**. A Riemann surface must be Hausdorff and second countable (or
   Radó's theorem must be invoked). *Repair:* add that $\pi$ is open, so $Q$ is second countable; and
   one line on why the transition maps between the charts $(z-p)^{m}$ are holomorphic (away from the
   cone points they are motions; at a cone point the chart is the only one).
4. **§5 proof step 3 and §11 item 4: the Behnke–Stein citation.** Severity: **minor**
   (reference). The section number is "from memory, to be checked" and is likely wrong (see (g)).
   *Repair:* cite Behnke–Stein, *Math. Ann.* 120 (1949), and the correct Forster section. An
   alternative that avoids it: once the remark "Q is homeomorphic to an open disk" is proved, which
   follows from van Kampen applied to the two cones glued along the simply connected lens, uniformisation
   makes $Q$ biholomorphic to the disk or the plane, and the coordinate is a non-constant function.
5. **Corollary 8.3, §0 item 6, §11 item 7: the interval $(r_A,r_c)$.** Severity: **minor**.
   The corollary needs $GG_n(r)$ finite for *every* $r\in(r_A,r_c)$. That follows from the overview's
   definition of $r_c$ as the least infinite radius together with group monotonicity
   (`boundary-contact.md`, Theorem 3.4), which the note does not cite. What then depends on the
   table is only $r_A<r_c$. That in turn needs the *true* $r_c$, while the table records where infinite
   orbits were found. For $n=5$, $r_A<r_c$ is proved (`critical-radius-n5.md`, Theorem B, finiteness up
   to $r_\ast\approx2.14$, modulo its computation). For the other $n$ it is numerical evidence, and the
   large-$n$ table question in `../overview.md` is relevant. *Repair:* cite monotonicity, and state the
   dependence as "$r_A<r_c^{\text{true}}$: proved for $n=5$, computed for the others".
6. **§11 item 6: the trigonometric polynomial.** Severity: **minor**. With $\omega$ in the dual lattice
   in the usual sense ($\langle\omega,\tau\rangle\in\mathbb Z$), the argument must be
   $2\pi\,\mathrm{Re}(\overline{\zeta^k\omega}(z+1))$, and $\omega\ne0$ is needed. Non-constancy
   holds because the frequencies $\pm\zeta^k\omega$ are non-zero and the coefficients do not cancel.
   *Repair:* fix the normalisation and say $\omega\ne0$.
7. **Theorem 8.1(1): "$\Gamma^{\rm an}(r)=\Gamma(r)$" at $r=r_A$.** Severity: **minor**. $\Gamma(r)$ is
   defined through $GG_n(r)$ with closed disks, while Proposition 9.1 excludes $r=r_A$. The equality
   is plausible (new motions at $r_A$ live only on the corner points, so they have no interior), but it
   is not argued. *Repair:* restrict the equality to $r<r_A$ or add the argument.
8. **Lemma 3.3(2).** Severity: **cosmetic**. "Non-constant" for a germ should mean non-constant near
   $\bar D_1\cup\bar D_2$, since $U$ may be disconnected. Restrict to $\Omega_{r+\varepsilon}$.
9. **Proposition 9.1(1).** Severity: **cosmetic**. The $A$-orbit of $-1$ is a fixed point, not an
   $n$-point orbit. Primitivity: spell out that the second point of $\Delta$ is fixed by $\sigma_a$ or by
   $\sigma_b$.
10. **Theorem 8.1 step 4.** Severity: **cosmetic**. Consecutive partial sums give triangles of diameter
    at most $4\varepsilon$, not $8\varepsilon$; the conclusion is unaffected.
11. **Status paragraph.** Severity: **cosmetic**. "Refereed by their author, not by an independent
    reader" should be updated to cite this report.

## 4. Computational checks

Scripts are in the session scratchpad (`ref6/geo.py`, `coinc.py`, `group.py`, `above.py`); they are
not part of the repository.

1. **Lemma 1.2 and the corners** (mpmath, 50 digits): $\min_k\operatorname{mec}(-1,1,A^k(1))=\sec(\pi/n)$
   with equality exactly for $k=\pm1$, and $\operatorname{mec}(-1,1,1-2\zeta)=\sec(\pi/n)$, for
   $n=5,6,7,8,12,13,30$. The corner has angle exactly $\pi/n$ from $-1$, and $A(i\tan\frac\pi n)=-i\tan\frac\pi n$,
   for $n=5,7,8,12$.
2. **Inequalities** for $5\le n\le60$: $\sec<2\cos$, $\sec<g$, and $2\tan<\sec$ for $n\ge7$; equality
   $2\tan(\pi/6)=\sec(\pi/6)$; pentagon identity $4\sin(\pi/5)/(2\cos(\pi/10))=\sec(\pi/5)$; $|1+\zeta_5^2|=1/\varphi$.
3. **Exact values** (sympy): $r_A^2$ for $n=5,8,10,12$ simplify to the tabulated forms exactly;
   $\sqrt5-1$ and $\sqrt6-\sqrt2$ agree with $\sec$ to 160 digits; the $n=7$ substitution gives
   $-(y^3-24y^2+80y-64)$, vanishing at $\sec^2(\pi/7)$; $8c^3+4c^2-4c-1$ is the minimal polynomial of
   $\cos(2\pi/7)$.
4. **Motion counts, exactly in $\mathbb Z[\zeta_n]/\Phi_n$**: the motions $\mathrm{id},A^k,B^j,B^jA^k,A^kB^j$
   number 41, 57, 85, 107, 173, 255 for $n=5,6,7,8,10,12$, matching $2n^2-2n+1$ (odd) and
   $2n^2-3n+3$ (even); the coincidences are exactly the predicted $n-2$ pairs
   $B^jA^{n/2-j}=A^{j+n/2}B^{-j}$.
5. **Group orders** (geometric orbits of $a,b$ in double precision on generic sample points; group on
   the union of one or two lens orbits and one pure orbit for each disk; order by sympy): exactly
   $n^2(2n-1)!/2$ for $n=3,\dots,8$ at $r=1$ and at the midpoint of the interval, and for
   $n=5,6,7,8$ at $r_A-10^{-3}$. (At $r=\text{threshold}-10^{-3}$ for $n=3,4$ the first sample points
   fell into lens orbits, so no pure orbit was sampled. Re-run with pure sample points near the centres,
   both give the predicted orders 540 and 40320.)
   **Above $r_A$** (same method; points of $L\cap A(L)$ plus pure orbits): the group induced on the
   sample orbits, a quotient of $GG_n(r)$, has orbit sizes $\{5,25,40\}$ and order $\approx3.05\cdot10^{35}$
   at $n=5$, $r=r_A+0.01$; sizes $\{5,40\}$ and order $39\,375\,000\,000$ at $n=5$, $r=r_A+0.05$; and orders
   far above $n^2(2n-1)!/2$ for $n=7$ ($r_A+0.005$) and $n=8$ ($r_A+0.005$). So at these radii the
   abstract group really is larger, which supports the intended reading of issue 1. This is
   floating-point evidence on generic points, not a proof.
6. **Tables**: $r_A$, $g$, $(g-1)/(r_A-1)$ and $(r_c-1)/(r_A-1)$ in §10.2 and the ratios 7.50, 7.91,
   7.98 at $n=20,50,100$ all reproduce to the stated digits (with $r_c$ taken from the note's own table;
   $r_c(5)=\sqrt{3+\varphi}=2.1489611$ agrees with `critical-radius-n5.md`).

## 5. What I did not check

- The paper's Appendix A values of $r_c(n)$ against the paper itself (no PDF text extraction was
  available); only the consistency of $r_c(5)$ with the closed form.
- The hull-closure computation of §10.3 items 1 and 3 (translation moduli, orbit sizes 13–132 above
  $r_A$) was not re-run.
- The exact theorem and section numbers in Forster, Wielandt and the Steinitz literature (see (g)).
- §11 item 5 (Laplace eigenfunctions), labelled conjecture, and §12 (interpretation), which makes no
  new claims.
- A proof that the abstract isomorphism type of $GG_n(r)$ changes at $r_A$ for general $n$ (issue 1);
  only floating-point evidence for $n=5,7,8$.
