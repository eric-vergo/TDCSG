# Referee report: the regularity scale of a two-disk system

Referee: Claude (independent of the authoring agent)

Subject: `regularity-scale.md` in this directory. I also read `analytic-radius.md` (AR) §§3–8,
`referee-report-thread6.md`, and the cited statements of `boundary-contact.md` (Lemma 2.3,
Proposition 3.3, Theorem 3.4) and `critical-radius-n5.md` (Theorems A and B). I re-derived by hand every
proof in §§1–5, §7(c) and §8. The computations are listed in §3 below. I did not run `lake build` or
the repository engine, and I made no git operations.

## 1. Verdicts

| claim | verdict |
|---|---|
| (1) Rigidity is an up-set in $r$ on $(r_A,\infty)$ for every class closed under restriction (Lemma 2.1, Proposition 2.2) | **correct** (issue 8 is cosmetic) |
| (2) Classes satisfying (C1)–(C4), in particular quasi-analytic Denjoy–Carleman classes $\supseteq C^\omega$, have $r_{\mathcal C}=r_A=\sec(\pi/n)$; $C\{1\}$ has threshold 1 (Remark 3.4) | **correct after minor fixes** (issues 2, 6) |
| (3) Bump classes: $\max(2,d_n)\le r_{\mathcal C}\le R_{\rm erg}(n)$; necklace island on $(r_A,d_n)$, central islands for $r<2$, ergodicity above $R_{\rm erg}$ | **correct after minor fixes** (issues 1, 4, 5) |
| (4) Dichotomy (Theorem 4.5) on $(r_A,\max(2,d_n))$ | **correct**. The status wording around it overclaims slightly (issue 3) |
| (5) $n=5$: bump thresholds in $[2\sqrt{4-\sqrt5},\,3.662]$ | **correct**. I reproduced the exact certificate independently (§3.1) |
| (6) $Q_r$ Hausdorff for $r\le r_A$, not Hausdorff on $(r_A,r_c)$ or above $R_{\rm erg}$; a.e. separation below $r_c$ | **correct** (issue 9 is cosmetic). The open case can probably be closed (issue 11) |
| (7) For $n\ge63$, $H^{(1)}_r$ has dense orbits for every $r>r_A$ | **correct after a minor fix** (issue 7) |
| (8) Classical inputs (Denjoy–Carleman, Steinitz with the Grinberg–Sevast'yanov constant, Behnke–Stein via AR) | **correctly stated and correctly used** |

I found no fatal error and no gap in any proof. The issues are overstatements in the wording and small
omissions.

## 2. Issues

**1. "Every class of functions is rigid" is false as stated.** *Location:* Theorem 5.2 (last line),
Corollary 5.3, §5.3 item 1, §9 ("for every class"). *Severity:* minor.
- Definition 1.1(1) allows any vector space of real functions, for example all real functions, or all
  Borel functions taken pointwise.
- By Lemma 1.2(1), the indicator of a single $P_r$-orbit is invariant. It is non-constant and Borel,
  since orbits are countable. So such classes are never rigid, at any $r$.
- What Theorem 5.2 proves is rigidity for every class contained in $C^0$, and for every class of
  measurable functions taken modulo null sets.
- *Repair:* say exactly that. Definition 1.1 could also require that a class lies in $C^0$ or in $L^0$
  modulo null sets.

**2. The headline of item 1 contradicts Remark 3.4.** *Location:* Statement, item 1 ("Every class with
unique continuation has threshold $r_A$"); §0 item 3 is fine. *Severity:* minor.
- $C\{1\}$ has unique continuation, but Remark 3.4 shows that its threshold is 1.
- *Repair:* "Every motion-invariant class of continuous functions with unique continuation that
  contains $C^\omega$ has threshold $r_A$."

**3. Status overclaims for $n\ne5$, and the value of $r_c(5)$ is overstated.** *Location:* Status
("items 1–3 in full"), Statement item 3, the sentence "$r_c(n)$ is therefore not a rigidity threshold
for any regularity class", and Statement item 4 ("$r_c=2.149$"). *Severity:* minor.
- Item 3 says the scale jumps "to a radius above $r_c$", so that the thresholds "do not fill the gap
  $(r_A,r_c)$". This needs $r_c(n)\le\max(2,d_n)$.
- That inequality is proved only for $n=5$. For other $n$ it rests on the paper's table, as §9
  ("Computed only") itself admits.
- "Not a threshold for any regularity class" is proved only for the classes treated here (Denjoy–Carleman,
  the bump classes, and (C1)–(C4) classes). It is not proved for arbitrary classes.
- For $n=5$, `critical-radius-n5.md` proves only $2.1138\lesssim r_c(5)\le\sqrt{3+\varphi}=2.1490$
  (Theorem B is itself proved modulo a computation). The note's arguments use only the upper bound,
  so they are unaffected.
- *Repair:* mark the "$r_c<\max(2,d_n)$" part of item 3 [computed] for $n\ne5$. Restrict "any regularity
  class" to the classes treated. Write $r_c(5)\le2.149$.
- *Suggestion:* for $n\ge7$, a proof that $GG_n(r)$ is infinite for $r>2$ would remove the dependence on
  the table. Numerically, the orbit of $-1$ is infinite at $r=2.001$ for $n=7,8,10,12$ (§3.2).

**4. "Equivalently almost everywhere" is asserted without proof, but it is needed.** *Location:*
Definition 1.1(2); used in Theorem 5.2 ("ergodic for Lebesgue measure") and in §6
($r_{L^\infty}=r_{\rm erg}$). *Severity:* minor.
- Ergodicity in the usual sense concerns sets that are invariant almost everywhere. The note's
  definition requires a representative that is invariant everywhere.
- The two notions agree, by a short argument. $P_r$ is countably generated by isometries. If $f$ is
  a.e. invariant, let $E$ be the null set of points where some word $w$ with $z\in{\rm Dom}(w)$ has
  $f(wz)\ne f(z)$. Its saturation is a countable union of isometric images of $E$, hence null. Setting
  $f=0$ on the saturation gives an everywhere-invariant representative.
- *Repair:* add this argument, and drop "the converse is not used".

**5. The chain of thresholds in §6 uses $C^0\subset L^\infty$, which is false.** *Location:* §6,
$r_{C^0}\le r_{L^\infty}$. *Severity:* minor.
- Continuous functions on the open set $\Omega_r$ need not be bounded.
- *Repair:* $\arctan f$ is a bounded continuous invariant, and it is non-constant iff $f$ is. A
  continuous function that is a.e. constant is constant.

**6. Constants must be in the class.** *Location:* Theorem 3.1 step 5, and Lemma 4.1 (extension by 0).
*Severity:* minor.
- Step 5 applies (C3) to $f-c$. Lemma 4.1 uses $0\in\mathcal C$, which is automatic in a vector space,
  and locality.
- *Repair:* add "contains the constants" to Theorem 3.1. All the examples satisfy it.

**7. The definition of $H^{(1)}_r$ is wrong for $r\le r_A$.** *Location:* §7(c). *Severity:* minor.
- Read literally, "$\tau_t$ on $U_{11}\cup U_{21}$" adds $\tau_t$ on $U_{11}$ even for $r\le r_A$.
  There $\tau_t$ on $U_{11}$ is not in $P_r$, so the claim "$H^{(1)}_r=P_r$ for $r\le r_A$" fails.
- *Repair:* define the new germ as $\tau_t$ extended from $U_{21}$ to the union of the atoms it meets
  (one round of continuation). For $r>r_A$ this is $U_{11}\cup U_{21}$ (AR §6 Step 1). For $r\le r_A$
  it is $U_{21}$, because $U_{11}\cap U_{21}=\emptyset$.
- The rest checks: the domains contain $D(-1,r-|t|)$; Steinitz needs $D(-1,r-5|t|)$; and
  $20\sin(\pi/n)<\sec(\pi/n)$ holds exactly from $n=63$ on. I checked
  $20\sin(\pi/62)=1.0130>\sec(\pi/62)=1.0013$ and $20\sin(\pi/63)=0.9969$.

**8. Strict versus non-strict inequality in Lemma 2.1.** *Location:* Lemma 2.1, step 6 ("at most
$K$"). *Severity:* cosmetic.
- The statement claims $w(z)$ lies in the open disk $D(\pm1,K)$, but the iteration only gives a
  distance $\le K$.
- *Repair:* run the iteration with some $K_1\in(r_A,K)$.

**9. Proposition 8.3: $g$ cannot be both compactly supported in $[0,\varepsilon^2)$ and strictly
decreasing there.** *Severity:* cosmetic.
- *Repair:* take $g$ strictly decreasing on $[0,a]$ and zero beyond, for some $a<\varepsilon^2$. A point
  $w$ in an island disk with $|w-y_i|^2\ge a$ then gets $f(w)=0<f(z)$.

**10. Small points.** *Severity:* cosmetic.
- Theorem 4.5 does not need $\mathcal C\supseteq C^\omega$. Theorem 3.1 needs only (C1)–(C3), and the
  bump construction needs only log-convexity and $M_0=1$.
- §0 item 8 says "$r\le r_A$", but Proposition 8.2 says "$1<r\le r_A$". The case $r\le1$ is trivially
  Hausdorff.
- §7(a): the central island exists on $(0,2)$, not only on $(r_A,2)$.
- Proposition 4.2: openness of ${\rm Reg}_r$ needs one more line. The motions mapping an island disk to
  itself are rotations about its centre by powers of $\zeta$, so nearby orbits are finite, of size at
  most $Nn$.
- Proposition 3.2(2): for the existence of compactly supported functions, cite Hörmander, *ALPDO I*,
  Theorem 1.3.8, alongside Rudin.
- "The two-disk system detects quasi-analyticity" is fair for Denjoy–Carleman classes, because there
  quasi-analyticity, unique continuation from open sets and the absence of bump functions coincide.
  What the system really detects is the existence of compactly supported invariant-friendly bumps
  versus unique continuation. A sentence saying so would prevent over-reading.

**11. Proposition 8.2 probably extends to every $r>r_A$.** *Severity:* information; a suggested
strengthening that I have not checked in every detail.
- In step 3, allow countably many motions $\delta$. Then $F_\gamma$ is countable, and a connected open
  planar set minus a countable set is still connected. So ${\rm Dom}_P(\gamma)\supseteq C\setminus
  F_\gamma$ again.
- Step 4 then gives, for all $z$ outside a countable set, orbits containing
  $z+(S_H\cap D(0,\varepsilon))$, which are dense in $D(z,\varepsilon)$.
- Take two such points $z,w$ with $|z-w|<\varepsilon/2$ and $w\notin O_r(z)$. Every saturated open set
  containing $w$ meets the orbit of $z$, so it contains $z$. Hence $Q_r$ is not Hausdorff.
- This would settle open question 4 of §9 (non-Hausdorff on all of $(r_A,\infty)$), and it would make
  the finiteness hypothesis in part 2 unnecessary.

**12. More islands, consistent with the note.** *Severity:* information.
- For $n=12$, the orbit of the lens corner $q$ stays finite (64 points, away from the circles) on
  roughly $(d_{12},1.556)$. The necklace island therefore survives past $d_{12}$ in a new form. This is
  harmless, because $\max(2,d_{12})=2$.
- For $n=5$, the orbit of the centre $-1$ is $\{-1,B^k(-1)\}$ (5 points) for $2<r<|t|=2.351$. This is a
  third island family, again below $d_5$.

**13. The §5.3 script is not in the repository.** *Severity:* minor (reproducibility).
- I re-ran the computation independently (§3.1) and it matches.
- *Repair:* commit a script, for example one like the one described below.

## 3. Computational checks

All computations are in the scratchpad (`refq2/`), run with `python3 -I`.

1. **The $n=5$ certificate, exact.** (`n5exact.py`.) This is a breadth-first search (BFS) of the
   open-disk orbit of $-1$ at $r'^2=(-56+30\sqrt5)/2$. Points are integer 4-vectors in
   $\mathbb Z[\zeta_5]$. Squared moduli are $(P+Q\sqrt5)/2$, and signs are decided by integer
   comparison.
   - The BFS reached exactly 60 001 points.
   - $s=576+110\zeta+288\zeta^2+466\zeta^3$ occurs as a difference of two orbit points (2163 pairs).
     Counting all rotations $\zeta^js$, there are 10 809 pairs.
   - $|s|^2=(573140-256316\sqrt5)/2$. Exact rational checks give $0<|s|<0.0119$; in fact
     $|s|=0.011814\ldots$.
   - Also exactly: $r'<2.354$ and $r'>|t|$.
   - The bound: $2.354+(\sqrt5-1)+6(0.0119)=3.66147<3.662$. With the exact values it is $3.66089$.
2. **Floating-point upper bounds** (`genorbit.py`; exact coordinates modulo the cyclotomic
   polynomial, floating-point disk tests). Starting from $r'=2.001$, I found smallest differences
   $0.00415, 0.00773, 0.01005, 0.01031$. These give rigidity for $r>3.136, 3.130, 3.113, 3.098$ for
   $n=7,8,10,12$. The note's (weaker) values 3.171, 3.200, 3.154, 3.160 are consistent with these. None
   of these values is certified.
3. **Islands** (`islands.py`; floating point, tolerance $10^{-9}$), for $n=5,7,8,12$:
   - The orbit of $q=i\tan(\pi/n)$ has exactly $2n-2$ points at $r=r_A+10^{-4}$, at the midpoint, and at
     $d_n-10^{-4}$. The margin to the circles is $\min(r-r_A,d_n-r)$.
   - Perturbed points have orbits of size at most $(2n-2)n$ (sizes 40, 84, 56, 132), staying within
     $3\times10^{-5}$ of the necklace when the perturbation is small. So the neighbourhood is genuinely
     invariant and permuted by isometries.
   - At $d_n+10^{-4}$ the orbit of $q$ exceeds the cap of 20 000 points, except for $n=12$ (issue 12).
   - Central islands: $n$ points at $r=1.5,1.9,1.99$. At $r=2.01$ the central island dies for
     $n\ge7$; for $n=5$ it survives (issue 12).
   - Table values of $r_A$, $d_n$ and $R_{\rm erg}$, the closed forms $2\sqrt{4-\sqrt5}$,
     $\sqrt{12-6\sqrt2}$, $2\sqrt3-2$, and the asymptotic coefficient $17\pi^2/2$ all check.
4. **Searching for islands above the conjectured threshold.** I took 300 random points per radius, with
   an orbit cap of 3000:
   - $n=5$ at $r=2.7,3,3.5,4,13$;
   - $n=8$ at $r=2.05,2.5,3,3.3$;
   - $n=7$ at $r=2.07,2.5$.

   No finite orbit was found. This is consistent with Theorem 5.2 and with Conjecture 6.1. It is not
   evidence for anything stronger.

## 4. Hand checks of the points raised in the brief

**(a) What "invariant" means.**
- Lemma 1.2 is correct. Invariance under the open-disk definition means exactly being constant on
  $P_r$-orbits, and these are the orbits of the piecewise group with open disks.
- Closed-disk orbits satisfy $O_r\subseteq O^{\rm cl}_r\subseteq O_{r'}$ for $r'>r$. The two coincide
  when the closed orbit avoids the circles.
- Islands are built from open-disk orbits that avoid the circles, so they are islands for both
  conventions.
- For measurable classes, rigidity is read as "a.e. constant". The islands use $\mathbf 1_U$, with $U$
  and its complement both of positive measure. Theorem 5.2 handles a.e. constancy correctly by
  mollification, given issue 4.

**(b) The islands.**
- The algebra of Theorem 4.3 is right: $\cos3x/\cos x=2\cos2x-1$, so $d_n^2=r_A^2+|t|^2$. The minimum
  over non-corner points is attained at $\pm3\pi/n$.
- Theorem 4.4 is right for every $r<2$. Every point of $\{A^kz\}$ is at distance more than $r$ from
  $+1$. The centre itself is a fixed island point.
- This is consistent with $r_c(5)\le2.149$, which exceeds 2 (islands are present below $r_c$ anyway).
  It is also consistent with $r_c(n)<2$ for $n\ge7$: finite orbits persist beyond $r_c$ while the group
  is already infinite. That is not a contradiction.
- Lemma 4.1 is right. The linear parts of all words are powers of $\zeta$, so a $\zeta$-invariant
  $\psi$ is carried to itself, including on stabilisers.

**(c) Ergodicity.** The mechanism is genuine.
- Lemma 5.1 shadows the chain of the centre $-1$ at a smaller radius $r'$. This gives true translations
  by $\pm\zeta^js$ on a fixed disk $D(-1,\rho-2|s|)$.
- The Steinitz lemma keeps paths of these translations within $4|s|$ of a segment. So orbits contain
  $(z+\mathbb Z[\zeta]s)\cap D(-1,K')$: they are dense, and ergodicity on the disk follows by
  mollification.
- The descent lemma then spreads constancy to all of $\Omega_r$.
- The constant: $K'+4|t|=r-\max(2,|t|)$ with $K'>\sec(\pi/n)$ gives exactly $R_{\rm erg}$. I verified
  the domains of $A^{-1}B=\tau_t$ and $B^{-1}A=\tau_{-t}$, and the conjugations, explicitly.
- I found no gap.

**(d) The up-set claim.**
- The descent inequality is right: $F(\rho)<\rho$ iff $\rho>\sec(\pi/n)$, and $\rho-F(\rho)$ is
  increasing. Equally spaced points on the circle give an angle of at most $\pi/n$ to the other centre.
- Proposition 2.2 is right for every class closed under restriction, pointwise or a.e.

**(e)** See §3.1.

**(f) The dichotomy.**
- The hypotheses are: $M$ log-convex, $M_0=1$, Roumieu local class, Rudin normalisation.
- Log-convexity is used for products ($M_jM_{k-j}\le M_k$) and for the Denjoy–Carleman equivalence.
  The rotation estimate ($2^k$) and the directional-derivative estimate ($(\sqrt2)^k$) are correct.
- See issue 10 for the superfluous $C^\omega$ hypothesis, and issue 3 for the status wording.

**(g)** See issues 7, 9 and 11.
- Proposition 8.2 part 2 is correct as written. The graph-closure argument with finitely many motions
  gives fullness up to finite sets, and AR's hull construction then forces infinite orbits.

## 5. What I did not check

- AR's results (Theorems 4.1 and 8.1, Lemma 5.3). I relied on them as refereed and re-read only the
  parts used.
- `critical-radius-n5.md` Theorems A and B, and the paper's $r_c$ table.
- The classical theorems against their sources. Denjoy–Carleman (Rudin, *Real and Complex Analysis*,
  Theorem 19.11; Hörmander 1.3.8) and Grinberg–Sevast'yanov (1980; Steinitz constant at most $d$ for
  any norm on $\mathbb R^d$) match my knowledge, but I did not look them up.
- The §6 evidence (random scans, coverage tests). I ran only the spot checks of §3.4.
- Issue 11 is a sketch, not a full proof.
- I did not use the compiled engine.
