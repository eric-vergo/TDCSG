# The critical radius of $GG_{12}$

Authors: Eric Vergo, Claude

**Statement.** Let $\zeta=e^{2\pi i/12}$, $\varepsilon=2-\sqrt3$ and $r_c=\sqrt{40-22\sqrt3}\approx1.376547$, the paper's conjectured critical radius. The target theorem is:

> (A) $GG_{12}(r)$ is infinite for every $r\ge r_c$; and (B) $GG_{12}(r)$ is finite for every $r<r_c$.

**Status.**
- **(A) is proved, in writing and in Lean.** The Lean theorems are `TDCSG.CriticalRadius.mem_orbit_pStar_twelve_pow`, `infinite_orbit_pStar_twelve` and `infinite_GG_twelve` (statements in `TDCSG/CriticalRadius/Statements.lean`; the closure data of Appendix A are checked by kernel reduction, `decide +kernel`, in `TDCSG/CriticalRadius/Twelve.lean`), which give `1 ≤ criticalRadius 12 ≤ √(40 - 22√3)`. The written proof follows. The infinite orbit is the orbit of the lattice point $p^\ast=(2-\sqrt3)(1-2i)=-2\zeta+4\zeta^2-3\zeta^3$, which lies exactly on $\partial D_1$ when $r=r_c$. For every $r\ge r_c$ that orbit contains $p^\ast+2\varepsilon^{k+2}V$ for all $k\ge0$, where $V=\zeta^5+\zeta^6$ (Theorem A, §2.4).
- The method is the one of `critical-radius-n8.md`, which transfers. A chord through $p^\ast$ carries 30 partial isometries, each realized by an explicit group word of length at most 28. The family is closed under rescaling by $\varepsilon$ about $p^\ast$. Every disk test, domain endpoint and composition was checked in exact arithmetic, and the data are listed in Appendix A.
- **(B) is open.** It is proved only for $r\le r_\ast$ by an exact finite computation (§3) together with the refereed group monotonicity.
  - The refereed certificate is at $\delta=1/20$ ($r\approx1.358264$). Like every certified range, it is proved modulo the computation and has no Lean counterpart.
  - This note's own exact certificates reach $\delta_\ast=1/50$ ($r_\ast^2=r_c^2-\delta_\ast$, $r_\ast\approx1.369263$, Table 3.1); those beyond $\delta=1/20$ are not refereed.
  - The deepest certified range is recorded in [`../certificates.md`](../certificates.md): the repository's Lean engine generates and independently checks a certificate at $\delta=1/180$, giving finiteness for $r\le1.374528$, an open window of length $r_c-r\approx0.002019$, modulo that computation. An exact interval of validity extends it slightly, to $r^2<\rho_1$ with $r_c^2-\rho_1\approx0.0055543$; a closure at $\delta=1/250$ exists but is not checked ([`../relative-certificates.md`](../relative-certificates.md) §§7, 8, 10).
- **Refereeing.** This note was independently refereed; see `referee-report-critical-radius-n8-n12.md` in this directory. The referee reproduced Part A fully and exactly, including end-to-end word checks for $k\le6$ with the true generators, and reproduced the Theorem B certificates up to $\delta=1/20$ in floating point with matching invariants.
- **Is $r_c$ the exact threshold?** What is proved is $r_\ast\le\inf\{r:GG_{12}(r)\text{ infinite}\}\le r_c$. The closed form is confirmed as an upper bound, and as the exact radius at which this mechanism switches on. Whether a smaller radius already gives an infinite orbit is not excluded; the evidence (§5) says no.

"Verified exactly" means as in the $n=8$ note: every equality and sign is decided in $\mathbb Q(\sqrt3)$, or in $\mathbb Q(\sqrt3)(\sqrt{H_1},\sqrt{H_2})$, by rational arithmetic. Floats only search.

---

## 1. Setting and notation

- $\zeta=e^{i\pi/6}$, with $\zeta^4=\zeta^2-1$. Then $\sqrt3=\zeta+\zeta^{-1}=2\zeta-\zeta^3$ and $i=\zeta^3$.
- $D_1,D_2$ are the closed disks of radius $r$ centred at $\mp1$. The maps $A,B,a,b$ are as in the $n=8$ note, with rotation angle $2\pi/12$ clockwise.
- Inverses are written as capitals ($\mathtt A=a^{-1}$, $\mathtt B=b^{-1}$), and words are read left to right.
- $\varepsilon=2-\sqrt3=\tan(\pi/12)=|1-\zeta|^2$. The fundamental unit of $\mathbb Z[\sqrt3]$ is $2+\sqrt3=\varepsilon^{-1}$.
- **Arithmetic.** For $w=\sum x_j\zeta^j$: $\operatorname{Re}w=x_0+\tfrac{x_2}2+\tfrac{x_1}2\sqrt3$ and $\operatorname{Im}w=\tfrac{x_1}2+x_3+\tfrac{x_2}2\sqrt3$. Signs in $\mathbb Q(\sqrt3)$ and its quadratic extensions are decided as for $n=8$.
- Lemma 1.1 (convexity) and Definition 1.2 (valid word) of the $n=8$ note apply verbatim. A word valid at $r_0$ on a segment stays valid, with the same action, at every $r\ge r_0$.

---

## 2. Part A: an infinite orbit for every $r\ge r_c$

### 2.1 The critical point

Put $p^\ast=(2-\sqrt3)(1-2i)=-2\zeta+4\zeta^2-3\zeta^3\approx0.267949-0.535898\,i$.

Checked exactly:
- $p^\ast+1=(3-\sqrt3)-i(4-2\sqrt3)$, so $|p^\ast+1|^2=(12-6\sqrt3)+(28-16\sqrt3)=40-22\sqrt3=r_c^2$. So $p^\ast\in\partial D_1$ exactly at $r=r_c$.
- Also $p^\ast+1=\varepsilon\,(3+\sqrt3-2i)$, with $|3+\sqrt3-2i|^2=16+6\sqrt3$. This exhibits the factorization $r_c^2=\varepsilon^2(16+6\sqrt3)=2\varepsilon\,(7-2\sqrt3)$, where $7-2\sqrt3$ has norm $37$.
- $|p^\ast-1|^2=32-18\sqrt3\approx0.823<r_c^2$. So $p^\ast\in\operatorname{int}D_2$.

### 2.2 The critical chord

Let $V=\zeta^5+\zeta^6=-1-\zeta+\zeta^3$. It has direction $165^\circ$ and $|V|^2=2+\sqrt3$. Let $\ell=\{p^\ast+uV:u\in\mathbb R\}$, the line through $p^\ast$ in the direction of $V$. The coordinate $u$ is used throughout, so lattice points of $\ell$ have $u\in\mathbb Q(\sqrt3)$; Euclidean length along $\ell$ is $|V|\,u\approx1.93185\,u$.

- $\ell\cap D_2$ is $u\in[\tfrac{15}2-\tfrac92\sqrt3-\sqrt{H},\ \tfrac{15}2-\tfrac92\sqrt3+\sqrt H]\approx[-0.905586,\,0.317129]$, with $H=145-\tfrac{167}2\sqrt3$. A second radical, $\sqrt{143-\tfrac{165}2\sqrt3}$, appears in some domain endpoints of Appendix A: it comes from the disk constraint of a letter acting on an intermediate image of $\ell$ (equivalently, from the end of the $D_2$-chord transported along a word). Comparisons between endpoints carrying the two different radicals use the two-radical sign test.
- $\ell\cap D_1$ starts at $p^\ast$ ($u=0$) and runs to $u\approx1.41155$.
- The proof works in the symmetric window $W=[-w,w]$ with $w=\tfrac{15}2-\tfrac92\sqrt3+\sqrt H\approx0.317129$, the upper end of the $D_2$-chord. A word's domain $D_w$ is the set of $u\in W$ at which the word is valid, starts and ends in $D_2$, and maps into $W$. It is a closed interval with exactly computable endpoints of the form $\alpha\pm\sqrt d$, $\alpha,d\in\mathbb Q(\sqrt3)$.

**How the chord was found (not used in the proof).**
- At $r=r_c$, an exact orbit of $0$ with $2\cdot10^6$ points meets $\ell$ in 1815 points.
- These fill two intervals with uniform density: from the far end of the $D_2$-chord up to $u\approx0.339$, and from $u\approx1.072$ up to the far end of the $D_1$-chord.
- The lines through $p^\ast$ in the directions $15^\circ$, $75^\circ$ and $105^\circ$ carry similar but sparser structures.
- The vertical line through $p^\ast$, along which the orbit approaches $p^\ast$ (Remark 3 below), is *not* the right line: it carries only 156 orbit points, with large gaps.

### 2.3 The certificate

Lemma 2.1 and Corollary 2.2 of the $n=8$ note hold verbatim on this $\ell$, with the similarity $u\mapsto\varepsilon u$ centred at $p^\ast$. That is the lattice map $z\mapsto p^\ast+\varepsilon(z-p^\ast)$.

**Lemma 2.3 (exact check).** At $r=r_c$, the family of 30 words in Appendix A satisfies:
1. each word acts on $\ell$ as $u\mapsto\pm u+c$ with the listed $c\in\mathbb Z[\sqrt3]$;
2. it is valid at both endpoints of the listed interval, hence on all of it (the listed intervals are the maximal domains, but only validity is used);
3. for each family member $f$, the interval $\varepsilon D_f$ is covered by the listed consecutive pieces. On each piece the listed sequence of at most 4 family members is defined, with every intermediate image interval inside the next domain, and composes exactly to $u\mapsto\varepsilon f(u/\varepsilon)$.

There are 37 pieces and 147 composition steps. (The Lean data `TDCSG.Twelve.pieces` also include the 8 redundant one-point pieces described next: 45 pieces and 179 steps, each one-point piece having a sequence of length 4.) Appendix A also lists 8 redundant one-point pieces (in rows 3, 5, 8, 21, 22, 24, 26 and 28), each consisting only of the right endpoint of $\varepsilon D_f$, which the previous piece already reaches. They are valid, play no role, and are ignored in the counts and in Lemma 2.3.

*Proof.* Exact computation: `python3 -I verify_closure_n.py 12 cl12_S28d.pkl`, in the scratch directory `t4_8/`. Output:
```
all 30 maps: exact domains agree with float; words valid at both endpoints
closure verified exactly; 147 composition steps
```
$\square$

**How the family was found** (floating-point search, not part of the proof).
1. All reduced words of length at most 28 were enumerated, with interval pruning, giving 1 687 maps of $W$ into $W$.
2. Maps whose domain lies inside the domain of another map with the same action were removed, leaving 106.
3. The closure was grown from the seed by depth-first search over compositions of at most 4 maps, discarding members whose rescaled version could not be found. Three rounds of pruning gave the closed 30-member family.
4. Earlier attempts failed in instructive ways: with words of length at most 20, with the full chord as the window, or with the vertical line through $p^\ast$, the searches made found no closed family.

The **seed** is $\mathtt{babbaa}$, acting as $u\mapsto(14-8\sqrt3)-u$ on $[-0.155409,\,0.143594]\ni0$. Note $14-8\sqrt3=2\varepsilon^2$.

### 2.4 Theorem A

**Theorem A.** For every $r\ge r_c=\sqrt{40-22\sqrt3}$, the orbit of $p^\ast=-2\zeta+4\zeta^2-3\zeta^3$ under $GG_{12}(r)$ contains the pairwise distinct points
$$p^\ast+2\varepsilon^{k+2}\,V,\qquad V=\zeta^5+\zeta^6,\quad k=0,1,2,\dots$$
Hence $GG_{12}(r)$ is infinite.

*Proof.*
1. At $r_c$ this is Lemma 2.3 with the renormalization lemma ($n=8$ note, Lemma 2.1 and Corollary 2.2), applied to the seed: $\mathtt{babbaa}(0)=2\varepsilon^2\neq0$.
2. For $r>r_c$ no monotonicity theorem is needed: every letter rotates because its point lies in the closed disk at $r_c$, the disks only grow, so all validity conditions persist with the same action, and the closure condition does not involve $r$. $\square$

**Remarks.**
1. *Sanity check (not part of the proof).* An exact search of the orbit of $p^\ast$ at $r_c$, capped at $3\cdot10^6$ points, contains $p^\ast+2\varepsilon^{k+2}V$ for $k=0,\dots,4$.
   - At $r^2=r_c^2-1/100$ the same orbit is finite, with 3 894 points.
   - At $r^2=r_c^2-1/1000$ it is finite, with 321 120 points.
2. *Where $r_c$ enters.* The seed does not need $p^\ast\in\partial D_1$: its six disk tests at $p^\ast$ have squared distances $32-18\sqrt3,\ 22-12\sqrt3,\ 12-6\sqrt3,\ 12-6\sqrt3,\ 22-12\sqrt3,\ 22-12\sqrt3$ (checked exactly), so $\mathtt{babbaa}$ is valid at $u=0$ for every $r\ge\sqrt{12-6\sqrt3}\approx1.2680$. What needs $r=r_c$ is the family as a whole: the domains of Appendix A are maximal at $r_c$, and at many of their endpoints a letter's disk test holds with equality at $r_c$. For $r<r_c$ those domains shrink and Lemma 2.3 as stated fails.
3. *Approach along the vertical.* In the exact threshold sweep of the orbit of $0$ (`notes/engine.md`), the jumps of the $\times4$ type occur at $r^2=1003-578\sqrt3$, $17409-10050\sqrt3$ and $256723-148218\sqrt3$. These are exactly $|q+1|^2$ for $q=p^\ast+i\varepsilon^3,\ p^\ast+i\varepsilon^4,\ p^\ast+i\varepsilon^5$, checked exactly. So the orbit of $0$ approaches $p^\ast$ vertically, at ratio $\varepsilon$ per period. This is consistent with the limit point and the scale of the paper's "analogous construction" for $n=12$; that the paper's path of segments is this approach is not shown.
4. *What changed from $n=8$.*
   - The chord direction is not the direction of approach.
   - The window must be restricted to the part of the chord with dense orbits. On the full chord, maps defined on periodic islands have no rescaled counterpart.
   - Library words up to length 28 are needed, against 12 for $n=8$. This is because $\varepsilon=0.268$ contracts more strongly: rescaled maps need about $3.7\times$ longer words, against $2.4\times$ for $n=8$.

### 2.5 Relation to the paper's construction

- The paper's limit point is identified as the lattice point $p^\ast$, on $\partial D_1$ exactly at $r_c$. The scale is $2-\sqrt3$, as the paper says.
- The construction stays inside the disks: every letter is checked to act inside its closed disk.
- The paper's figure (Figure 5d) could not be inspected for this note, so the geometry of its path of segments is neither confirmed nor refuted beyond the limit point and the scale.

---

## 3. Part B: finiteness for $r\le r_\ast$

The facts used are the same as for $n=8$: orbit and group monotonicity (`boundary-contact.md` Theorems 3.1 and 3.4), and the cut-set certificate (Theorem 3.1 of the $n=8$ note, whose proof is independent of $n$; the bound "at most $n$ maps per pair of cells" becomes $12$).

**Computation.** The programs are the same as for $n=8$: `cut/cut.py` and `cut/verify.py`, with $n=12$. Here $r^2=(40-\delta)-22\sqrt3$.
- Real and imaginary parts of elements of $\mathbb Q(\zeta_{12})$ lie in $\mathbb Q(\sqrt3)$, so all ordering decisions are exact signs in $\mathbb Q(\sqrt3)(\sqrt{H_1},\sqrt{H_2})$.
- Tangency of a carrying circle with $\partial D_p$ would need $|c-p|^2=4\rho$, which is impossible when $4\delta\notin\mathbb Z$.
- `verify.py` re-checks (C1)–(C4) with no float decisions.

**Table 3.1.** Cut set $K(r)$ at $r^2=r_c^2-\delta$; columns as in the $n=8$ note. Every listed certificate was checked by the exact verifier, with (C4) failures $0$ and no tangency.

| $\delta$ | $r$ | $r_c-r$ | circles | maximal arcs | (C2) image arcs | (C4) endpoints | max $\lvert\sigma(c)\rvert$ | exact verification |
|---|---|---|---|---|---|---|---|---|
| $1/3$ | 1.2496 | 0.1269 | 282 | 556 | 1 252 | 368 | 13.5 | **valid** |
| $1/5$ | 1.3019 | 0.0747 | 2 324 | 6 016 | 13 492 | 1 000 | 37.1 | **valid** |
| $1/10$ | 1.3397 | 0.0368 | 2 360 | 6 192 | 13 924 | 1 032 | 37.5 | **valid** |
| $1/20$ | 1.3583 | 0.0183 | 37 180 | 114 380 | 257 092 | 3 928 | 137.5 | **valid** |
| $1/30$ | 1.3644 | 0.0122 | 37 840 | 157 924 | 355 012 | 4 804 | 137.5 | **valid** (not yet refereed) |
| $1/40$ | 1.3674 | 0.0091 | 38 016 | 162 960 | 366 628 | 6 420 | 137.5 | **valid** (not yet refereed) |
| $1/50$ | 1.3693 | 0.0073 | 83 674 | 335 412 | 754 420 | 9 444 | 266.8 | **valid** (not yet refereed) |
| $1/60$ | 1.3705 | 0.0061 | not finished: stopped by me at more than $3.2\cdot10^5$ circles and 2.9 GB, to stay within the resource budget | | | | | — |

The "(C2) image arcs" column counts the four images of the two boundary circles about their own centres, which the repository engine's checker skips; its counts are 4 lower. The engine closes $\delta=1/60$ and deeper radii, down to $\delta=1/180$ ([`../certificates.md`](../certificates.md) §5).

**Growth of the computation.** Closure time / peak memory / exact-verification time: $\delta=1/30$: 107 s / 0.8 GB / 586 s; $1/40$: 147 s / 1.0 GB / 602 s; $1/50$: 307 s / 1.9 GB / 1263 s. The growth is in steps: almost none from $1/20$ to $1/40$ (circles $\times1.02$), then a factor $2.2$ by $1/50$ and more than $8$ by $1/60$. These steps are consistent with one per level of §4 (a factor $2+\sqrt3$ in $\delta$).

**Theorem B (proved modulo the computation of Table 3.1).** $GG_{12}(r)$ is finite for every $r\le r_\ast$, where $r_\ast^2=40-22\sqrt3-\delta_\ast$ and $\delta_\ast=1/50$, i.e. $r_\ast\approx1.369263$. The open window left by this table, $(r_\ast,r_c)$, has length about $0.0073$; the engine certificates of `../certificates.md` narrow it to about $0.002019$. The certificates at $\delta\le1/30$ were produced after the referee's pass and are not yet refereed; the refereed certificate is $\delta=1/20$ ($r\approx1.358264$).

*Proof.* The certificate at $\delta_\ast$ satisfies (C1)–(C4), checked exactly. Apply the certificate theorem and group monotonicity. $\square$

The internal extent grows like $\delta^{-1}$ on average. As for $n=8$, no single computation reaches $r_c$; the stopping point here is a resource limit of this implementation, and the repository engine reaches $\delta=1/180$.

---

## 4. Renormalization data

1. **Scale unit.** $\varepsilon=2-\sqrt3$, the inverse of the fundamental unit; $\bar\varepsilon=2+\sqrt3$ is the internal expansion.
2. **Critical point.** $p^\ast=(2-\sqrt3)(1-2i)\in\partial D_1(r_c)$.
3. **Chord and window.** $\ell=p^\ast+\mathbb RV$ with $V=\zeta^5+\zeta^6$, and $W=[-w,w]$.
4. **Exact one-dimensional renormalization at $r_c$.** The family of Appendix A is closed under $u\mapsto\varepsilon u$ (Lemma 2.3).
5. **Thresholds.** For the orbit of $0$, `notes/engine.md` gives gap ratios $3.6828, 3.7189, 3.7286\to2+\sqrt3$ for one jump type and $3.7159, 3.7277, 3.7308$ for the other. The $\times4$ jumps occur where $p^\ast+i\varepsilon^m$ enters $D_1$ (§2.4, Remark 3).
6. **Asymptotic only off criticality**, for the curvature reason recorded for $n=5$ and $n=8$.

**Levels.** Put $q_m=p^\ast+i\varepsilon^m$ and $\delta_m=r_c^2-|q_m+1|^2>0$, so that $q_m$ enters $D_1$ exactly at $r^2=r_c^2-\delta_m$ (for $m=3,4,5$ these are the thresholds of Remark 3 of §2.4); $\delta_m/\delta_{m+1}\to2+\sqrt3$. A radius with $r^2=r_c^2-\delta$ is at **level $m$** if $\delta\in[\delta_{m+1},\delta_m)$. The **type at scale $\varepsilon^m$** is defined as in the $n=8$ note (§4): the circles of $K(r)$ meeting the disk of radius $C\varepsilon^m$ about $p^\ast$, rescaled by $\varepsilon^{-m}$ about $p^\ast$, with the cyclic order of arc endpoints inside that disk.

**Conjecture R₁₂.** There are $C$ and $m_0$ such that for every $m\ge m_0$ the type at scale $\varepsilon^{m+1}$ at level $m+1$ is the image under $z\mapsto p^\ast+\varepsilon(z-p^\ast)$ of the type at scale $\varepsilon^m$ at level $m$, and likewise at the symmetric images of $p^\ast$.

As for $n=8$, Conjecture R₁₂ alone does not imply (B). It would reduce (B) to three further statements: a fixed type of $K(r)$ away from the critical neighbourhoods at each level, persistence of (C1)–(C4) from level to level, and control of the curvature mismatch; plus one certificate at level $m_0$.

**Conjecture F₁₂.** $GG_{12}(r)$ is finite for every $r<r_c$; equivalently, $r_c$ is exactly the infimum of the radii with infinite group.

---

## 5. Is the closed form exactly the critical radius?

- **Proved:** $\inf\{r:GG_{12}(r)\text{ infinite}\}\in[r_\ast,r_c]$, modulo the computation of §3; and with $r_\ast^2=r_c^2-1/180$ modulo the certificate of `../certificates.md`. The upper bound is proved in Lean.
- **Not proved:** that no point has an infinite orbit in $(r_\ast,r_c)$.
- **Evidence:**
  - the exact threshold sweep of the orbit of $0$ accumulates only at $r_c$, with gap ratios tending to $2+\sqrt3$;
  - the orbit of $0$ is finite at $\delta=9.34\cdot10^{-4}$, with 1 945 733 points (`notes/engine.md`);
  - the orbit of $p^\ast$ is finite at $\delta=10^{-3}$, with 321 120 points;
  - every cut-set closure attempted here at $\delta\ge1/50$ terminated, and in the repository engine every one attempted at $\delta\ge1/180$.

---

## 6. Status and gaps

Verdicts are those of the referee report (`referee-report-critical-radius-n8-n12.md`) unless marked otherwise.

| claim | status |
|---|---|
| Lemma 2.3 (30-word family closed under $\varepsilon$) | proved by exact computation; refereed: correct, independently reproduced in full in exact arithmetic |
| Theorem A: $GG_{12}(r)$ infinite for all $r\ge r_c$, explicit orbit of $p^\ast$ | **proved**; refereed: correct. **Proved in Lean** (`TDCSG.CriticalRadius.infinite_GG_twelve`) |
| Theorem B at $\delta=1/20$ | **proved modulo the computation of §3**, all decisions exact; refereed: correct as stated, certificate reproduced in floating point with matching invariants |
| Theorem B at $\delta_\ast=1/50$ | **proved modulo the computation of §3**, all decisions exact; **not yet refereed** |
| Finiteness for $r^2\le r_c^2-1/180$ | **proved modulo the engine certificate** of `../certificates.md` (generator and independent checker; not refereed) |
| finite for $r_\ast<r<r_c$ (Conjecture F₁₂); $r_c$ is exactly the infimum | **open** |
| Conjecture R₁₂ | conjecture; it would reduce (B) to further statements (§4), not prove it |

**Caveats.**
1. *Independent checks.* Part A has been re-implemented and re-checked exactly by the referee. The exact cut-set verifier behind Theorem B is single-author: the referee did not read or run it, and its own reproduction used floating-point comparisons. The certificates at $\delta\le1/30$ were produced after the referee's pass; the repository engine, a separate exact implementation with its own checker, reproduces them with the same invariants (`../certificates.md` §§4–5).
2. The window $W$ and the restriction "start and end in $D_2$" only shrink domains, so they cannot create false validity.
3. Theorem A is about the orbit of $p^\ast$. Whether the orbit of $0$ is infinite at $r_c$ is not proved here.

**Not checked by the referee:** the author's programs; the numerical evidence of §5 and of §2.4 Remark 1 (orbit counts); the orbit-of-0 and threshold-sweep observations; the "how the family was found" description; `notes/engine.md` and companion notes; the paper's figures; §7.

---

## 7. Lean formalization: what is done and what is not

As for $n=8$ (§7 of `critical-radius-n8.md`), with $\mathbb Z[\zeta_{12}]$ modulo $\zeta^4=\zeta^2-1$ and sign decisions in $\mathbb Q(\sqrt3)$.

**Formalized:** Part A in full. The 30 words of Appendix A and the closure data (`TDCSG.Twelve.family`, `TDCSG.Twelve.pieces`) are checked by `decide +kernel` (`realizeOK_family`, `closureOK_family` in `TDCSG/CriticalRadius/Twelve.lean`), with `TDCSG.Twelve.isRoot_zeta` for the actual $e^{2\pi i/12}$; Theorem A is `TDCSG.CriticalRadius.mem_orbit_pStar_twelve_pow`, `infinite_orbit_pStar_twelve` and `infinite_GG_twelve`, hence `criticalRadius_twelve_le`.

**Not formalized:** the certificate theorem (a refereed written result with no Lean counterpart; the library has no certificate predicate), the link between a certificate file and the hypotheses (C1)–(C4) (the engine's checker is a tested program, not a kernel-checked proof), hence Theorem B, which is proved modulo the computation; and Part B in full.

---

## Appendix A. The renormalization family for $n=12$

Coordinates: $u$ on $p^\ast+uV$, with $V=\zeta^5+\zeta^6$, and window $W=[-w,w]$ as in §2.2. Sign $+$ means $u\mapsto u+c$; sign $-$ means $u\mapsto c-u$. In the exact endpoints, $a/2\sqrt3$ means $\tfrac a2\sqrt3$. Domains are the maximal intervals in $W$ on which the word is valid, starts and ends in $D_2$, and maps into $W$.

| # | word | sign | shift c | domain (decimal) | domain endpoints (exact) |
|---|---|---|---|---|---|
| 1 | `bbabAbaBABabABAbaBabABABAbaB` | + | −38 + 22√3 | [-0.278653, -0.248711] | 89/2 − 51/2√3 − √(145 − 167/2√3) ; 24 − 14√3 |
| 2 | `bbABabaBAbabABabaBAbABaBAB` | + | −38 + 22√3 | [-0.248711, -0.145861] | 24 − 14√3 ; 77/2 − 45/2√3 + √(143 − 165/2√3) |
| 3 | `bbABabaBAbabABababaB` | − | 38 − 22√3 | [-0.248711, -0.052559] | 24 − 14√3 ; 19 − 11√3 |
| 4 | `bbABabaBAbababbababa` | + | −24 + 14√3 | [-0.248711, -0.052559] | 24 − 14√3 ; 19 − 11√3 |
| 5 | `bbabABAbaBabAbaBABabABABAbaB` | + | −38 + 22√3 | [-0.207968, -0.105118] | 47/2 − 27/2√3 − √(143 − 165/2√3) ; 38 − 22√3 |
| 6 | `babbaa` | − | 14 − 8√3 | [-0.155409, 0.143594] | 9/2 − 5/2√3 − √(143 − 165/2√3) ; 14 − 8√3 |
| 7 | `bABababaBAbababABABAbaBABABa` | + | 28 − 16√3 | [-0.143594, 0.000000] | −14 + 8√3 ; 0 |
| 8 | `bbABaBAABABabaBAbABabaBAbaba` | + | −38 + 22√3 | [-0.105118, -0.052559] | 38 − 22√3 ; 19 − 11√3 |
| 9 | `bABBABabABAbabABaBAbabABAB` | − | −24 + 14√3 | [-0.068417, -0.040743] | −63/2 + 37/2√3 − √(145 − 167/2√3) ; 1/2 − 1/2√3 + √(143 − 165/2√3) |
| 10 | `bbababABABAbaBABabAB` | + | −24 + 14√3 | [-0.052559, 0.068417] | 19 − 11√3 ; 63/2 − 37/2√3 + √(145 − 167/2√3) |
| 11 | `bbababABABAbaBABabAbaBabABAB` | + | −38 + 22√3 | [-0.052559, 0.050291] | 19 − 11√3 ; 67/2 − 39/2√3 + √(143 − 165/2√3) |
| 12 | `bbababABABAbaBABabAbaBBB` | + | −28 + 16√3 | [-0.029941, 0.050291] | 41/2 − 23/2√3 − √(145 − 167/2√3) ; 67/2 − 39/2√3 + √(143 − 165/2√3) |
| 13 | `bbabABaBAbABabaBAbababbababa` | + | −38 + 22√3 | [-0.011815, 0.091035] | 37/2 − 21/2√3 − √(143 − 165/2√3) ; 33 − 19√3 |
| 14 | `bbabABaBAbABabaBAbabABBAbaBB` | + | −28 + 16√3 | [-0.011815, 0.091035] | 37/2 − 21/2√3 − √(143 − 165/2√3) ; 33 − 19√3 |
| 15 | `AABBAB` | − | 14 − 8√3 | [0.000000, 0.299003] | 0 ; 19/2 − 11/2√3 + √(143 − 165/2√3) |
| 16 | `ABABABBABABabAbaBABabABAbaBB` | + | 38 − 22√3 | [0.000000, 0.052559] | 0 ; −19 + 11√3 |
| 17 | `ABABABBABABabAbaBABABa` | + | 28 − 16√3 | [0.000000, 0.029941] | 0 ; −41/2 + 23/2√3 + √(145 − 167/2√3) |
| 18 | `babaBAbABaBAbabABababaBABABB` | + | 38 − 22√3 | [0.052559, 0.155409] | −19 + 11√3 ; −9/2 + 5/2√3 + √(143 − 165/2√3) |
| 19 | `babaBAbABaBAbabABabaBAbaba` | − | −24 + 14√3 | [0.052559, 0.155409] | −19 + 11√3 ; −9/2 + 5/2√3 + √(143 − 165/2√3) |
| 20 | `bbababABABAbaBabABAbaBABabAB` | + | −38 + 22√3 | [0.091035, 0.120976] | 33 − 19√3 ; 25/2 − 15/2√3 + √(145 − 167/2√3) |
| 21 | `bababaBABABabABAbaBabAbaBABB` | + | 38 − 22√3 | [0.093302, 0.196152] | −39/2 + 23/2√3 − √(143 − 165/2√3) ; −5 + 3√3 |
| 22 | `ABABabABAbaBABabAbaBabABAB` | − | −24 + 14√3 | [0.093302, 0.196152] | −39/2 + 23/2√3 − √(143 − 165/2√3) ; −5 + 3√3 |
| 23 | `AbababABabaBAbABaBAbabABAB` | + | −38 + 22√3 | [0.143594, 0.212011] | 14 − 8√3 ; 91/2 − 53/2√3 + √(145 − 167/2√3) |
| 24 | `ABAABabaBAbababABABAbaBABABa` | − | 42 − 24√3 | [0.143594, 0.287187] | 14 − 8√3 ; 28 − 16√3 |
| 25 | `baBAbabABabaBAbABababaBABABB` | + | 38 − 22√3 | [0.196152, 0.226094] | −5 + 3√3 ; −51/2 + 29/2√3 + √(145 − 167/2√3) |
| 26 | `baBAbabABabaBAbABabaBAbaba` | − | −24 + 14√3 | [0.196152, 0.248711] | −5 + 3√3 ; −24 + 14√3 |
| 27 | `babaBABabAbaBabABAbaBABABa` | + | 38 − 22√3 | [0.248711, 0.317129] | −24 + 14√3 ; 15/2 − 9/2√3 + √(145 − 167/2√3) |
| 28 | `bbaBabAbaBABabABAbaBABabaBAB` | + | −42 + 24√3 | [0.275372, 0.287187] | 93/2 − 53/2√3 − √(143 − 165/2√3) ; 28 − 16√3 |
| 29 | `AbababABaBAbabABababaB` | − | 42 − 24√3 | [0.287187, 0.317129] | 28 − 16√3 ; 15/2 − 9/2√3 + √(145 − 167/2√3) |
| 30 | `AbababABaBAbabABabaBAbABaBAB` | + | −42 + 24√3 | [0.287187, 0.317129] | 28 − 16√3 ; 15/2 − 9/2√3 + √(145 − 167/2√3) |

**Closure data** (pieces of $\varepsilon D_f$ and their composition sequences, given by row numbers and applied left to right; conventions as in the $n=8$ note):

| # | pieces of ε·D: composition (indices, applied left to right) |
|---|---|
| 1 | [8, 10, 28, 5] |
| 2 | [8, 10, 30, 5] ; [10, 23, 30, 5] |
| 3 | [8, 10, 29, 21] ; [11, 14, 2, 3] ; [10, 24, 21, 18] |
| 4 | [8, 10, 29, 6] ; [10, 24, 15, 8] |
| 5 | [8, 10, 30, 5] ; [11, 14, 2, 5] ; [11, 13, 24, 26] |
| 6 | [6, 15, 6, 21] |
| 7 | [6, 23, 24, 21] |
| 8 | [11, 13, 24, 26] ; [11, 20, 24, 26] |
| 9 | [6, 23, 24, 22] |
| 10 | [10, 15, 7, 22] |
| 11 | [11, 20, 24, 26] |
| 12 | [13, 20, 24, 15] |
| 13 | [13, 20, 24, 26] ; [12, 1, 5, 8] |
| 14 | [13, 20, 24, 15] ; [12, 1, 5] |
| 15 | [6, 6, 6, 18] |
| 16 | [16, 7, 21, 18] |
| 17 | [16, 6, 24, 21] |
| 18 | [16, 7, 25, 18] |
| 19 | [16, 6, 24, 26] |
| 20 | [12, 1, 5, 11] |
| 21 | [16, 7, 25, 21] ; [16, 9, 29, 21] ; [18, 9, 29, 21] |
| 22 | [6, 20, 24, 26] ; [6, 13, 24, 26] |
| 23 | [13, 23, 24, 22] |
| 24 | [13, 24, 27, 21] ; [13, 23, 29, 21] |
| 25 | [18, 9, 29, 21] |
| 26 | [6, 14, 2, 8] ; [6, 14, 2, 5] |
| 27 | [18, 7, 27, 21] |
| 28 | [13, 23, 28, 5] ; [13, 23, 30, 5] |
| 29 | [13, 23, 29, 21] |
| 30 | [13, 23, 30, 5] |
