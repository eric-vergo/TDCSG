# Referee report: `critical-radius-n5.md`

Referee: Claude (independent of the authoring agent)

Scope: the note `critical-radius-n5.md` in this directory, the author's programs in the session scratch directory `t4/` (`certify.py`, `z5.py`, `partA.py`; read only, never modified), and the paper arXiv 2302.12950 (garbled text extraction). The companions `boundary-contact.md` and `theorem1-converse.md` are taken as refereed. My own code is in the session scratch directory `ref4/` (`fld.py`, `cut.py`, `partA_ref.py`, `author_dump.py`, `test_same.py`). It was written from the theorem statements, not adapted from `t4/`.

## Verdicts

| claim | verdict |
|---|---|
| (A) $GG_5(r)$ infinite for every $r\ge r_c=\sqrt{3+\varphi}$ (Theorem A, Lemma 3.1, §3.3) | **correct after minor fixes** (issues 1, 2) |
| Side fact: $r_c$ is where the lens corners are $\pm(\zeta-\zeta^{-1})$; same for $n=10$, not for $n=8,12$ | **correct** |
| (B1) Theorem 4.2 (cut-set certificate) and Lemma 4.1 | **correct after minor fixes** (issues 3, 4, 5) |
| (B2) Theorem B: $GG_5(r)$ finite for $r\le r_\ast$, $r_\ast^2=3+\varphi-1/10$ | **correct** given the computation, which I reproduced independently, with **identical arc sets**. There is one reproducibility **gap**: the program and its output are not archived (issue 6) |
| (C) Openness of $(r_\ast,r_c)$, Conjecture R, §6–§7 | open status stated honestly. The sentence "Conjecture R plus Table 5.1 would prove (B)" is a **gap** (issue 7). "Exact only at $r_c$" needs qualifying (issue 8) |
| Title / status table | **minor overclaims** (issues 9, 10) |

## Issues

**1. (minor) §3.2, "All three words are tight at $r_c$": the list of tight points is incomplete.**
I checked exactly which trajectory points sit at squared distance exactly $3+\varphi$ from a centre. They are $\pm E$, the lens corners $\pm(\zeta-\zeta^{-1})=\pm(1,2,1,1)$, and also $\pm(1,1,1,2)=\pm(\zeta^3-\zeta^{-1})=\mp\bar E$. The last pair are the mirror images of $\mp E$ in the real axis; $(1,1,1,2)$ lies on $\partial D_2$ and its negative on $\partial D_1$. The claim "each word is tight" is correct: each word fails at $r^2=3+\varphi-10^{-6}$. *Repair:* add $\pm\bar E$ to the list.

**2. (minor) §3.3 Remark 2: "Only the closed-disk convention at $E$ and $E'$ is used."**
This is false as stated. The closed convention is needed at every tight point of issue 1, including the lens corners, which are visited by $w_1$, $w_2$ and $w_3$. *Repair:* "the closed-disk convention is used at the tight points $\pm E$, $\pm\bar E$, $\pm(\zeta-\zeta^{-1})$".

**3. (minor) Theorem 4.2, proof step 8: "the unbounded face is $\mathbb C\setminus(D_1\cup D_2)$, by (C1)".**
The theorem allows any $K$ satisfying (C1)–(C4), and such a $K$ may contain arcs outside $D_1\cup D_2$. Then the claim is false, although the conclusion survives. *Repair:* "the unbounded face misses $D_1\cup D_2$, so every generator fixes it pointwise." All other cells are bounded and are covered by the five-maps-per-target count. Also state explicitly that there are finitely many faces (a finite arrangement of circular arcs has a complement with finitely many components). The count in step 8 needs this.

**4. (minor) Theorem 4.2, step 4: "edges ... are open arcs".**
A full circle of $K$ that meets no other arc of $K$ is a component of $K\setminus V$ without being an open arc. The argument is unaffected, because such an edge is bounded and maps to an edge. *Repair:* "open arcs or full circles".

**5. (minor) §4.2, "The minimal certificate", and §4.1, "Equivalently".**
(a) The "if" direction is right: if the group is finite, then $K(r)$ is a finite union of arcs. But finiteness of $K(r)$ does not give (C3) or (C4). For example, my run at $\delta=1$ (where $4\delta\in\mathbb Z$) aborts on a tangency, and $GG_5$ is presumably finite there. So the certificate is sufficient, not necessary, and "the canonical finite test of finiteness" overstates it. *Repair:* say "a sufficient test, which also needs (C3)–(C4)".
(b) The "compact invariant window" is asserted to be equivalent to (B) with no proof. The direction window ⇒ $\mathcal T(r)$ finite is clear. For the converse, invariance of a closure under discontinuous maps needs an argument. *Repair:* prove it, or say "(B) follows from".

**6. (gap: reproducibility of a computer-assisted proof) §5.1.**
The program lives only in a session scratch directory, which the note itself says is not in the repository. The certificate files (`cert_*.json`) store only circle centres, not the arcs. So $K(r_\ast)$ cannot be re-checked without rerunning the closure. *Repair:*
- commit `certify.py`, `z5.py` and `partA.py`;
- export the maximal arcs (centre plus two symbolic endpoints; 198,470 arcs at $\delta=1/10$) as the certificate;
- ship a separate checker of (C1)–(C4), like my `cut.py check()`, which reads that file.
I have done this independently (see the computations section), so the mathematical claim stands. But a "proved modulo computation" status should not rest on files that a cleanup can delete. The §8 caveat 1 ("has not been re-implemented independently") is now out of date.

**7. (gap, in the conjectural part) §6, "Conjecture R plus Table 5.1 at level $k_0$ would prove (B) by induction on $k$".**
Conjecture R constrains only the combinatorial type of $K(r)$ inside scaled copies of $U$ near $\pm E$. Proving (B) needs, for some sequence $r_k\uparrow r_c$:
- that $K(r_k)$ is finite as a whole, including outside the copies of $U$, and that the recursion stops after finitely many levels at each fixed $r$;
- that (C3)–(C4) hold.
The conjecture asserts neither. The sentence "The correction from curvature never changes the sign ..." is also ambiguous: it could be read as part of the conjecture or as a claim. *Repair:* reformulate Conjecture R so that it gives $K(r)$ finite with (C3)–(C4) at every $r$ in each level window (or at one radius per level, which suffices by monotonicity), or weaken "would prove" to "is the main missing ingredient".

**8. (minor) §6.4 and §7.2: "exact only at $r_c$" / "no exact renormalization below $r_c$".**
The §6.4 argument is correct in this precise form: a similarity of ratio $\varphi^{\pm3}$ cannot carry an arrangement of radius-$r$ arcs onto one of radius $r'\approx r$ over a region that contains a non-degenerate arc. But the same argument applies at $r=r_c$ too. What is exactly self-similar at $r_c$ is only the 1-D interval exchange on the chord ($G=\varepsilon E$), not the 2-D picture. *Repair:* state that exact similarity renormalization of the 2-D cut set fails at every $r$, including $r_c$, and that only the 1-D chord dynamics renormalizes exactly at $r_c$. Also note that the argument excludes only conjugacy by similarities.

**9. (minor) §8 table, row "infinite orbit exactly at $r_c$ (paper's footnote 4) proved here for $n=5$".**
Footnote 4 is about the *critical radius*. The note proves infinitude at $\sqrt{3+\varphi}$, which the paper's Theorem 2 already does. It does not prove that $\sqrt{3+\varphi}$ is the critical radius, as the note's own caveat 5 says. *Repair:* "infinite at $\sqrt{3+\varphi}$ (paper's Theorem 2; footnote 4 for $n=5$ would follow from (B))".

**10. (minor) Title.**
"The critical radius of $GG_5$" suggests the critical radius is determined. What is proved is $r_\ast\le r_{\rm crit}\le r_c$. The status paragraph is honest. *Repair:* for example "Bounds on the critical radius of $GG_5$: infinite for $r\ge\sqrt{3+\varphi}$, finite for $r\le r_\ast$".

**11. (cosmetic) §5.2, remarks.**
- `arcs_float.py` is by the same author, so it is a consistency check rather than an "independent" implementation.
- "Pieces" depends on processing order and is not an invariant of $K$. Report the number of maximal arcs (64, 952, 4222, 13138, 35194, 87922, 198470 for the seven rows of Table 5.1).
- The (C4) column counts piece endpoints including shared ones. On maximal arcs the counts are 60, 316, 864, 1696, 2964, 4420, 7172.
- The author's store contains two degenerate (single-point) pieces from $\delta=9/20$ on. They lie on a boundary circle and are harmless, but deserve a sentence.

**12. (cosmetic) §6, template for $n=8,10,12$.**
The values $r_c^2=10-5\sqrt2$, $4-\varphi$, $40-22\sqrt3$ match the paper (Table 1 and §"Geometric Constructions"), and so do the scale factors $\sqrt2-1$ and $2-\sqrt3$. "Carry over verbatim" overstates it: `z5.py` hard-codes $\Phi_5$, and the side-of-line sign uses $\zeta_5-\zeta_5^{-1}$. My `fld.py` shows the generalization is routine. The claim that the paper's $n=8,12$ constructions are limit-point arguments is correct.

**13. (cosmetic) §7.4, literature.**
I confirmed by search the bibliographic data of Akiyama–Brunotte–Pethő–Steiner (Tsukuba J. Math. 32 (2008), no. 1). Their theorem is periodicity of all *integer* sequences with $0\le a_{k-1}+\lambda a_k+a_{k+1}<1$ for $\lambda\in\{(\pm1\pm\sqrt5)/2,\pm\sqrt2,\pm\sqrt3\}$, that is, lattice orbits of the discretized rotation. The note's "all orbits periodic" should say this. Consider also citing Lowenstein–Hatjispyros–Vivaldi (Chaos 1997) for the golden case. I did not check the other citations (Adler–Kitchens–Tresser 2001; Kouptsov–Lowenstein–Vivaldi 2002; Goetz–Poggiaspalla; Lowenstein–Kouptsov–Vivaldi) beyond my own memory, which agrees with them.

## Part A: what I checked (`ref4/partA_ref.py`, own $\mathbb Z[\zeta_n]$ arithmetic in `fld.py`)

All decisions are exact (integer vectors, zero tests, signs in $\mathbb Q(\sqrt5)$ with a proven lower bound).

- **Points.** $E=(0,1,-1,0)$, $F=(1,-1,1,-1)$, $G=(2,-3,3,-2)$.
- **Identities.** $\varphi F=E$ and $\varphi^3G=E$ hold exactly. $F/E=\varphi^{-1}$ and $G/E=2\varphi-3$ are real elements, so all six points lie on the chord, in the stated order.
- **Boundary.** $|E+1|^2=3+\varphi$ exactly, and $|E-1|^2<3+\varphi$.
- **Convention.** Read left to right ($a$ is rotation by $\zeta^{-1}$ about $-1$), each word maps its segment endpoints exactly onto the targets in order. Read right to left, each word leaves a disk at $r_c$. So the left-to-right convention is the right one.
- **Each word.**
  - Before each letter both current endpoints lie in that letter's closed disk. By convexity the whole segment does, so the letter acts on it as one global rotation.
  - The $\zeta$-exponents sum to $0\bmod5$.
  - The composite is a translation: $w_1,w_2$ by $(2,-2,2,-2)=2F=2\varphi^{-1}E$, and $w_3$ by $(2,-4,4,-2)=G-E=-2\varphi^{-2}E$. The same translation holds at both endpoints.
  - Every intermediate segment lies in $D_1\cap D_2$, with both endpoints in both disks at every stage.
- **Endpoints suffice.** Disks and segments are convex. Each letter acts on the current segment by a single isometry because the whole current segment lies in the letter's disk. By induction the whole closed segment is translated.
- **Tightness.** For each word the maximum squared distance to a centre is exactly $3+\varphi$. Each word fails at $r^2=3+\varphi-10^{-6}$. The tight points are listed in issue 1.
- **Cover and induced map.**
  - The source segments $[E',F']\cup[F',G']\cup[G',E]$ cover $E'E$.
  - The map $T$ on $[-1,1)$ is $t+2\varphi^{-1}$ on $[-1,-\varphi^{-3})$ and $t-2\varphi^{-2}$ on $[-\varphi^{-3},1)$. Since $2\varphi^{-1}+2\varphi^{-2}=2$, this is rotation by $2\varphi^{-1}$ on $\mathbb R/2\mathbb Z$.
  - On the overlap point $-\varphi^{-1}$, $w_1$ and $w_2$ agree.
- **Infinite orbit.**
  - $0\in[G',E]$, and each $t_kE$ is the image of $0$ under a product of group elements, so it lies in the $GG_5(r)$-orbit of $0$.
  - $t_k\equiv2k\varphi^{-1}\pmod 2$ with $\varphi$ irrational, so the $t_k$ are distinct.
- **Extension to $r>r_c$.** The note argues directly, not via monotonicity: the disks grow, every disk test still passes, and the rotation applied does not depend on $r$. This is correct. Orbit monotonicity (`boundary-contact.md` Thm 3.1) would give the same result.
- **Side fact.**
  - $\zeta-\zeta^{-1}=(1,2,1,1)$, and $|\zeta-\zeta^{-1}|^2+1=3+\varphi$ exactly.
  - $1+4\sin^2(\pi/5)=4-\varphi$, which is the paper's $r_c(10)^2$.
  - For $n=8$: $3\ne10-5\sqrt2$. For $n=12$: $2\ne40-22\sqrt3$.

## Theorem 4.2 (B1): line-by-line assessment

I read "arc" as a closed arc of a radius-$r$ circle, "tangency" (C3) as $|c-p|=2r$ for a carrying circle $c\ne p$ (equal radii rule out internal tangency), and (C4) as stated.

- **Step 1.** $a^{\pm1}(K)\subseteq K$ gives $a(K)=K$.
- **Steps 2–3.** $V$ is finite and $a(V)=V$. The case $x\in\partial D_1$ is exactly where (C3) and (C4) are needed. Without them, a vertex could map to a regular point of $\partial D_1$ and the cell structure would not be preserved. Using $A(D_1)=D_1$, the case $x\in\operatorname{int}D_1$ is fine.
- **Steps 5–6.** Faces and edges lie in $\operatorname{int}D_p$, lie in $\partial D_p$, or miss $D_p$. On each of them $a$ is a single isometry, and it maps cells onto cells, by applying the same argument to $a^{-1}$.
- **Steps 7–8.** The word map is constant on each cell. For bounded cells there are at most five maps per target. There are finitely many cells. So $\mathcal T(r)$ is finite, and so is the group (Lemma 4.1(3), whose proof I also checked; the bound $|t|\le2+2r$ and the lattice argument are fine).
- **Points on arcs and closed disks.** These are handled, because $\partial D_p\subseteq K$ and cells partition $\mathbb C$.
- **Inverses.** Invariance under inverses is part of (C2), and the program applies both $A$ and $A^{-1}$.
- **Could $K$ be finite with the group infinite?** Not under (C1)–(C4), by the argument above. I found no counterexample. At $r=r_c$ ($\delta=0$) both programs stop on a tangency, so (C3) fails at the first step. At $r^2=3+\varphi+1/10$ (group infinite by Theorem A) neither closure terminates: both hit the time cap with the circle count still growing.
- **Known finite cases.** The certificate succeeds, with (C1)–(C4) all holding, for:
  - $n=5$ at $r^2=\varphi-1/10<\sec^2(\pi/5)$ (10 circles; the author's program agrees: 10 circles, (C4) 0 failures);
  - $n=5$ at $r<1$ (2 circles);
  - $n=3,4,6$ at $r^2\in\{1/3,4/3,7/3,10/3,31/7,40/7,73/7,101/3\}$, all closed.
  The one exception is $n=6$, $r^2=4/3$. There my program stops on a genuine triple point (two different symbols naming the same point), which it does not handle; this does not bear on the theorem.
  I did not verify group orders such as $25\cdot9!/2$ from the certificates.

## Computation B2: code review of `t4/certify.py`

- **Exactness.**
  - Equality of endpoints: identical symbols, else an exact circumcentre test in $\mathbb Q(\zeta_5)$. It was never needed (`exact_eq_calls=0`).
  - Disk and tangency tests: exact in $\mathbb Q(\sqrt5)$.
  - Ordering: `mpmath.iv` at 120 bits, with quadrants fixed by exact signs. A comparison is declared only when the intervals are disjoint, and otherwise raises.
  - I spot-checked that `iv.atan2` returns enclosures (it is a genuine interval routine in `mpmath.ctx_iv`). Trust in mpmath's outward rounding remains, as the note says.
- **Constants.** $\cos72^\circ$, $\sin72^\circ$, $\cos144^\circ$, $\sin144^\circ$ are correct.
- **Window orientation.** The arc of $\operatorname{circle}(c)$ inside $D_p$ runs ccw from $(p,-1)$ to $(p,+1)$, because $\beta=\arccos(|d|/2r)\in(0,\pi/2)$.
- **Pre-filter.** It uses float midpoints with a $10^{-6}$ margin. That is sound except for an arc whose length is within $10^{-6}$ of $2\pi$, where it could only cause re-adding of covered parts. It is harmless here: the outputs agree exactly with mine.
- **Hypotheses.**
  - (C1) is by initialization.
  - (C2) is by construction. I checked it independently on the author's output (below).
  - (C3) is checked at every processed circle against both centres, and is implied by $4\delta\notin\mathbb Z$ (correct: $|c-p|^2\in\mathbb Z[\varphi]$).
  - (C4) is checked on piece endpoints, with "shared" meaning that a piece on the same circle continues the arc. That is stricter than the theorem requires.
- **Cap.** The default `maxpieces=10**6` truncated the first $\delta=1/10$ run (`log_1_10.txt`). The rerun (`log_1_10b.txt`) closed. This is consistent with the note.

## Independent computations (record)

My implementation (`ref4/cut.py`) differs from the author's in three ways:
- Orderings use double-precision angles. Any two positions within $10^{-9}$ rad are forced to an exact identity decision, and the program aborts if they are distinct. The error bound: the worst conditioning factor over all $\delta=1/10$ circles is $1/\sqrt{1-x^2}\approx46$ (min $|4\rho-|c-p|^2|=0.0086$), so the angle error is about $10^{-14}$, far below the $10^{-9}$ margin.
- Sign decisions are exact zero tests plus numerics with a proven norm lower bound.
- Exact point coincidence uses a different formula (incidence on the second circle plus side test). I validated it on three synthetic triple points, against numerics, with perturbed controls.

The arc store is merged into maximal arcs. After closure, a separate pass checks (C1)–(C4): every image of every maximal arc $\cap D_p$ under $A^{\pm1}$ or $B^{\pm1}$ must lie inside a single maximal arc. "Identical" in the tables below means the sorted canonical lists of maximal arcs (centre, start symbol, end symbol) are byte-identical; the author's pieces were merged by `author_dump.py`, which imports `certify.run` read-only.

Results at $r^2=3+\varphi-\delta$, $n=5$:

| $\delta$ | mine: closed / circles / pieces (+2 initial) / maximal arcs / (C2) uncovered / tangencies / (C4) failures | author's run | arc sets |
|---|---|---|---|
| 13/5 | yes / 54 / 112 / 64 / 0 / 0 / 0 | 54 / 112 | identical |
| 1/2 (not in the note's table) | yes / 1398 / 8749 / 3074 / 0 / 0 / 0 | 1398 / 8751 (2 point pieces) | identical |
| 9/10 | yes / 466 / 2040 / 952 / 0 / 0 / 0 | 466 / 2040 | identical |
| 9/20 | yes / 1722 / 10301 / 4222 / 0 / 0 / 0 | 1722 / 10303 (2 point pieces) | identical |
| 3/10 | yes / 5044 / 35665 / 13138 / 0 / 0 / 0 | 5044 / 35667 | identical |
| 1/5 | yes / 11606 / 185539 / 35194 / 0 / 0 / 0 | 11606 / 185541 | identical |
| 3/20 | yes / 30776 / 496587 / 87922 / 0 / 0 / 0 | not rerun; matches Table 5.1 (30776 / 496587) | counts agree |
| **1/10** | **yes / 50714 / 1437580 / 198470 / 0 / 0 / 0** (116 s, 1.0 GB) | 50714 / 1437580; (C4) 0 failures; 2304 s | **identical** |

Further checks:
- My (C1)–(C4) checker, applied to the author's merged output, passes with the same numbers at $\delta=13/5,1/2,9/10,9/20,3/10,1/5,1/10$.
- Sanity runs:
  - $\delta=0$: tangency abort in both programs.
  - $\delta=-1/10$ ($r>r_c$): no closure in either program within its cap (author 200 s: 119,542 circles; mine 150 s: 1,400,581 circles, still growing).
  - $\delta=1/40$: no closure within 120 s (118,821 circles).
  - $\delta=31/10$: closed in both, 10 circles.
  - $\delta=37/10$: closed in both, 2 circles.
  - $\delta=3$: closed, 54 circles.
  - $\delta=1$: tangency.

## What I did not check

- The measured renormalization data in §6.1 (threshold ratios, orbit-growth factors) and the files they cite (`twodisk_experiments.md`, `twodisk_arith.md`, `exact5.json`).
- The internal-extent column $\max|\sigma(c)|$ of Table 5.1.
- The run times.
- The group orders at known radii (only that the certificate succeeds there).
- The literature beyond the bibliographic check in issue 13.
- The Lean outline in §9.
- The correctness of `mpmath.iv` beyond a spot check.
- My own orderings rest on a stated double-precision error bound, not on interval arithmetic. The two programs agree exactly, so they cross-check each other.
