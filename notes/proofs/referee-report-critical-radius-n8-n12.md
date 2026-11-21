# Referee report: critical radius of $GG_8$ and $GG_{12}$

Referee: Claude (independent of the authoring agent)

Documents refereed: `critical-radius-n8.md` and `critical-radius-n12.md` (this directory).
Companions taken as already refereed: `boundary-contact.md` (orbit and group monotonicity), `theorem1-converse.md`.
The certificate theorem that these notes restate from `critical-radius-n5.md` was re-proved here from scratch (§3).

All computations below were done with code written for this report, from the notes' Appendix A data and from the definitions. The author's programs were not run and not reused. Scripts and logs are in the session scratch directory `ref8/`: `fld.py` (exact arithmetic), `partA.py`, `redund.py`, `misc.py`, `cutref.py`, `run_*.log`.

---

## 1. Verdicts

| claim | $n=8$ | $n=12$ |
|---|---|---|
| $p^\ast\in\partial D_1$ exactly at $r_c$; $p^\ast\in\operatorname{int}D_2$ | correct | correct |
| Lemma 1.1 / Definition 1.2 (endpoint checks suffice) | correct (only "inside" conditions are used; see issue 7) | correct |
| Renormalization Lemma 2.1, Corollary 2.2 | correct | correct (used verbatim) |
| Lemma 2.3 (n=8) / Lemma 2.1 (n=12): the exact finite check | **correct, independently reproduced in full** | **correct, independently reproduced in full** |
| Theorem A: $GG_n(r)$ infinite for all $r\ge r_c$, with the explicit orbit points | **correct** | **correct** |
| Theorem 3.1 (cut-set certificate) | correct after cosmetic fixes (issue 6) | correct (same theorem) |
| Theorem B ($\delta_\ast=1/7$, resp. $1/20$) | correct as stated ("modulo the computation"). The certificate was independently reproduced in floating point with exact tie-breaking, and all its canonical invariants agree | same |
| Status, §5, open problems | correct after minor fixes (issues 2–4) | correct after minor fixes (issues 2, 3, 5) |
| Conjectures R₈, R₁₂ as statements | the sentence "would prove (B)" overclaims (issue 2) | same |

I found no fatal issue and no gap in any proof. The bound $r_\ast\le\inf\{r:GG_n(r)\text{ infinite}\}\le r_c$ is proved, and the notes state correctly that equality is open.

---

## 2. Part A: what was recomputed

### 2.1 Independent implementation

- **Arithmetic.** $\mathbb Z[\zeta_n]$ as integer 4-vectors, with $\zeta^4=-1$ resp. $\zeta^4=\zeta^2-1$. Real and imaginary parts lie in $\mathbb Q(\sqrt m)$, $m=2,3$, with Fraction coefficients.
- **Signs.** The sign of $\alpha+\beta\sqrt{H_1}+\gamma\sqrt{H_2}+\delta\sqrt{H_1H_2}$, with all coefficients and radicands in $\mathbb Q(\sqrt m)$, is decided by recursive squaring. No floating-point number enters any decision.
- **Words.** A point of the line is written $P+tD$, where $P,D\in\mathbb Z[\zeta]$ are tracked symbolically through the word. Each letter's condition "the current point lies in the closed disk" is the quadratic inequality $|D|^2t^2+2\operatorname{Re}((P-q)\bar D)\,t+|P-q|^2-r_c^2\le0$. This inequality is evaluated exactly at endpoints of the form $\alpha+\beta\sqrt H$.
- **Parsing.** The 31 resp. 30 words, their signs, shifts, exact endpoints and closure sequences were parsed directly from the Markdown tables of Appendix A. So what was checked is exactly what is printed.

### 2.2 Results (all exact)

**Basic facts.**
- $|p^\ast+1|^2=r_c^2$ exactly for both $n$. Also $|p^\ast-1|^2=6-3\sqrt2$ resp. $32-18\sqrt3$, both $<r_c^2$.
- $p^\ast=-1+(2+i)(1-\zeta)$ for $n=8$, and $p^\ast=(2-\sqrt3)(1-2i)$ for $n=12$.
- The chord endpoints of $J$ (n=8) and of $\ell\cap D_2$ (n=12) are exact roots of the $D_2$ constraint. $\ell\cap D_1$ is $[0,1.41154]$ for $n=12$ and $[0,3\sqrt2-2]$ for $n=8$, as stated.
- The factorization $r_c^2=\varepsilon^2(16+6\sqrt3)=2\varepsilon(7-2\sqrt3)$ holds.
- The threshold identities in n=8 §2.6 and §4.5 hold: $p^\ast+i\varepsilon^5=(1,27,-40,28)$ and $p^\ast+i\varepsilon^7=(1,167,-238,168)$, with $|q+1|^2=3117-2202\sqrt2$ and $112761-79732\sqrt2$.
- The three identities in n=12 Remark 3 hold.
- A box search $[-4,4]^4$ finds exactly 16 lattice points on $\partial D_1(r_c)$ for $n=8$. This is consistent with the PID/Kronecker argument, which I also checked by reading.

**Words.** All 31 (n=8) and 30 (n=12) words passed every check:
- The composite rotation is $\pm1$, the image of the line is the line, and the sign and the shift $c$ are exactly as listed.
- Each listed endpoint satisfies every letter's disk condition, plus the window conditions: $J$ for n=8; $D_2$ at start and end and $W$ for start and image for n=12.
- At each endpoint some constraint is active with the correct one-sided sign, so the listed domains are the maximal ones, as claimed. Maximality is not needed for the proof.
- The decimal domains agree with the exact ones to the 6 digits printed.

**Closure.** For each $f$, the pieces were reconstructed as follows. The valid set of a sequence $g_1,\dots,g_L$ is $\bigcap_i F_{i-1}^{-1}(D_{g_i})$, where $F_i$ is the composite of the first $i$ maps. Each piece runs from the end of the previous piece to the right end of its valid set. I checked that:
- each piece starts inside its valid set;
- the pieces chain up and reach the right end of $\varepsilon D_f$;
- the composite is exactly $t\mapsto\sigma_f t+\varepsilon c_f$, which is $\varepsilon f(\cdot/\varepsilon)$.

The comparisons involve one extra radical for $n=8$ ($\sqrt{19/2-5\sqrt2}$). For $n=12$ they involve two different radicals, $\sqrt{145-\tfrac{167}2\sqrt3}$ and $\sqrt{143-\tfrac{165}2\sqrt3}$, and were handled by the two-radical sign test. Result:
- every family member is covered;
- the effective counts are **46 pieces / 172 steps (n=8)** and **37 pieces / 147 steps (n=12)**;
- the step counts agree with the notes' 172 and 147. For the piece counts see issue 1.

**End-to-end check of the induction, using the true piecewise group action.**
- I expanded the induction of Lemma 2.1 into explicit group words. For level $k$ and point $t$, I chose the piece containing $t/\varepsilon^{k-1}$ and recursed on its sequence.
- I then applied each word letter by letter to $p^\ast$ with the genuine generators at $r=r_c$: rotate if the point is in the closed disk, identity otherwise. All points here are lattice points, so every disk test is an exact sign in $\mathbb Q(\sqrt m)$.

Results:
- **n=8**, $k=0,\dots,7$: word lengths 4, 36, 146, 468, 1700, 6300, 23518, 87636. Every word ends exactly at $p^\ast+4i\varepsilon^{k+1}$, and **no letter ever acted as the identity**.
- **n=12**, $k=0,\dots,6$: word lengths 6, 46, 250, 1166, 5120, 21742, 90460. Every word ends exactly at $p^\ast+2\varepsilon^{k+2}V$, and no letter acted as the identity.

### 2.3 Assessment of the logic

- **Convexity / validity.** Definition 1.2 only uses the condition that the image segment lies *inside* the disk of each letter. That condition is convex, so checking it at the endpoints is legitimate. No word in either family relies on a letter acting as the identity: validity requires every letter to rotate. So the problem that "wholly outside" is not implied by the endpoints does not arise. The end-to-end run confirms this.
- **Closure statement.** Hypothesis 2 of Lemma 2.1 is exactly the following. For every $s$ in a piece $I_j\subseteq\varepsilon D_f$, the orbit chain $s_i=g_i(s_{i-1})$ stays in the domains $D_{g_i}$, and $s_L=\varepsilon f(s/\varepsilon)$. Equivalently, $S\circ f\circ S^{-1}$ on $S(D_f)$ is realized piecewise by compositions of family members. At level $k$ each family word $w_g$ is replaced by its level-$(k-1)$ expansion, so word lengths grow by a factor of about 4 per level.
- **The induction.** I re-derived it; it is correct. The base case is Realization at $k=0$. The domains are fixed intervals and are applied at level $k$ through $\varepsilon^kD_g$; the chain's intermediate points lie in these by construction.
- **Infinitely many distinct points.** $0\in D_{\text{seed}}$, and the seed's $f(0)$ is $4\varepsilon\ne0$ resp. $2\varepsilon^2\ne0$. The points $p^\ast+\varepsilon^kf(0)D$ are pairwise distinct because $0<\varepsilon<1$. A finite group has finite orbits, so the group is infinite.
- **From $r_c$ to $r\ge r_c$.** This is correct and does not need the monotonicity theorems. Every letter of every word acts as a rotation because the point lies in the closed disk at $r_c$. The disks grow with $r$, so the same letters still rotate, with the same action. The closure hypothesis does not involve $r$. The closed-disk convention matters only at $p^\ast\in\partial D_1(r_c)$, where the seed's letter $a$ is applied to a boundary point, and the notes say so (n=8 Remark 1).
- **"Modulo an exact finite computation".** That computation is: (i) the listed endpoint sign checks for each word (the action plus the disk conditions at 2 endpoints); (ii) the closure chain checks. I reproduced **all** of it independently in exact arithmetic. Part A therefore no longer rests only on the author's program.

### 2.4 Relation to the paper (item 2)

I extracted the text of arXiv 2302.12950 from the PDF's compressed streams; the figures could not be rendered. The paper says:
- For $n=8$: "A path of consecutive line segments that follows the fractal structure can be realized, starting from the center of one disk and approaching the disk boundary from the interior … consecutive segments scale down by a factor of $\sqrt2-1$ and traverse angles of $\pi/8$." The limit point is said to give $r=\sqrt{5(2-\sqrt2)}$.
- For $n=12$: "an analogous construction gives a scale factor of $2-\sqrt3$, and $r=\sqrt{2(20-11\sqrt3)}$." The text does **not** state an angle $\pi/12$ explicitly.
- The paper adds: "These closed-form radii rely on the limit point lying on the disk boundary at the critical value, which has not been proven."

The n=8 note's §2.6 summary of this is accurate, and so is its statement that the π/8 turning was not reproduced. One observation, offered as information only:
- If "traverse angles of $\pi/8$" meant that consecutive segment vectors differ by the factor $\varepsilon e^{i\pi/8}$, the vertices could not all be orbit points of a lattice point. Differences of points in $\bigcup_j(\zeta^jz_0+\mathbb Z[\zeta_8])$ with $z_0\in\mathbb Z[\zeta_8]$ lie in $\mathbb Z[\zeta_8]$, and $e^{i\pi/8}\notin\mathbb Q(\zeta_8)$.
- So the paper's path is either not made of orbit points, or "angle" means something else, such as the angle subtended at a centre.
- The notes' straight-line mechanism is consistent with the paper's scale and limit point, and does not contradict the paper's text.

The n=12 note's Remark 3 is the one place that overstates the identification (issue 3).

---

## 3. Part B

### 3.1 The certificate theorem (n=8 Theorem 3.1; used for n=12)

I re-proved it. Each step is correct:
- **Invariance.** $a(K)\subseteq K$ and $a^{-1}(K)\subseteq K$ give $a(K)=K$.
- **The singular set $V$ is finite.** It lies in the set of arc endpoints together with the pairwise intersections of distinct circles.
- **$a(V)\subseteq V$.** There are three cases.
  - Outside $D_1$, $a$ is the identity on the open complement.
  - In $\operatorname{int}D_1$, $A$ is a local homeomorphism carrying $K\cap U$ onto $K\cap A(U)$, by (C2) both ways.
  - On $\partial D_1$, a second circle must pass through $x$; it is transversal by (C3); then either it is a crossing, or (C4) applies. The image is a branch point on $\partial D_1$.
- **Cells.**
  - The faces avoid $\partial D_p$ by (C1).
  - An edge on a circle other than $\partial D_p$ cannot meet $\partial D_p$, since a meeting point would be singular.
  - So each generator is one isometry on each cell and maps cells onto cells; applying $a^{-1}$ gives the "onto" part.
- **Counting.** Fix a bounded cell $X$, a target cell $Y$ and a rotation part $\zeta^j$. At most one translation carries $X$ onto $Y$. The unbounded face lies outside $D_1\cup D_2$ and is fixed pointwise. Group elements are determined by their action on all cells, so the group is finite.
- **Closed-disk boundaries.** These are handled correctly. On $\partial D_1$ the generator $a$ acts as $A$, which is consistent with closed disks, and edges lying on $\partial D_1$ are cells on which $a=A$.
- **Inverses.** Invariance under inverses is built into (C2), through $A^{\pm1}$ and $B^{\pm1}$.
- **$r>1$.** This hypothesis ensures that $\partial D_1$ and $\partial D_2$ cross transversally. Theorem B then extends finiteness downward by group monotonicity (`boundary-contact.md` Theorem 3.4). That is applied correctly.

### 3.2 Independent reproduction of the certificates

**Program.** I wrote my own closure, `cutref.py`. It shares no code with `cut/`.
- **Representation.** Circles are given by their centres $c\in\mathbb Z[\zeta]$. Arc endpoints are intersection symbols $(e,s)$, plus artificial cut points at direction $\zeta^k$ from the centre, which are carried by rotations and merged away at the end.
- **Decisions.** Ordering decisions use floating-point angles when they differ by more than $10^{-9}$, and exact two- or three-radical sign tests otherwise. Tangency is tested exactly. (C2) is re-checked independently on the final merged arcs, and (C4) is checked on the maximal arcs themselves.

Results. "Author" values are from Table 3.1. Circles, maximal arcs and (C4) endpoints are invariants of the minimal cut set $K(r)$, so they should agree between implementations. Piece counts and image-arc counts depend on the implementation.

| n | δ | circles (mine / author) | maximal arcs | (C4) endpoints / failures | max abs σ(c) | closed |
|---|---|---|---|---|---|---|
| 8 | 1 | 52 / 52 | 84 / — | 80 / 0 | 6.2 / 6.2 | yes |
| 8 | 1/2 | 726 / 726 | 1 920 / 1 920 | 676 / 0 (author 676 / 0) | 20.6 / 20.7 | yes |
| 8 | 1/3 | 3 648 / 3 648 | 10 824 / 10 824 | 1 420 / 0 (1 420 / 0) | 46.1 / 46.1 | yes |
| 8 | 1/5 | 4 222 / 4 222 | 18 780 / 18 780 | 2 920 / 0 (2 920 / 0) | 47.6 / 47.6 | yes |
| 8 | 1/6 | 5 024 / 5 024 | 22 258 / 22 258 | 3 176 / 0 (3 176 / 0) | 51.1 / 51.1 | yes |
| 8 | **1/7** | **24 150 / 24 150** | **122 762 / 122 762** | **5 692 / 0 (5 692 / 0)** | 110.4 / 110.4 | yes |
| 8 | 1/10 | 30 490 / (30 490 at author's cap) | 213 418 | 10 328 / 0 | 122.8 / 122.8 | **yes** (author: cap) |
| 8 | 1/12 | 31 366 | 229 058 | 11 252 / 0 | 124.6 | yes |
| 12 | 1/3 | 282 / 282 | 556 / 556 | 368 / 0 (368 / 0) | 13.5 / 13.5 | yes |
| 12 | 1/5 | 2 324 / 2 324 | 6 016 / 6 016 | 1 000 / 0 (1 000 / 0) | 37.1 / 37.1 | yes |
| 12 | 1/10 | 2 360 / 2 360 | 6 192 / 6 192 | 1 032 / 0 (1 032 / 0) | 37.5 / 37.5 | yes |
| 12 | **1/20** | **37 180 / 37 180** | **114 380 / 114 380** | **3 928 / 0 (3 928 / 0)** | 137.5 / 137.5 | yes |
| 12 | 1/30 | 37 840 | 157 924 | 4 804 / 0 | 137.5 | yes |

- In every run my (C2) re-check found 0 image arcs outside a single merged arc.
- No tangency occurred, not even at $\delta=1/2$ and $\delta=1$, where $4\delta\in\mathbb Z$.
- No two float angles of distinct symbols ever came within $10^{-9}$, so the exact fallback was never triggered.

**Sanity checks.**
- **At $r=r_c$ ($\delta=0$)** the run aborts immediately on an exact **tangency** for both $n$ (circle centres $(9,-8,-4,10)$ for $n=8$ and $(3,2,-2,4)$ for $n=12$). So (C3) fails at $r_c$, and the certificate cannot be produced there.
- **Above $r_c$** ($\delta=-1/3$ for n=8, $-1/5$ for n=12), where Theorem A gives an infinite group, the closure hits a cap of $5\cdot10^5$ pieces and keeps growing. This is as required.
- **Just below $r_c$** ($\delta=10^{-3}$) the closure hits a cap of $10^6$ pieces. This is inconclusive, as expected.
- **A known finite case.** $GG_6(r)$ is finite for every $r$ by the refereed Theorem 5.1 of `theorem1-converse.md`. I ran it with the $\mathbb Z[\zeta_{12}]$ arithmetic and rotation by $\zeta_{12}^{\pm2}$, at $r^2=2.1$, $3.7$ and $6.1$. The certificate closes with 10, 18 and 24 circles and (C4) holds.

**Status of my reproduction.** Every ordering decision in my runs was a float decision with a margin above $10^{-9}$, against a rounding error of order $10^{-13}$. So my runs are strong independent confirmation, not an exact proof. The proof of Theorem B rests on the author's exact `verify.py`, which I did not read or run. The canonical invariants agree exactly at the certified radii.

---

## 4. Issues

1. **Closure piece counts include degenerate pieces.**
   - *Location:* n=8 §2.4 and Appendix A (rows 10, 13, 15); n=12 §2.3 and Appendix A (rows 3, 5, 8, 21, 22, 24, 26, 28).
   - *Severity:* cosmetic.
   - *Explanation:* "49 pieces" and "45 pieces" include 3 resp. 8 listed pieces that meet $\varepsilon D_f$ only in its right endpoint. The previous piece already reaches that endpoint. These pieces are valid but redundant. The effective counts are 46 and 37. The author's verifier evidently skips them too, since its step counts, 172 and 147, are the counts without them.
   - *Repair:* drop the redundant pieces or say "46 (resp. 37) pieces"; in Lemma 2.3(3), say that pieces after full coverage are ignored.

2. **"Conjecture R₈ (R₁₂) together with Table 3.1 at one level would prove (B)" overclaims.**
   - *Location:* n=8 §4, after Conjecture R₈; n=12 §4.
   - *Severity:* minor.
   - *Explanation:* The conjecture concerns only the combinatorial type of $K(r)$ in shrinking neighbourhoods of $p^\ast$ and its images. To deduce finiteness one still has to control $K(r)$ away from these neighbourhoods, show that (C1)–(C4) persist, and handle the curvature mismatch that the notes themselves point out (§4.6). Also, "level" and the thresholds $\delta_k$ are defined only through `notes/engine.md`.
   - *Repair:* say "would reduce (B) to …", or state precisely which additional statement is needed; and define $\delta_k$ and "type at level $k$" in the note.

3. **n=12 Remark 3, "This is the paper's 'path towards the boundary'".**
   - *Location:* n=12 §2.4, Remark 3.
   - *Severity:* minor.
   - *Explanation:* The paper's construction is a path of segments, described for $n=8$ as turning by π/8, with "an analogous construction" for $n=12$. A vertical approach of orbit points is not shown to be that path. §2.5 of the same note correctly says the geometry is "neither confirmed nor refuted".
   - *Repair:* say "consistent with the paper's limit point and scale".

4. **The δ=1/10 row and §3.5 present an implementation limit as an intrinsic one.**
   - *Location:* n=8 Table 3.1 row δ=1/10; n=8 §3.5 ("at δ=1/10 it exceeds 2·10⁶").
   - *Severity:* minor.
   - *Explanation:* The 2·10⁶ figure is the author's stored-piece count. My implementation stores 547 504 pieces at δ=1/10 and closes it: 213 418 maximal arcs, (C4) holds, float-filtered. δ=1/12 for n=8 and δ=1/30 for n=12 also close, using under 1 GB of memory.
   - *Repair:* reword §3.5. Optionally, run the exact `verify.py` at δ=1/10 or 1/12 (n=8) and 1/30 (n=12) to improve $r_\ast$.

5. **Second radical in n=12 not introduced in the text.**
   - *Location:* n=12 §2.2.
   - *Severity:* cosmetic.
   - *Explanation:* The endpoints use both $\sqrt{145-\tfrac{167}2\sqrt3}$ and $\sqrt{143-\tfrac{165}2\sqrt3}$, but §2.2 mentions only the first.
   - *Repair:* say where the second comes from (a disk constraint on an intermediate image line), and that the comparisons need two-radical sign tests.

6. **Theorem 3.1 wording.**
   - *Location:* n=8 §3.2.
   - *Severity:* cosmetic.
   - *Explanation:* (C3) should exclude $\partial D_p$ itself, as the n=5 version does ("other than $\partial D_p$ itself"). Step 5 compresses the n=5 proof's step 7, the induction along words showing that every $g$ is a single isometry on each cell. The singleton cells are covered by "bounded cell", which is fine.
   - *Repair:* restore both phrases.

7. **Definition 1.2 should say explicitly that letters are never allowed to act as the identity.**
   - *Location:* n=8 §1.
   - *Severity:* cosmetic.
   - *Explanation:* This is what makes the endpoint check sufficient, since "wholly outside a disk" is not a convex condition. The definition implies it, but it is worth one sentence.

8. **Lemma numbering clash.**
   - *Location:* n=12 §2.3–2.4.
   - *Severity:* cosmetic.
   - *Explanation:* The exact check is called "Lemma 2.1", which is also the name of the renormalization lemma it is combined with. Theorem A's proof cites both.
   - *Repair:* rename the exact check to Lemma 2.3, matching n=8.

9. **Caveat 1 in both notes is now out of date.**
   - *Location:* the caveat lists.
   - *Severity:* minor.
   - *Explanation:* Part A has been independently re-implemented and re-checked exactly; the Theorem B certificates have been independently reproduced in floating point with exact tie-breaking.
   - *Repair:* update the caveat and cite this report. Keep the statement that the exact cut-set verification is single-author.

10. **Maximality of domains is claimed but not needed.**
    - *Location:* n=8 Lemma 2.3(1); n=12 Lemma 2.1(2).
    - *Severity:* cosmetic.
    - *Explanation:* The claim is true (verified), but the proof needs only validity on the listed intervals. Saying so would shrink the Lean task of §7.

The status paragraphs do **not** overclaim on the main point. Both notes state that the closed form is proved as an upper bound, that $r_\ast$ (certified) is a lower bound, and that equality is open (Status bullet 3, §5, §6 table). The title "The critical radius of $GG_n$" is acceptable given that framing. One improvement would be an explicitly labelled conjecture, "$GG_n(r)$ is finite for all $r<r_c$", separate from R₈/R₁₂.

---

## 5. What I did not check

- The author's programs (`verify_closure_n.py`, `exactn.py`, `cut/cut.py`, `cut/verify.py`) were neither read nor run, except for listing the directory. I did not compare against their logs.
- My cut-set runs are float-filtered, as described in §3.2. They are not an exact proof of Theorem B.
- The numerical evidence was not checked: n=8 §5 and n=12 §5 orbit sizes and threshold sweeps; Remarks 2–3 of n=8 §2.5; the orbit-of-0 observations; the "how the family was found" search descriptions; and the n=12 Remark 1 orbit counts.
- `notes/engine.md`, `arithmetic.md` and the companion notes were not re-refereed.
- The paper's figures (5c, 5d) could not be rendered. Only its text was read.
- §7 (the Lean plan) was not checked.
