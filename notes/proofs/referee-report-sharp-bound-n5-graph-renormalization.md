# Referee report: `sharp-bound-n5-graph-renormalization.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: transport of tokens and connectors by $\varepsilon$, and what the renormalization statement (R) still needs" (`sharp-bound-n5-graph-renormalization.md`, commit `4d90a9b`).

Companions consulted:
- the component-graph note and its referee report (house format, the counterexamples to its Conjecture 5.1, the fixed form of its Theorem 3);
- the (T) note and its referee report (Table 1.1, $\Lambda_T$, Theorem 4, Corollary 5(2));
- the chaining note (definitions; the method of Computation 1.2);
- `sharp-lower-bound-n5.md` Theorem 4.1, `boundary-contact.md` Theorems 3.1 and 3.4, `../certificates.md`, `../engine.md`.

## Summary

The proofs are sound. Every line was checked and every constant re-derived, the margins by a second, independent method.
- **Theorem 1** is correct after three small fixes. They are the same kind of fix the component-graph note needed.
  - The bound in item 3 must be $\max(N_0,5|GG_5(r_\ast)|)+kC$, not $\max(N_0,5|GG_5(r_\ast)|+kC)$.
  - The base used "$r'$" for the radius at $\delta'$, which clashes with the note's $r'$.
  - The last step needs the lattice reduction at non-norm radii (`sharp-lower-bound-n5.md` Theorem 4.1), because the note's $D$ ranges over lattice orbits.

  **Fixed.**
- **Lemma 2** is correct as written.
- **Theorem 3** is correct, and in fact holds for every $\delta\ge0$. As written, its proof did not quite reach the stated range.
  - The two centres with the smallest margin, $0.0381717$, were treated as "margin" cases. That gives $\delta\le0.0381717/\varepsilon=0.161698$, slightly less than the stated $0.1617$.
  - Both of these centres satisfy the exact tangency identity of Lemma 2. So do six more, 12 in all. The binding margin of the remaining 14 is $0.503017$, valid for $\delta\le2.1308$.
  - For $\delta>3\varphi-4\approx0.8541$ the domain $U_3(r)$ is empty, so the theorem holds for every $\delta\ge0$.

  **Fixed**: the statement, the count and the proof now say this.
- **Theorem 4, Corollary 5 and Lemma 6** are correct as written.
- **Small corrections in §4.2.** The half-plane variant holds for $\delta\le0.1408$, not $0.1411$. The $w_1$ failure region starts at $|X|\approx1.011$–$1.014$, not $1.017$. **Fixed.**

Reproduced with my own exact programs:
- the splitting example of §6.2;
- the transport statements, on 117 453 orbit points at six radii and on 27 814 adversarial lattice points at eight radii, with no exception;
- every tangency identity, exactly in $\mathbb Z[\varphi]$;
- every margin used in a proof, by branch-and-bound in exact rational interval arithmetic.

On the big question, my reading is plain. After this note, nothing has been reduced. What stands between the refereed results and (B) is still a uniform bound of (K) type. The atlas idea, as it stands, restates (R2); it does not reduce it. I think the chord-token programme has reached the point where more cycles of the same kind (local transport lemmas plus data) will not close (K) without a new idea (§4).

## 1. Verdicts

| result | verdict |
|---|---|
| Theorem 1(1) ((R) $\Rightarrow$ (R$^\flat$) $\Rightarrow$ (R$^0$), $F=LD+c+2b$) | **correct** (take $F=\lceil LD+c+2b\rceil$ if $L,c$ are not integers) |
| Theorem 1(2) ((R$^0$) at all $\delta<\delta_\ast/\varepsilon$ $\Rightarrow$ finiteness for all $r<r_c$) | **correct after minor fixes**: the base wording, and the lattice reduction at non-norm radii (issue 1). Quantifiers, base and coverage of all radii check |
| Theorem 1(3) (uniform additive recursion) | **correct after a minor fix**: the bound is $\max(N_0,5\lvert GG_5(r_\ast)\rvert)+kC$ (issue 1) |
| remark: with $\delta$-dependent constants (R$^0$) is equivalent to (B) | **correct** |
| Lemma 2 (tangent disks) | **correct**; $r=\sqrt{r_c^2-\delta}$ (parent), $r'=\sqrt{r_c^2-\varepsilon\delta}$ (child), needs $0\le\delta\le r_c^2$ |
| Theorem 3 ($w_3$-type tokens) | **correct after a minor fix to the proof** (issue 2); now stated, and proved, for every $\delta\ge0$ |
| Theorem 4 ($w_1,w_2$-type, exact domain, $\delta\le2.79$) | **correct**; every centre, margin, tangency and the two deciding disks re-derived |
| Corollary 5 ($\lvert z\rvert\le0.99$, $\delta\le\tfrac1{10}$) | **correct**; margin $0.0249736$ against $\varepsilon/10=0.0236068$ (it holds for $\delta\le0.1057$) |
| Lemma 6 (letter exchange) | **correct**; checked exactly for all 8 pairs |
| §4.2 (other constraints, failure region) | **two numbers corrected** (issue 3) |
| Computation §6.2 (a token edge that splits) | **reproduced exactly**, including (R1) on all 20 parent components |
| "all images lie in $\lvert y\rvert<0.75$" (§2, §7) | **correct**: $\varepsilon(1+r)<\varepsilon(1+r_c)=0.743369$ |
| Computations 5.1–5.4, 6.1, 6.3, 6.4 | not reproduced |
| Conjectures 7.1, 7.2 | conjectures; nothing here refutes them |

**What the proofs rest on.**
- Theorem 1 rests on:
  - the (T) note's Theorem 4 and Corollary 5(2) (refereed);
  - `sharp-lower-bound-n5.md` Theorem 4.1;
  - orbit and group monotonicity (Lean-checked);
  - the base: the cut-set certificate at $1/55$. Its theorem, `critical-radius-n5.md` Theorem 4.2, is refereed on paper but not proved in Lean.
- Theorems 3 and 4 and Corollary 5 rest on Lemma 2, on exact tangency identities in $\mathbb Z[\varphi]$, and on finitely many margins. I re-derived the margins by two methods (§3.1). They use nothing else.

## 2. Issues

1. **Theorem 1.**
   - *Item 3.* The step gives $D(\varepsilon\delta)\le\max(N_0,D(\delta)+C)$. Iterating from $D(\delta')\le X'=5|GG_5(r_\ast)|$ gives $\max(N_0,X')+kC$. The stated $\max(N_0,X'+kC)$ fails when $N_0>X'$: a child's parent may itself be a small orbit of diameter up to $N_0-1$. This is the same slip the component-graph referee found in that note's Theorem 3. **Fixed**, with the induction written out.
   - *Notation.* The base said "$r'\le r_\ast$", but $r'$ is the child radius throughout the note. **Fixed.**
   - *Lattice orbits.* The step bounds $D$ only over lattice orbits, because (R$^0$) speaks only of them. Corollary 5(2) of the (T) note takes the supremum over all orbits. At a non-norm radius, `sharp-lower-bound-n5.md` Theorem 4.1 closes the gap, and density plus group monotonicity then give every radius. The conclusion was right, but the citation was missing. **Fixed.**
   - *What checks.*
     - Every $\delta<\delta_\ast$ is $\varepsilon^k\delta'$ with $\delta'\in[\delta_\ast,\delta_\ast/\varepsilon)$, and (R$^0$) is used only at $\varepsilon^j\delta'<\delta_\ast/\varepsilon$.
     - $\delta\ge\delta_\ast$ is covered by orbit monotonicity.
     - A connected graph has diameter less than its number of vertices.
     - Children with at most $N_0$ states have diameter less than $N_0$.
   - *The remark.* "$D(\varepsilon\delta)\le D(\delta)+C$ suffices" is right: it gives $D(\delta)\le X+C\lceil\log(\delta_\ast/\delta)/\log\varphi^3\rceil$. For finiteness alone any finite $F_\delta$ suffices, as item 2 says. The remark that this makes (R$^0$) equivalent to (B) is also right.
2. **Theorem 3: the range, and which centres are tangent.**
   - My enumeration of the 26 distinct centres of $W(w_3)$ agrees with the note's 22 margins value for value and in order (§6.5 of the note).
   - The proof's case split was "tangent (identity) or margin". It put the four touching centres in the first case and the other 22 in the second, with $\min m=0.0381717$. That gives $\varepsilon\delta\le0.0381717$, i.e. $\delta\le0.161698$. The theorem claimed $0.1617$, and §4 claimed every margin exceeds its requirement by $1.3\cdot10^{-3}$. Both were slightly false.
   - The exact identity $|c'-\varepsilon c|^2=(1-\varepsilon)^2(3+\varphi)$, i.e. $=48-28\varphi$, holds for **12** of the 26 centres. Among them are the two binding ones, $(3,-4,6,-4)\leftarrow(-1,2,0,0)$ and $(7,-12,10,-6)\leftarrow(-1,2,-4,2)$. So Lemma 2 covers them for every $\delta$.
   - The other 14 have $\min m=0.503017$, at $(1,-2,0,0)$ and $(9,-14,16,-10)$, valid for $\delta\le2.1308$.
   - $U_3(r)$ is empty for $\delta>3\varphi-4=0.854102$. The disks about $(-1,2,-4,2)$ and $(-1,2,0,0)$ are at squared distance $28-8\varphi$ (exact), so they are disjoint once $r^2<7-2\varphi$.
   - So Theorem 3 holds for **every** $\delta\ge0$. That is better than stated, and it is what the note's own method gives with the right classification. **Fixed** in the summary, the statement, the paragraph after it, the proof (§3.3), Table 4.1 and the method paragraph of §4.
   - For $w_1$ the analogous extra identities ($(1,0,0,0)$, $(1,-4,4,-2)$, $(5,-8,8,-6)$) do not change the binding margin $0.660344$. Theorem 4 stays at $\delta\le2.7972$. $U_1(r)$ is non-empty up to $\delta=\varphi+2\sqrt5-3\approx3.09$, so the window $(2.797,3.09]$ is genuinely not covered.
3. **§4.2.**
   - With the half-plane $\operatorname{Im}z\ge-0.85$, the margin is $0.0332400$, and $0.0332400/\varepsilon=0.14081$. So the range is $\delta\le0.1408$, not $0.1411$ ($0.1411\varepsilon=0.03331>0.03324$).
   - The nearest point of the $w_1$ failure region to $0$ lies on the circle $|\varepsilon X-c_a|=r'$ inside $U_1(r)$: $|X|=1.01130$ as $\delta\to0$ and $1.01352$ at $\delta=0.1$. A double-precision grid of step $0.001$ gives $1.0139$ at $\delta=0.1$. The note's "$1.017$" was off in the third digit; this value is not used in any proof.

   **Fixed** (the second value is labelled as not rigorous).
4. **Symmetry in Theorem 4.**
   - For a token $g\cdot w_i$ ($g\in\{\mathrm{id},\nu,\iota,\iota\nu\}$), the deciding disks are $D(g(c_a),r')$ and $D(g(c_b),r')$. That is because $W(g\cdot w_i)=g\cdot W(w_i)$ letter by letter. I checked this against the note's rules $W(t^{-1})=W(t)^{-1}$ and $W(\iota t)=\iota W(t)$ on all twelve words.
   - The inverse route of the note gives shifted centres $c+\varepsilon\tau$. These agree: $c_a(w_1)+\varepsilon\tau=-c_b(w_2)$ and $c_b(w_1)+\varepsilon\tau=-c_a(w_2)$, as they must, since $w_1^{-1}=\nu\cdot w_2$.

   No change needed.
5. **Statements resting on floating point** (none is used in a proof; all are labelled as computed).
   - §4: "50-digit arithmetic, kept if feasible within $10^{-40}$" is a margin argument, not exact arithmetic. It is sound, and my exact interval branch-and-bound (§3.1) confirms every margin used.
   - Also floating point: the corrected failure-region value of §4.2 (50 digits), the lune and coverage percentages of §5.1 (double precision), the cluster description of §5.3 (read off plots, as stated), the annulus fractions of §5.4, the nearest points $|y'|\le0.2217$ of §6.1, and the double-precision "large" label (bounding boxes) used for $\mathcal D$ in §6.1.
   - The exact claims I reproduced really are exact: orbit sizes, components, transport tests, tangency identities.
6. **Lemma 6, a wording point.** "Exactly when … the letter $L'$ …" is right once $L'$ ranges over both letters of the same rotation sense. A path with one connector of the other sense ends on the wrong sheet. Two maps $z\mapsto uz+\text{const}$ with the same $u$ that agree at one point agree everywhere, so the translation must be $v$. No change needed.

## 3. Reproduction

### 3.1 Programs

All are the referee's own, written for this report in Python with exact integers.
- `zq.py`: $\mathbb Z[\zeta]$ in the basis $1,\zeta,\zeta^2,\zeta^3$.
  - Conjugation $(c_0,c_1,c_2,c_3)\mapsto(c_0-c_1,-c_1,c_3-c_1,c_2-c_1)$. $|x|^2$ in $\mathbb Z[\varphi]$, with $\varphi=-\zeta^2-\zeta^3$.
  - The disk test is the exact sign of $r^2-|y\mp1|^2\in\mathbb Q(\varphi)$, with $r^2$ rational in $1,\varphi$.
  - Words act leftmost letter first. This convention reproduces Table 1.1 of the (T) note, the translations $(2,-2,2,-2)$ of $w_1,w_2$, and $(-6,10,-10,6)=\varepsilon\tau(w_1)$ for $W(w_1)$.
  - Pull-back centres are $h_j^{-1}(p_j)$, computed exactly.
- `geo.py`: the note's candidate method (arc ends and farthest points), at 60 digits, for Table 4.1 and §4.2.
  - All 16, 16 and 26 distinct centres and every margin agree with the note to all printed digits. The cuts $-1.05573$ and $-0.96053$ are attained at the corner $-0.691-2.127i$.
- `bb.py`: an **independent** check by branch-and-bound in exact rational interval arithmetic. Centre coordinates are enclosed in rational intervals of width $2\cdot10^{-45}$.
  - A box is discarded if it provably misses a domain disk. It is accepted if $\max|\varepsilon z-c'|^2\le r_c^2-m_{\rm lo}$ provably holds on it. Otherwise it is split.
  - Certified ($m\ge m_{\rm lo}$ for every $z$ of the domain at radius $r_c$):
    - all 14 non-tangent centres of $W(w_3)$ with $m_{\rm lo}=0.503$;
    - the 7 centres of $W(w_1)$, and the 7 of $W(w_2)$, that neither satisfy the identity nor cut, with $0.6603$ (the note's "10 others" also counts 3 centres that satisfy the identity);
    - $c_a$ on $U_1\cap\{|z|\le0.99\}$ with $0.02497$, and $c_b$ there with $0.2722$;
    - $c_a$ on $U_1\cap\{\operatorname{Im}z\ge-0.85\}$ with $0.03323$.

    At most 5 605 boxes per test.
  - Tangency identities are checked as exact equalities in $\mathbb Z[\varphi]$: 12 for $w_3$, 7 for $w_1$, 7 for $w_2$.
- `orb.py`, `tt.py`, `run_tt.py`: exact lifted orbits (breadth-first search over $(y,j)$), the twelve tokens $g\cdot w_i$ with transport words $g\cdot W(w_i)$, union-find token components, and the transport tests.
  - The prediction for a $w_3$-type token is "always". For a $w_1,w_2$-type token it is "iff $\varepsilon X\in D(g c_a,r')\cap D(g c_b,r')$", tested exactly.
  - For Corollary 5, "both ends in $|z|\le0.99$" is tested exactly ($|x|^2\le0.9801$ in $\mathbb Q(\varphi)$).
  - Every success was also checked to end at $\varepsilon t(X)$.
- Orbit sizes were cross-checked with a copy of `tdcsg-orbit` (40 and 665 points).

### 3.2 The splitting example (§6.2)

- At $\delta=1/16$ the parent $r^2=(47+16\varphi)/16$ and the child $r'^2=(51+14\varphi)/16$ check, from $r'^2=r_c^2-\varepsilon/16$ with $\varepsilon=2\varphi-3$.
- Parent seed $(250,102,91,257)$: 40 states (40 points, engine agrees). Child seed $(-711,387,-680,-51)$: 665 states (engine agrees).
- $X=(167,-93,160,11)$ is in the parent. $\iota w_2=ABABB$ acts at $X$ and gives $Y=(171,-91,160,15)$, with $|Y|=1.8518$.
- $\varepsilon X$ and $\varepsilon Y$ are both in the child, in token components of **46 and 3** states. These are different components, so no token path joins them.
- $W(\iota w_2)$ does not act at $\varepsilon X$.
- The child point nearest $0$ is $(-1060,-434,-387,-1089)$, $|y'|=0.1334$. Its $\varepsilon^{-1}$-preimage lies in the 40-point parent, so this is the parent the note's procedure picks.
- With $\mathcal D$ all 20 parent components (all have images) and $\kappa$ the plurality map, (R1) holds on all 400 ordered pairs. The child has 225 components.

All as stated.

### 3.3 Sample tests of Theorems 3, 4 and Corollary 5

**On orbit points.** Every point of each orbit, every token acting there (exact), with an exact test of the transport word at $\varepsilon X$ at the child radius. Random seeds were lattice points within $2\cdot10^{-7}$ of a uniform point of $D_1\cup D_2$, with coefficients up to about $2\cdot10^6$.

| $\delta$ | orbits (points) | $w_1,w_2$-type edges (word acts) | $w_3$-type edges (word acts) | Corollary 5 edges | mismatches |
|---|---|---|---|---|---|
| $1/10$ | orbit of 0 + 15 random (20 430) | 24 508 (13 272) | 2 550 (2 550) | 3 688, all transport | 0 |
| $\varepsilon/10$ | orbit of 0, level 1 (30 165) | 37 296 (20 112) | 4 140 (4 140) | 5 884, all transport | 0 |
| $1/16$ | §6.2 parent + 15 random (56 342) | 69 048 (37 308) | 7 492 (7 492) | 10 704, all transport | 0 |
| $4/25$ | orbit of 0 + 15 random (9 669) | 11 320 (6 100) | 1 104 (1 104) | — | 0 |
| $2$ | 19 random (410) | 260 (16) | none ($U_3=\varnothing$) | — | 0 |
| $21/10$ | 24 random (437) | 292 (0) | none | — | 0 |

**Adversarial.** For each of the twelve tokens and each radius, lattice points were placed at distance $10^{-6}$ to $10^{-1}$ (log-uniform) from one of the following:
- a random point of a relevant circle: the token's domain circles, the deciding circles $|\varepsilon z-gc|=r'$, every circle of the transport word, and $|z|=0.99$;
- one of their pairwise intersections, which include the tight corners $E$, $-\varepsilon E$, $-F$ and $-\sqrt5E$.

Only points where the token acts were kept: 27 814 points at $\delta\in\{1/1000,\varepsilon/10,1/16,1/10,4/25,2,21/10,2.79\}$ (3 200–4 257 per radius, 916 at $2.79$). The results:
- the prediction of Theorems 3 and 4 failed at none of them;
- every transport ended at $\varepsilon t(X)$;
- each of the 2 352 edges at $\delta\le1/10$ with both ends in $|z|\le0.99$ transports.

At $\delta=1/1000$, $w_3$ points within $10^{-6}$ of the touching corners pass, as Lemma 2 says they must.

**Images in $|y|<0.75$.** This needs no computation. A point of a non-trivial orbit lies in $D_1\cup D_2\subseteq\{|y|\le1+r\}$, so $|\varepsilon y|\le\varepsilon(1+r_c)=0.743369$.

**Not reproduced:** Computations 5.1–5.4 (connector words, success region, births), 6.1, 6.3 and 6.4, and the 886-word coverage in §5.2.

At most three processes ran at once.

## 4. Assessment

**What now stands between the refereed results and finiteness for every $r<r_c$.**

Refereed and proved:
- $GG_5(r)$ is finite iff $D(r)<\infty$ (the (T) note);
- (B) follows from any recursion $D(\varepsilon\delta)\le F_\delta(D(\delta))$ (Theorem 1). But such a recursion, with $\delta$-dependent constants, *is* (B). Theorem 1(2) is a correct reformulation, not progress;
- the local transport of every token edge, with explicit regions (Theorems 3, 4, Corollary 5);
- the algebra of connector images (Lemma 6).

What is missing is one statement with **uniform** constants. Either:
- (K): $D(\delta)\le K_0$ for small $\delta$; or
- the additive recursion $D(\varepsilon\delta)\le D(\delta)+C$ for children with more than $N_0$ states, with $C,N_0$ fixed.

To get the second from (R$^\flat$), all four of the following are needed, and none is proved:
1. connector-edge transport (computed, with a cell-decomposition proof plausible);
2. the global part of (R1): the images of a component concentrate in one child component, and shortest parent paths can be taken through transported states. The data show 4%–20% spill, and §6.2 shows a split;
3. (R2) with fixed $b$;
4. a separate uniform radius bound for children whose parents are all dust (the component-graph report's counterexamples).

Items 3 and 4 are themselves uniform radius bounds of the component graph, relative to the image skeleton or absolutely. Every child component outside $|y|<0.75$ is born, so (R2) is a statement about the child dynamics on all of $D_1\cup D_2$. That is (K) in a relative form. So the gap after this note is (K), in essentially the same form as before it. The note says this honestly in §7 and §8.

**The atlas of $\pm\varepsilon$ charts: a restatement as it stands, not a reduction.** It has two parts:
- the per-chart transport lemmas. These would be finite and of the kind proved here;
- a covering statement: every child state is within bounded connector distance of some chart image, and overlapping chart images are joined at bounded distance, with the number of chart patches along any path bounded independently of $\delta$.

The second part is the whole content of (R2). It is a uniform bound on how far the child orbit's component graph reaches from a skeleton, and nothing in the atlas makes it finite. The data point the same way:
- 30 charts cover 80% of one child orbit, and the last charts add little;
- the parents of different charts are different orbits, so bounded diameters of parents add up along a chain of charts unless the chain length is uniformly bounded, which is (K) again.

A finite atlas would become a reduction only if the covering could be proved from physical position alone, uniformly in $\delta$. No mechanism for that is offered.

**Is the chord-token programme at the point where more cycles of the same kind will not close it?** I think yes.
- The pattern of the last cycles is constant: chaining, the component graph and (R), and now graph renormalization. Each produces true local statements, often proved cleanly, as here. Each then ends with a global statement equivalent to a uniform bound on the depth of the component graph.
- (T) was closed by a genuinely new device, the fence. Nothing comparable exists for connectors, and the (T) note explains why the fence does not transfer.
- More transport lemmas, more charts or more child-first data will sharpen the picture. On present evidence they will not produce the missing uniform bound.

A new idea is needed. Two seem worth exploring; I have not tested either.
1. **Renormalize the finite certificate objects, not orbit graphs.** The cut set $K(r)$ of `certificates.md` is finite at $1/55$. The tangency mechanism of Lemma 2 (circles at $\delta$ go to circles at $\varepsilon\delta$, tight corners stay tight, margins scale) is exactly what a $\delta$-parametric statement needs: "$K(\varepsilon\delta)$ is $\varepsilon K(\delta)$ together with finitely many explicitly described arc families, for all $\delta\in(0,\delta_0]$". That is the shape of renormalization proofs for piecewise isometries: an induced first-return map on a subdomain, conjugate by a scaling to the original system, verified by a finite computation. If it held, it would prove (B) directly and avoid (K).
2. **A conserved or monotone quantity for connectors**, playing for sheet changes the role the fence plays for token indices. This would attack (K) head-on. I see no candidate in the present data.

## 5. Suggestions

1. Make the tangency identity, not "touching", the case criterion everywhere it is used, as now in Theorem 3. Check whether Theorem 4's range $2.797$ can be extended to the emptiness threshold $\varphi+2\sqrt5-3\approx3.09$ by the same reclassification or a finer domain bound. This is cosmetic: only small $\delta$ matters.
2. Before more graph-level work, test idea 1 of §4 on data. Compute the cut sets $K(r)$ at $\delta=1/55$ and $\varepsilon/55$ with the engine, map the first by $\varepsilon$, and see whether the difference is a bounded, explicitly describable family of arcs. This is a medium-sized computation with the existing `certify` program. It was not run here, because `certify*` runs were excluded from this review.
3. Keep the §6.2 example as a regression test for any future claim about token edges near the boundary of the success region.
