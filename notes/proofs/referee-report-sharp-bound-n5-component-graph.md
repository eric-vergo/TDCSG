# Referee report: `sharp-bound-n5-component-graph.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: the token-component graph, one hub per sheet, and its transport by $\varepsilon$" (`sharp-bound-n5-component-graph.md`, commit `3b59815`).

Companions consulted:
- the chaining note and its referee report (definitions, Proposition 6);
- `sharp-bound-n5-token-components.md` ("the (T) note"). It was refereed in parallel and found correct after minor fixes. Here its Theorem 4 and Corollary 5 are treated as cited hypotheses;
- the critical-renormalization note and the orbit-of-zero note;
- `sharp-bound-n5-conjugate.md` Lemma 1 and `sharp-lower-bound-n5.md` Theorem 4.1;
- `boundary-contact.md` Theorems 3.1 and 3.4, and `critical-radius-n5.md` Lemma 4.1;
- `../certificates.md` and `../engine.md`.

## Summary

The proofs are sound. Every line was checked and every constant re-derived.
- Lemma 1, Lemma 2 and Proposition 1 are correct as written.
- Theorem 3 is correct after two small fixes.
  - The bound should be $\max(N_0,5|GG_5(r_\ast)|)+2bk$. The stated $\max(N_0,5|GG_5(r_\ast)|+2bk)$ fails when $N_0>5|GG_5(r_\ast)|$, because a parent can itself be a small orbit.
  - $D$ must be the supremum over *lattice* orbits, since (R) speaks only of lattice orbits.
- With these fixes, (R) at every $\delta<\delta_\ast/\varepsilon$ gives finiteness at every $r<r_c$. The argument goes through non-norm radii and group monotonicity. It does not need to be run only along the sequence $\delta_\ast\varepsilon^k$.

The main mathematical finding concerns what (R) says. If $N_0$ and $b$ may depend on $\delta$, then (R) holds at $\delta$ whenever $D(\varepsilon\delta)<\infty$: take $\mathcal D$ to be one component. Over all $\delta$, together with the base, it is then equivalent to (B). So all of its content is that $b$ is fixed. With $b$ fixed, (R) sits between "every component graph has radius $\le b$" and "$D=O(\log 1/\delta)$". It is a genuine weakening of (K), but not a different kind of statement.

The independent reproduction confirms the following.
- All the exact diameters checked: levels 0–3 of the orbit of $0$ (6, 6, 7, 8), the $1/55$ witness (9), rows 6, 7, 8 (9, 9, 9), the $1/30$ witness (6) and row 10 (8).
- The hub structure on eleven orbits.
- The transport statistics for $\varepsilon$ on every pair tried.

Four claims needed correction.
1. **Token edges do split for $\varepsilon^2$.** It is 4 of 694 at $0\to2$ and 204 of 14 850 at $1\to3$. The author's own raw counts show this too. The note said "no exception" for $\varepsilon,-\varepsilon,\varepsilon^2$. **Fixed.**
2. **The one "merge to distance 0" of connector edges is an artifact.** So are the one birth at distance 2 and one of the three coverage values 4. All three come from a single random pair at $1/30$ whose orbits have five states per point. There the program chose an arbitrary lift of each image. With the sheet-preserving lift $(y,j)\mapsto(\varepsilon y,j)$ the values are 1, 1 and 3. **Fixed**, and the lift is now part of the definition of $\kappa$.
3. **Conjecture 5.1 is false as stated.** Some child orbits at $\varepsilon/55$ and $\varepsilon^2/10$ have 155 to 1 757 states (more than $N_0=40$), but every parent orbit with more than one state has no large component. There $\mathcal D=\varnothing$. Taking $\mathcal D$ to be all components does not rescue it, because (R1) then fails. One repair passes every test made here (§4).
4. **Small items.** The constant of Conjecture 5.2 is $1\,244/\delta$ for $\delta\le1/30$, not $1\,266/\delta$ for $\delta\le1$. An image fraction range was too narrow. A citation was vague ("Part I"). A sentence about dust was a non sequitur. **All fixed.**

## 1. Verdicts

| result | verdict |
|---|---|
| Lemma 1 (component of $n$ states has internal diameter $\le9.960(n-1)$) | **correct**; $2\varphi^2\cdot1.902113=9.9596$ |
| Proposition 1(1), (K$'$) $\Rightarrow M\le2((K_0+1)C_T+1.903K_0)$ | **correct** |
| Proposition 1(2), (K$_s$) | **correct**; the count "$\le K_2+1$ small segments" and the constant $K_2(1.903+9.960(s_0-1))+9.960(s_0-1)$ check |
| Proposition 1(3) (no uniformity in $\delta$ needed) | **correct after a citation fix** ("Part I Lemma 1" is now `sharp-lower-bound-n5.md` Theorem 4.1). Quantifiers: a bound at that $r$ over all *lattice* orbits, at a *non-norm* $r$; norm radii by monotonicity (§2, issue 2) |
| remark after Lemma 1 (dust) | **correct after a minor fix**: "depth at most 3" does not bound visits; the diameter does |
| Lemma 2 (long passages reach the tube) | **correct**; all constants re-derived: $\lvert E\rvert\sin36^\circ=(5-\sqrt5)/4$, $s^\ast=-1.170820h$, and $\tfrac{5-\sqrt5}4\cdot\varphi^3/\sqrt5=\varphi^2/2$ exactly |
| Theorem 3 ((R) $\Rightarrow$ (B)) | **correct after minor fixes** (the form of the bound; $D$ over lattice orbits); covers every $r<r_c$ |
| Conjecture 5.1 | **false as stated** (§4); a repaired form survives every test here |
| Conjecture 5.2 | constant **corrected** to $1\,244/\delta$ for $\delta\le1/30$; the statement itself is a conjecture |
| Table 4.1 | **reproduced** on 11 of 18 rows (states, components, large, diameter, $e$(hub), depth), every entry equal |
| Computation 4.2 (hubs, one per sheet, 5-cycle) | **reproduced** on 11 orbits, plus 6 random ones |
| Table 4.3, Computations 4.4, 4.5, 4.7, 4.8 | not reproduced |
| Computation 4.6 (transport) | **reproduced** on 11 named or named-type pairs and 32 random pairs; **corrected** in items 2, 3, 5 (issues 3, 4) |

**What depends on the (T) note.** Its Theorem 4 is used only in three places: the value of $C_T$ in Proposition 1 (the parenthesis and item 3's last sentence), the last step of Theorem 3 ("$D(r)<\infty\Rightarrow GG_5(r)$ finite"), and the constant of Conjecture 5.2. Corollary 5(2) is cited for the same last step and is re-proved by Proposition 1(3). Lemma 1, Lemma 2, Proposition 1(1)–(2) as conditional statements, and the bound on $D$ in Theorem 3 (base, step, induction) do not depend on the (T) note.

**What else Theorem 3 rests on.**
- The base needs finiteness of $GG_5$ at $\delta_\ast=1/55$. That is the cut-set certificate of `../certificates.md`, checked by the engine's checker. Its theorem, `critical-radius-n5.md` Theorem 4.2, is refereed on paper but is not proved in Lean.
- Orbit monotonicity and group monotonicity, `boundary-contact.md` Theorems 3.1 and 3.4 (Lean-checked).
- `critical-radius-n5.md` Lemma 4.1.
- `sharp-lower-bound-n5.md` Theorem 4.1, for the lattice reduction at non-norm radii.

## 2. Issues

1. **The induction bound in Theorem 3.** The step gives $D(\varepsilon\delta)\le\max(N_0,D(\delta)+2b)$, and that is correct: orbits with at most $N_0$ states have diameter at most $N_0-1$. Iterating from $D(\delta')\le X'=5|GG_5(r_\ast)|$ gives $\max(N_0,X')+2bk$, not $\max(N_0,X'+2bk)$. A child's parent may be an orbit with at most $N_0$ states, whose diameter is up to $N_0-1$. So if $N_0>X'$, the bound can be $N_0-1+2b$, which exceeds $\max(N_0,X'+2b)$. At $\delta_\ast=1/55$ this is harmless, because $|GG_5(r_\ast)|\ge111\,107$ (the witness orbit). But the theorem is stated for general $\delta_\ast$ and $N_0$. **Fixed**, in the statement and the proof.
2. **Quantifiers: lattice orbits, non-norm radii.** (R) speaks of lattice orbits, so the step bounds the supremum over lattice orbits only. The base bounds every orbit. The note's §1 wrote $D(r)=\sup_O$ without saying which orbits, and the proof cited Corollary 5(2) of the (T) note, whose $D$ is over the orbits of all points of $\mathbb C$. The conclusion is still right.
   - At a non-norm radius a bound on the lattice word maps bounds all word maps (`sharp-lower-bound-n5.md` Theorem 4.1). Proposition 1(1) with $K_0=D(r)$ and the (T) note's $C_T$ then gives $M(r)<\infty$.
   - Norm radii follow by density and group monotonicity (Proposition 1(3)). Theorem 3 gives a lattice bound at *every* $\delta<\delta_\ast$, so the nearby non-norm radii needed are available.
   - So the theorem covers all $r<r_c$, not only the sequence $\delta_\ast\varepsilon^k$: every $\delta<\delta_\ast$ is $\varepsilon^k\delta'$ with $\delta'\in[\delta_\ast,\delta_\ast/\varepsilon)$, and (R) is assumed at every $\delta$ in $(0,\delta_\ast/\varepsilon)$. Radii with $\delta\ge\delta_\ast$ follow by group monotonicity, as the note says.

   **Fixed** (definition of $D$, wording of the proof).
3. **$\varepsilon^2$ splits token edges.** My counts are as follows. At $0\to2$, 694 token edges have both images; 690 go into one child component and 4 split. At $1\to3$ it is 14 646 and 204. In every split, one image lies in a hub and the other in a component of 43 or 46 states. The author's raw output agrees once the directed counts are halved: same + missing = $1\,540\ne1\,548$ at $0\to2$, and $32\,408\ne32\,816$ at $1\to3$. For $\varepsilon$ and $-\varepsilon$ there is no exception on any pair, the author's or mine. **Fixed** in the summary and Computation 4.6(2). The rest of the note uses only $\varepsilon$, so nothing else is affected.
4. **The lift of the image, and an artifact.** The note's `kmap` looked up $\Phi(y)$ in the child "any lift". On orbits with one state per point that is the only lift. Some orbits have five states per point, because the lifted orbit visits every point in all five sheets. I found such orbits at $1/55$ and $\varepsilon/55$ (20 995 and 252 725 states), and the author's random run at $1/30$ contains one (seed $(-55,-10,-28,-44)$, 18 180 states, child 252 050). On these, "any lift" picks one sheet for every image, and $\kappa$ collapses. I reran that pair with the lift $(y,j)\mapsto(\varepsilon y,j)$:
   - the 9 680 connector edges map to distance 1, not 0;
   - $\kappa$ sends adjacent components to adjacent ones (distances $1\to1$, $2\to0$ or $2$, $3\to1$);
   - births are within 1 of $\kappa(\mathcal D)$, not 2, and coverage is 3, not 4.

   On the 20 995-state pair the sheet-preserving lift gives (R1) with 0 violations and $b=2$. "Any lift" gives every distance 0. So the note's exceptional "merge", its one birth at distance 2 and one of its three coverage values 4 were artifacts. **Fixed**: §1 now defines the image of a state as $(\Phi(y),j)$, and Computation 4.6(3), (5) are corrected.
5. **Conjecture 5.2's constant.** $2(7\cdot88.8/\delta+6\cdot1.903)=1243.2/\delta+22.84$. That is not at most $1266/\delta$ for $\delta\le1$ ($1266.04$ at $\delta=1$). Also $88.8/\delta$ is the (T) bound only for $\delta\le\tfrac25$. For $\delta\le1/30$ the value is $\le1\,243.96/\delta$. **Fixed** to $1\,244/\delta$ for $\delta\le1/30$. With the sharper $72.07/\delta+41.82$ it would be about $1\,028/\delta$.
6. **Small items.**
   - The image fraction on random parents with at least $10^4$ states reaches $0.6802$ (89 371 states), against the stated range $0.6783$–$0.6797$. **Fixed.**
   - "Part I Lemma 1" is undefined in this note. **Fixed.**
   - "Whether dust is visited boundedly often … in the data it is (depth at most 3)." Depth measures distance to the large set, not visits. What bounds visits on a shortest path is the diameter ($\le9$). **Fixed.**
7. **"Large" depends on the frame.** "Large" is defined by the bounding box of $V=\zeta^{-2j}\sigma y$, and $j$ is counted from the seed's sheet. So the class depends on which point of the orbit is the seed. The $1/55$ witness has 15 large components from the seed $(470,202,166,493)$ and 18 from $(-500,-26,-293,-335)$, a point of the same orbit. The depth changes from 3 to 2. The note mentions the factor $\sqrt2$ for extents (§4.5), but $\mathcal D$ in Conjecture 5.1 is defined through "large". Not fixed in the note, because it changes the conjecture. A frame-free measure, such as the diameter of the component's $V$-set, would remove it. All my comparisons with the note use the note's seeds.
8. **Where the edge statements stop short of (R1).** §5 of the note proposes to prove (R1) by transporting token edges and connector edges. That is not enough for the plurality map. The transported states of one large parent component usually fall into *several* child components. On my pairs this held for 4 to 24 of the large components per pair, with up to 20% of a component's transported states outside its plurality. Two things are missing:
   - the edge statements say nothing about which child component is the plurality;
   - a shortest parent path between two large components passes through small components, which may have no transported state at all.

   A proof of (R1) from edges needs a further statement: either the transported states of each large component lie in one child component up to a bounded set, or a shortest path can be chosen through transported states. Recorded here; the note's plan is left as is.

## 3. Reproduction

### 3.1 Program

`rk.c` (C, exact). The referee's own code, written for this report. The author's `lineK/` outputs were read only afterwards, to resolve the discrepancies in issues 3 and 4.
- Points are integer 4-vectors in the basis $1,\zeta,\zeta^2,\zeta^3$.
- The closed-disk test is the exact sign of $r^2-|y\mp1|^2\in\mathbb Q(\varphi)$, with 128-bit integers. $r^2=(A+B\varphi)/Q$ is given exactly.
- The rotation sense was fixed by checking that $w_1=AABAB$ translates by $2\varphi^{-1}E=(2,-2,2,-2)$ and $w_3$ by $-2\varphi^{-2}E$.
- Lifted states are $(y,j)$, found by breadth-first search. The letter table is exact.
- Tokens are the six words $AABAB$, $ababb$, $abaBAB$ and their conjugates $aabab$, $ABABB$, $ABAbab$. The other six are their inverses and give the same undirected edges. Components are found by union-find.
- The component graph uses every letter move between distinct components. Every edge was checked to change the sheet by $\pm1$.
- The exact diameter is computed by iFUB from the largest component, with 64-way bit-parallel breadth-first searches.
- Transport: $\Phi(y)=uy$ by exact multiplication; the image state is $(uy,j)$; token and connector edges are counted; $\kappa$ is the plurality map; (R1) is checked on all ordered pairs; (R2) by a multi-source breadth-first search from $\kappa(\mathcal D)$ and from all components containing an image.
- $\mathcal D$ can be chosen as the large components (the note), all components, or the components with at least $s$ states.
- A parent search lists the distinct parent orbits $O_\delta(\varepsilon^{-1}x)$ over the child points $x$ with $|x|<\rho$.

**Double precision.** Physical radius filters, $V$, the bounding boxes and the "large" threshold are double precision, used only to select and label, as the note says. Everything presented as exact here is exact: orbit sizes, components, graph distances, diameters, hub sheets and adjacencies, edge-transport counts, $\kappa$, and the (R1) and (R2) counts. Orbit sizes were cross-checked with `tdcsg-orbit` (111 107; 400 519; 40; 1 757; 50 545 points, the last with 5 states per point).

### 3.2 Named orbits

| orbit | states | comps | large | diam (exact) | $e$(hub) | depth | hubs one per sheet, 5-cycle |
|---|---|---|---|---|---|---|---|
| $0$, level 0 | 1 433 | 447 | 19 | 6 | 3 | 2 | yes, yes |
| $0$, level 1 | 30 165 | 9 553 | 23 | 6 | 4 | 2 | yes, yes |
| $0$, level 2 | 400 519 | 126 165 | 11 | 7 | 4 | 3 | yes, yes |
| $0$, level 3 | 5 673 561 | 1 787 929 | 15 | **8** | 4 | 3 | yes, yes |
| $1/55$ witness | 111 107 | 34 750 | 15 | 9 | 5 | 3 | yes, yes |
| row 6 | 1 448 901 | 455 528 | 14 | 9 | 5 | 3 | yes, yes |
| row 7 | 1 467 539 | 461 690 | 16 | **9** | 5 | 3 | yes, yes |
| row 8 | 20 057 921 | 6 321 176 | 20 | **9** | 5 | 3 | yes, yes |
| $1/30$ witness | 54 210 | 17 021 | 21 | 6 | 4 | 2 | yes, yes |
| row 10 | 747 936 | 235 591 | 15 | **8** | 5 | 3 | yes, yes |
| $\varepsilon\cdot(437,-36,293,235)$ | 925 886 | 291 645 | 19 | — | 5 | 3 | yes, yes |

Every entry equals the note's. The new exact values (bold) are confirmed. Row 8 took 22 s and 2.5 GB. Further checks:
- The hub sizes at level 2 ($42\,106^{\times2}$, $37\,946^{\times2}$, $21\,779$) and on row 10 ($76\,857^{\times2}$, $76\,743^{\times2}$, $76\,736$) agree with Computation 4.2(1).
- Every other large component is within 1 of the five hubs, and within 2 on the $1/55$ witness, as in 4.2(4).
- No component graph has an edge that keeps the sheet.
- Every lifted orbit in this table has one state per point.

### 3.3 Transport by $\varepsilon$ (and $-\varepsilon$, $\varepsilon^2$) about 0

$\mathcal D$ = large parent components, with the sheet-preserving lift.

| pair | image fraction | token edges, both images: same / split | connector edges large–large: child distance | (R1) ordered pairs / violations | max $d(\cdot,\kappa\mathcal D)$ | births, max distance |
|---|---|---|---|---|---|---|
| $0\to1$ | 0.6790 | 566 / 0 | 796 at distance 1 | 342 / 0 | 3 | 14, 1 |
| $1\to2$ | 0.6785 | 12 150 / 0 | 15 476 at 1 | 506 / 0 | 3 | 0 |
| $2\to3$ | 0.6797 | 162 446 / 0 | 200 980 at 1 | 110 / 0 | 3 | 4, 1 |
| $1\to2$, $-\varepsilon$ | 0.6785 | 12 150 / 0 | 15 476 at 1 | 506 / 0 | 3 | 0 |
| $0\to2$, $\varepsilon^2$ | 0.7739 | 690 / **4** | 1 092 at 1 | 342 / 0 | 3 | 2, 1 |
| $1\to3$, $\varepsilon^2$ | 0.7753 | 14 646 / **204** | 21 408 at 1 | 506 / 0 | 3 | 4, 1 |
| $1/55\to$ row 6 | 0.6792 | 45 080 / 0 | 57 540 at 1 | 306 / 0 | 3 | 2, 1 |
| $1/30\to\varepsilon\cdot1/30$ | 0.6783 | 21 912 / 0 | 28 080 at 1 | 420 / 0 | 4 | 14, 1 |
| $1/30$, seed $(-55,-10,-28,-44)$, 5 lifts | 0.6788 | 7 400 / 0 | 9 680 at 1 | 90 / 0 | 3 | 5, 1 |

- The $1/55$ pair used the seed $(-500,-26,-293,-335)$, so its large set (18) differs from the note's (15). The distance matrices of the other pairs equal the author's exactly (for example $1\to1{:}66$, $2\to0{:}28$, $2\to2{:}144$, $3\to1{:}80$, $3\to2{:}16$, $4\to0{:}8$ at $0\to1$).
- On every pair, the sheet is preserved on every transported state, every large component has images, $\kappa$ is large-to-large, and $\kappa$ preserves the sheet.
- On every pair, the images of some large components are spread over more than one child component: 4 to 24 of the large components per pair, with plurality shares $\ge0.80$.

**Random pairs, parent first** (as in the note). Seeds: a physical point uniform in $|y|<0.9$, internal point uniform of modulus $\le8/\delta$, rounded to $\Lambda$; 8 parents at $1/55$, 4 at $\varepsilon/10$. Seven have large components (1 745 to 89 371 states). On all seven: token edges 0 split, connector edges all at distance 1, (R1) 0 violations, $b\le3$, births within 1. Five are 40-state parents with no large component. One of them has a child with **252 725** states. That child has a different parent (20 995 states, 8 large components) for which (R1) holds with 0 violations and $b=2$.

**Random pairs, child first** (the direction (R) quantifies). Seeds: 12 children at $\varepsilon/55$ and 8 at $\varepsilon^2/10$, physical point uniform in $D_1\cup D_2$, internal modulus $\le8/\delta$. For each child, every parent orbit $O_\delta(\varepsilon^{-1}x)$ over child points with $|x|<0.6$ was listed, and the largest was used. For the nine children below, the search was then widened to $|x|<2.2$. That covers every parent with more than one state: for $|x|>(1+r)\varphi^{-3}\approx0.742$ the point $\varepsilon^{-1}x$ lies outside $D_1\cup D_2$ and is fixed.
- 2 children have no parent candidate (17 and 21 states).
- 5 have 40 states.
- 4 have large components (98 552 to 1 159 301 states). Each has a parent with large components, (R1) with 0 violations and $b=3$.
- **9 children have 155 to 1 757 states, and each has exactly one parent orbit with more than one state** (25, 40 or 155 states). None of these parents has a large component. This is §4.

Sample sizes: 9 named and named-type pairs, 12 parent-first and 20 child-first random pairs, and 5 extra runs of $\mathcal D$ variants. Total memory never exceeded 2.5 GB.

**Not reproduced:** Table 4.3 (878 orbits), Computations 4.4 (tube), 4.5 (type graph), 4.7 (failure region), 4.8 (transport words), and the orbits of $E$ and of $-\zeta^2$.

**Sampled or capped claims.**
- Table 4.3 and the "0 violations in 118 pairs" are samples. They are labelled as computed, which is right.
- The random pairs of the note were sampled parent first. That tests whether images behave well. It does not test (R), which asks that every child have *some* good parent. The child-first test above is the one that found the failure of Conjecture 5.1.
- The 5 orbits marked $\ge7$ at $\varepsilon^3/10$ are capped, as stated.

## 4. Assessment of (R)

**Well-posedness.** With the fixes, (R) as a hypothesis of Theorem 3 is well posed. $\mathcal D$ is any set of components, and $\kappa$ any map, so components without a transported state are simply left out of $\mathcal D$. For the specific $\kappa$ of Conjecture 5.1, three things had to be fixed: the lift of an image (issue 4), a tie rule, and the domain (components with at least one image). All three are now in §1 of the note. "Large" remains frame-dependent (issue 7).

**The content of (R) is the uniformity of $b$.** If (R) is allowed $\delta$-dependent constants, any child $O'$ satisfies it with $\mathcal D$ one component and $b=\operatorname{rad}\mathcal C(O')$. So (R) at $\delta$ follows from $D(\varepsilon\delta)<\infty$, and over all $\delta$ it is equivalent to (B). With $b$ fixed:
- uniform radius $\le b$ for orbits with more than $N_0$ states $\Rightarrow$ (R) with that $b$;
- (R) $\Rightarrow D\le\max(N_0,5|GG_5(r_\ast)|)+2bk$.

The remark is now in the note after Theorem 3. It also shows that (R1) has content only together with a small $b$. The degenerate $\kappa$ always satisfies (R1).

**Conjecture 5.1 as stated is false.** Take $O'=O_{\varepsilon/55}((443,379,39,651))$: 1 757 states, 572 components, no large component, exact diameter 6, hub eccentricity 4.
- Among all its points $x$ with $|x|<2.2$, which covers every non-trivial parent (995 candidates, 891 distinct parent orbits), the only parent orbit with more than one state is $O_{1/55}((-145,9,-95,-80))$: 155 states, 45 components, none large.
- So $\mathcal D=\varnothing$ for every parent, and (R2) fails.
- Eight more children behave the same way: 155, 155, 590, 600, 620, 651, 651 and 695 states. Each has a single non-trivial parent, of 25 or 40 states, with no large component. The 651-state child at $\varepsilon/55$ has diameter 8 with no large component.

(R) itself is not refuted. These children have radius at most 4, so the degenerate choice gives $b=4$. But the conjecture's mechanism, large components carried by plurality, says nothing about them.

**$\mathcal D$ = all components does not work either.**
- At $0\to1$, (R1) fails on 284 of 117 306 ordered pairs. Adjacent parent components go to child distance 3: a 3-state component next to a hub goes to a 4-state child component three connectors from the hub's image.
- On the random pair with 70 793 states, 158 660 of $2.8\cdot10^8$ pairs fail.
- On the 40-state parents, 6 to 12 pairs fail.

**A repaired form that survives every test here.** Let $\mathcal D$ be the components with at least 5 states, and $\kappa$ the plurality map with the sheet-preserving lift. On six pairs this gave 0 violations of (R1) and $b\le4$: $0\to1$, $1\to2$, $1/55\to$ row 6, $1/30\to\varepsilon\cdot1/30$, a 70 793-state random pair, and the 155-state parent of the 1 757-state child (there $b=2$). The children whose only parents have 40 states (20 components of 2 states) still need the degenerate choice. So a correct conjecture has two parts:
- (R$'$) with $\mathcal D=\{K:|K|\ge5\}$, for children that have a parent with such a component;
- a separate uniform radius bound for orbits all of whose parents are dust.

In the data that radius is at most 4, and the diameter at most 8.

**(R1) for token and connector edges: plausibly finite.** For $\pm\varepsilon$ the edge statements are local. They say that $X\sim X'$ at radius $r$, with $\varepsilon X$ and $\varepsilon X'$ in the child, implies a short path between $\varepsilon X$ and $\varepsilon X'$ at radius $r'$ (0 connectors for a token edge, 1 for a connector). Proving them needs the local form "for $X$ in an explicit region, a fixed short word acts at $\varepsilon X$". That is a finite cell-decomposition problem in the circles of radii $r$ and $\varepsilon$-rescaled $r'$, of the kind already certified elsewhere in the repository. The note's §4.8 says the $w_3$ word always acts and the $w_1,w_2$ words act on only 54%, so the token case needs a short finite list of alternative words. That is plausible from the lengths 3, 5 and 11+ recorded there. As issue 8 says, these edge statements do not yet give (R1) for the plurality map.

**(R2): not finite as posed; it is the old difficulty.** (R2) quantifies over every child orbit and every component in it. About 92% of a child's states are not images, and they lie in components that the parent does not see. Bounding their distance to the image set is a statement about the dynamics at $\varepsilon\delta$ on the whole disk union. With $\mathcal D$ a single component it *is* the uniform radius bound. The child-first test shows that the parent can be tiny while the child is large (40 states against 252 725). So (R2) cannot be derived from the parent alone. It needs the union of all parents of points of the child, which is the reverse inclusion in another form.

**The most promising provable next statement.** It is a *local* (R1) for $\varepsilon$ about 0. There are explicit compact regions $G_\delta$ (the success region of Computation 4.7, given by finitely many circles) and a finite set of words $W$ with these properties:
1. For every token $g\cdot w_i$ acting at $X$ at radius $r$ with $X$ and $g\cdot w_i(X)$ in $G_\delta$, some word of $W$ made of tokens only maps $\varepsilon X$ to $\varepsilon g\cdot w_i(X)$ at radius $r'$.
2. For every connector letter at $X$ with both ends in $G_\delta$, some word of $W$ with exactly one connector does the same.

This is uniform in $\delta$ after rescaling, local and finite, and it is exactly what the data show for $\pm\varepsilon$ (and fails for $\varepsilon^2$, which is a useful control). Next would come "the transported states of each component with at least 5 states lie, outside a set of bounded size, in one child component". Together these would give (R1) for the repaired $\mathcal D$. (R2) should be attacked separately, as a uniform radius bound relative to the image skeleton. The 5-cycle of hubs and the depth $\le3$ are the structure a proof would have to explain.

## 5. Suggestions

1. **Restate Conjecture 5.1** in the two-part form of §4. Test it child first, with all parents of each child, at least at $\varepsilon/55$, $\varepsilon^2/10$ and $\varphi^{-3}/30$. Also try smaller size thresholds for $\mathcal D$ (3, 4) to locate the true cut-off.
2. **Replace "large"** by a frame-free measure, such as the diameter of the component's $V$-set, so that $\mathcal D$ does not depend on the seed.
3. **Record multi-lift orbits.** Orbits with five states per point are rare but real. In the random runs here, 1 of 60 orbit computations gave one (252 725 states); the parent search found another (20 995 states); and the author's $1/30$ runs contain a third. Their component graphs have the same hub pattern, with all five hubs of equal size. Table 4.3 should say which rows they are, and the transport program should use the sheet-preserving lift throughout. The note's rows other than the one $1/30$ random pair are unaffected.
4. **Prove the local (R1)** of §4 for $w_3$ first. The note's §4.8 data say its transport word acts at every tested state, so it should be a containment of disk intersections with a lune analysis at the tight points.
5. **Measure the plurality shares** and the number of child components hit per large parent component. Issue 8 shows these numbers decide whether edge transport can give (R1).
