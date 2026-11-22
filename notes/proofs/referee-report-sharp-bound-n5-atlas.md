# Referee report: `sharp-bound-n5-atlas.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: an atlas of $\pm\varepsilon$ charts, what it localizes, and the gluing step it cannot reach" (`sharp-bound-n5-atlas.md`, commit `a52f38c`).

Companions consulted:
- the transport note `sharp-bound-n5-graph-renormalization.md` and its referee report (house format; Lemma 2, Lemma 6, the fixed form of Theorem 1);
- the component-graph note and its report (lifted states, sheets, the base of Theorem 3);
- the (T) note (tokens, $\Lambda_T$, Theorem 4, Corollary 5(2));
- the invariant note, Propositions 2 and 3 (the 20 classes, the symmetries);
- `../engine.md`.

## Summary

The proofs are sound. Every line of §3 was checked. The fixes needed are small, with one exception: a computed claim about transitions was wrong.

- **Propositions 1, 2, 4 and Lemma 5** are correct as written.
- **Proposition 3** is correct. Its last sentence needed "of the same sign": two charts of opposite sign can both send one orbit into one class without differing by an element of $\Lambda_T$. **Fixed.**
- **Proposition 6** is correct after a wording fix. "Carves the region $\{\dots\le\varphi^3r'\}$ out of" said the opposite of the proof: the test *keeps* that disk. Also, the three kinds do not cover a margin of exactly $0$ without the tangency identity. That case does not occur in Computation 4.2. **Fixed.**
- **Proposition 7 (lune lemma)** is correct, and its statement is exactly what the proof gives. Its scope is narrower than parts of the note said:
  - it is about one parent word $w$ and one child word $W$ with $\chi(\operatorname{dom}w)\subseteq\operatorname{dom}W$;
  - it does not show that the child relation as a whole (all words) strictly contains a chart image of the parent relation, because another parent word could cover the lune.

  **Fixed** in the summary, §2.3, §2.4 and §6 ("word-by-word"). The proof of item 3 also gained one missing step (the inclusion at $\delta=0$), and $N_0$ was renamed $\Omega_0$ there, because $N_0$ is a constant of Theorem 8.
- **Theorem 8** is correct after minor fixes:
  - (A4)–(A6) must use image states $\chi(x)$ with $x\in G_\chi$, since that is all item 1 controls;
  - the case $L=1$ of the closed form needed a word;
  - Theorem 8 needs its hypotheses on $(0,\delta_\ast/\varepsilon)=(0,\varphi^3/55)\approx(0,0.0770)$, but Conjecture 9 was stated for $\delta\le1/30$. So "Conjecture 9 implies (B)" did not follow. The conjecture's range is now $0<\delta<\varphi^3/55$.

  The multiplicative recursion with $L>1$ does give a finite bound at every fixed $r$, which is all that (B) needs. The base and the $\max(N_0,\cdot)$ check out (issue 4).
- **Computation 4.4, transitions: wrong as stated. Fixed.** The note said that a parent state good for several charts always has its images in *different* child components, "never 0", and hence that transitions are never free. In fact every parent state is good for at least 3 good charts, and for $10\,009$ of the $30\,165$ states all of these images lie in one child component, so the transition costs $0$. The "never 0" came from sampling only the states that have at least two distinct image components. On all $20\,156$ such states the largest mutual distance is $2$ ($19\,952$) or $4$ ($204$). Theorem 8 is unaffected.
- **Spread (A4).** Measured from the plurality component, the chart-$0$ pieces are at distance $\le2$, as the note says. (A4) is stated pairwise, though, and pairwise two pieces can be $4$ apart (15 of 89 components at $1\to2$). So Conjecture 9's $s=2$ did not match its own evidence. **Fixed** to $s=4$, with a remark that $G_\chi$ is unspecified.

Reproduced with my own exact program:
- the pointwise census of §4.1;
- the coherence census of §4.3;
- the transitions (all states, not a sample) and the spread of §4.4;
- the gluing table of §4.6 at all three levels, and 13 random children.

All agree with the note to the last digit, except for the transition claim above. Orbit sizes were cross-checked with the engine.

On the big question:
- **The atlas does not reduce (K).** I agree with this verdict.
- **It is an assessment, not a proof.** Proposition 7 shows that chart images of parent words never exhaust the child words. It does not show that (A5)–(A6) cannot be proved from local, child-side statements. The note now says so.
- **Idea 47 is the better next step.** It can be made precise: with the rim graph defined in §4, $D(\varepsilon\delta)\le(R+1)D(\delta)+R$, where $R$ bounds the diameter of the rim graph. Coverage is then automatic, and there is no chart and no choice of regions. On the orbit of $0$ the rim graph has diameter exactly $12$, $14$, $14$ at levels $1$, $2$, $3$ (§4).

## 1. Verdicts

| result | verdict |
|---|---|
| Proposition 1 (centred charts $=\chi_{\pm\varepsilon,t}$, $t\in2\Lambda$, unique centre) | **correct** |
| Proposition 2 (charts normalize $\Gamma$, $u\Lambda_T=\Lambda_T$, translations $u\tau$) | **correct** |
| Proposition 3 (labels, class map, one coset per sign) | **correct after a wording fix** ("of the same sign" in item 3) |
| Proposition 4 (minus-charts via $-O$; $\chi_{u,t+us}(x)=\chi_{u,t}(x+s)$) | **correct** |
| Lemma 5 (distances $0,2,4$ or $\ge5$ within a sheet) | **correct** |
| Proposition 6 (per-chart transport is a finite cell problem) | **correct after wording fixes** (direction of "carves"; the case $m_j=0$ without tangency) |
| Proposition 7 (lune lemma) | **correct**; the statement is what the proof gives. Its reading in the summary, §2.3, §2.4 and §6 was too broad (whole relation instead of one word pair). **Fixed** |
| Theorem 8 (atlas recursion) | **correct after minor fixes** (image states in $G_\chi$; $L=1$; the range of Conjecture 9) |
| "(A5), (A6) cannot be made local" | **evidence, not proof**; now labelled as an assessment |
| Computation 4.1 (pointwise census) | **reproduced exactly** |
| Computation 4.2 (margins for 13 charts) | not reproduced |
| Computation 4.3 (structural census) | **reproduced exactly** for the coherences, the 53 good charts and both coverages; the distance and letter-distance histograms not reproduced |
| Computation 4.4, transitions | **wrong as stated, fixed**: free for $10\,009$ of $30\,165$ states |
| Computation 4.4, spread | **reproduced exactly**; pairwise spread up to $4$ added |
| Computation 4.5 (`lcov`) | not reproduced |
| Computation 4.6 (gluing) | **reproduced exactly** (orbit of $0$, levels 1–3); random children agree on my own sample |
| Computation 4.7 (lunes on the lattice) | not reproduced |
| Conjecture 9 | conjecture. Range and $s$ fixed to match Theorem 8 and the data; $G_\chi$ still unspecified (issue 5) |

**What the proofs rest on.** Theorem 8 rests on:
- the (T) note's Theorem 4 and Corollary 5(2), refereed;
- `sharp-lower-bound-n5.md` Theorem 4.1;
- orbit and group monotonicity, Lean-checked;
- the base, which is the cut-set certificate at $1/55$. Its theorem is refereed on paper but not proved in Lean.

Propositions 1–7 use only the invariant note's Proposition 2 and the transport note's Lemma 2.

## 2. Issues

1. **Propositions 1–4 and Lemma 5: what was checked.**
   - **Proposition 1.** $\varepsilon=2\varphi-3$, $1-\varepsilon=2\varphi^{-2}$, $1+\varepsilon=2\varphi^{-1}$, and $\varphi$ is a unit of $\Lambda$, so $(1\mp\varepsilon)\Lambda=2\Lambda$.
   - **Proposition 2.** $\chi L\chi^{-1}(z)=\omega z+(up+t)(1-\omega)$. $up-p'\in\{\pm2\varphi^{-2},\pm2\varphi^{-1}\}$. For $\chi^{-1}$: $\varphi^3\mp1\in2\mathbb Z[\varphi]$.
   - **Proposition 3.** $\varepsilon=(-3,0,-2,-2)$ has coefficient sum $-7\equiv3\pmod5$, and $\varepsilon\equiv1\pmod2$.
     - The proof shows "into". "Onto" follows from the same computation for $\chi^{-1}$: $\varphi^3=(1,0,-2,-2)$ has residue $2=3^{-1}$ modulo 5 and is $\equiv1\pmod2$.
     - The class count $5\times4=20$ and the coset statement are right.
     - *Fix:* item 3 needs "of the same sign". For $a\ne1$ the images under $+\varepsilon$ and $-\varepsilon$ need different residues of $t$.
   - **Proposition 4.** The map $z\mapsto-z$ exchanges $a$ and $b$ and preserves the rotation index, so it maps lifted orbits to lifted orbits.
   - **Lemma 5.** Token components lie in one sheet, and each connector changes the sheet by $\pm1$. For $k\le4$ connectors, $\sum e_i\equiv0\pmod5$ forces $\sum e_i=0$.
   - **An observation the note can use.** That every chart "keeps the sheet" (§4.1) is a theorem, not only a computed fact, for orbits whose class has $b\ne0$ (for example the orbit of $0$):
     - On such an orbit, $y+1\equiv\zeta^{-j}(y_0+1)\pmod{2\Lambda}$, and $\zeta$ acts freely on $\mathbb F_{16}^\times$. So the sheet $j$ is a function of $y$ modulo $2\Lambda$.
     - By the proof of Proposition 3(2), $\chi(y)+1\equiv y+1\pmod2$.

     My census found no sheet-shifted image among the 8 142 charts, as this predicts.
2. **Proposition 6.**
   - The criterion and the three kinds are right. In particular, the tangent case follows from Lemma 2 by concavity: $\varepsilon r+(1-\varepsilon)r_c\le\sqrt{\varepsilon r^2+(1-\varepsilon)r_c^2}=r'$.
   - The wording said that a cutting test "carves the disk out of" the domain. The proof said, correctly, that what is removed is the *complement* of the disk. **Fixed.**
   - A tangent test has $m_j\ge0$. A test with $m_j=0$ and no tangency identity fits none of the three kinds. It does not occur in Computation 4.2 ("every reported margin is far from 0 except the exact tangencies"). **Fixed** by saying so.
   - Computation 4.2 is 50-digit arithmetic with a $10^{-40}$ candidate tolerance. That is a margin argument, not exact arithmetic, and I did not reproduce it.
3. **Proposition 7.**
   - *What the proof gives.*
     - Item 1 holds as stated. Boundary circles of $\chi^{-1}(V)$ have radius $R=r'/\varepsilon\ge r/\varepsilon>r$, so each meets a circle of radius $r$ in at most two points. Off those points, $\gamma\subseteq U\subseteq\chi^{-1}(V)$ lies in the open disks. $U$ is closed, so $\operatorname{int}\chi^{-1}(V)\setminus U$ is open and non-empty.
     - Item 2 follows for every open set meeting $\partial U$: such a set contains a sub-arc of some boundary arc, hence non-exceptional points.
     - Item 3: the lower bound on the area needs item 1 at $\delta=0$. That needs $\chi(U_0)\subseteq V_0$, which follows from the inclusion at small $\delta>0$: interior points of $U_0$ lie in $U_\delta$ for small $\delta$, $V_\delta\subseteq V_0$, $U_0$ is the closure of its interior, and $V_0$ is closed. It also needs $U_\delta\subseteq U_0$. **Added** to the proof.
     - The numbers check: $R\approx2.149/0.2361=9.10$ and $r\approx2.15$.
   - *What it does not give.* The note read Proposition 7 as "no chart is a local conjugacy" and "the child relation strictly contains every chart image of the parent relation".
     - The lemma is about a fixed pair $(w,W)$. On the lune, some *other* parent word with the same translation could act, and then the parent relation would have the edge after all.
     - So the lemma rules out a word-by-word conjugacy, not a conjugacy of the relations.
     - That the relations really differ is supported by §4.7: $4\,912$ child joins between different parent orbits at $1\to2$. That is computed for chart $0$ near $0$, not proved.

     **Fixed** in five places (summary twice, §2.3 heading and remark, §2.4, §6). The proposition itself is unchanged.
4. **Theorem 8.**
   - *Quantifiers and base.*
     - The hypotheses are used only at parent defects $\varepsilon^j\delta'<\delta_\ast/\varepsilon$, which is what is assumed.
     - The base $D(\delta')\le5|GG_5(r_\ast)|$ for $\delta'\ge\delta_\ast$ follows from orbit monotonicity (at most 5 lifted states per point).
     - *Small parents.* With $X=\max(N_0,5|GG_5(r_\ast)|)$, the induction $B_{k+1}=\max(N_0,LB_k+C)=LB_k+C$ is valid because $L\ge1$ and $B_k\ge X\ge N_0$. So the closed form $L^kX+C(L^k-1)/(L-1)$ is right, and it covers parents that are themselves small orbits.
     - The one slip is $L=1$ (possible only when $m=0$, $\Sigma=0$ and $a=0$), where the last term is $kC$. **Fixed.**
   - *Multiplicative recursion.* At a fixed $\delta=\varepsilon^k\delta'$ only $k$ steps are used, so the bound is finite. That is all Corollary 5(2) of the (T) note needs. The rate $O(\delta^{-\log L/\log\varphi^3})$ is right, and it gives (B), not Conjecture A.
   - *Item 1.*
     - The nerve of the charts meeting a token component $P$ is connected. If $P$ has an edge, every chart meeting $P$ at a state $x$ is adjacent to the chart of an edge at $x$. If $P$ is a single state, the nerve is complete.
     - On a shortest nerve path there are $n+1\le|\mathcal A|$ terms bounded by $s$ and $n$ terms bounded by $\tau$. Each $s$-term compares two points of $P\cap G_{\chi_i}$, as (A4) requires.
     - The chain of connector edges adds $k(1+a)$.
     - So $\Sigma$, $L$ and $C$ are right. Item 2 is right too: $2b+(m+1)[(D+1)\Sigma+D(1+a)]+mg=LD+C$.
   - *Image states.* Item 1 bounds only images $\chi(x)$ with $x\in G_\chi$. (A4) says this, but (A5), (A6) and item 1 said only "image state". If (A6) allowed images of points outside $G_\chi$, item 1 would not apply to them. **Fixed** by a sentence after the hypotheses.
   - *Range of Conjecture 9.*
     - With $\delta_\ast=1/55$, Theorem 8 needs (A1)–(A6) on $(0,\varphi^3/55)\approx(0,0.0770)$.
     - Conjecture 9 was stated for $\delta\le1/30=0.0333$. A defect $\delta<1/55$ whose representative $\delta'$ lies in $(1/30,\varphi^3/55)$ has its first step outside the conjectured range.
     - Shifting the base down to $\delta'\in[\varepsilon/30,1/30)$ instead would need finiteness at $\varepsilon/30\approx0.0079$, which is not certified.

     So "Conjecture 9 implies (B)" did not follow. **Fixed** by stating Conjecture 9 on $0<\delta<\varphi^3/55$. The note's evidence for (A5) and (A6) includes parent defects $1/16$ and $2/45$ in that interval.
5. **Conjecture 9 and the spread.**
   - (A4) asks that the image pieces be *pairwise* within $s$.
   - §4.4 measured the distance from the plurality component. That is at most $2$, which I confirm. Pairwise, though, two minority pieces can be $4$ apart:

     | pair, chart | components | largest pairwise distance 2 | largest pairwise distance 4 |
     |---|---|---|---|
     | $1\to2$, chart $0$ | 89 | 74 | 15 |
     | $2\to3$, chart $0$ | 1 015 split | 1 004 | 11 |
     | $1\to2$, chart $(-10,-6,-2,-12)$, a good chart | 11 split | 4 | 7 |

   - So with $G_\chi=\mathbb C$ the conjectured $s=2$ is already false on the note's own data. **Changed** to $s=4$, with a remark that the regions $G_\chi$ are not specified. Conjecture 9 remains under-specified until $G_\chi$ is defined. With $G_\chi$ the set of good states of $\chi$, (A4) with $s=2$ might hold; I did not test it.
6. **Transitions (§4.4, summary item 3, §6). Wrong as stated; fixed.**
   - I recomputed the good charts and good states exactly as defined in §1.
   - My counts of distinct image components per parent state agree with the note exactly: $10\,009$, $9\,608$, $5\,180$, …, $786$ with seven or more.
   - But every parent state is a good state of at least 3 good charts (median 21). So the $10\,009$ "one component" states are states where several good charts agree up to token moves: the transition costs $0$.
   - The note's "never $0$" was a statement about a sample drawn only from states with at least two distinct components, so it was true by construction.
   - On all $20\,156$ states with at least two, the largest mutual distance is $2$ for $19\,952$ and $4$ for $204$. On every 13th of them it is $2$ for $1\,534$ and $4$ for $17$; the note's sample of $1\,557$, taken in a different order, gave $1\,542$ and $15$.
   - The text now says "transitions cost $0$, $2$ or $4$". Nothing in the proofs depended on this.
7. **The gluing graph.**
   - §4.6 says Theorem 8 charges per step of a gluing graph "whose diameter stays at most 2 here".
   - What was measured is the chart-$0$, near-$0$ part: the distance from the main group to each other group. With $g=1$ that part has diameter $\le2$.
   - The full $\mathcal P(O')$ of (A6), over all charts and all of $O'$, was not computed. **Fixed** wording.
8. **Statements resting on floating point** (none used in a proof; all labelled):
   - the chart filters $|t|\le3.4$ and $|\sigma t|\le40$;
   - the selections $|y'|<0.2$ and $|y'|<0.24$;
   - the position bins of §4.3 and §4.5;
   - the margins of §4.2 (50 digits; issue 2).

   The memberships, components and distances I reproduced really are exact.
9. **Claims resting on samples.** These are labelled as computed, but they are sampled:
   - "every component with no covered state has at most 7 states" (72 random children);
   - the random-children rows of §4.6 (83 children);
   - "about $7\%$ uncovered in every radial bin" (one orbit).

   None is used beyond Conjecture 9.

## 3. Reproduction

### 3.1 Program

- **Language and arithmetic.** One C program written for this report (`atl.c`, with `z5.h` and `orb.h`), sharing no code with the author's.
  - $\mathbb Z[\zeta]$ in the basis $1,\zeta,\zeta^2,\zeta^3$.
  - $|x|^2=P+Q\varphi$ exactly, with $P=\sum c_i^2-s_1$, $Q=s_1-s_2-s_3$, where $s_d$ is the sum of $c_kc_l$ over $l-k=d$.
  - Disk tests use the exact sign of $\alpha+\beta\varphi$, computed with 128-bit integers.
- **Letters and tokens.** $a,b$ multiply by $\zeta^{-1}$ about $\mp1$; words act leftmost letter first.
  - This reproduces the translations $(2,-2,2,-2)$ of $w_1,w_2$ and $(2,-4,4,-2)=-2\varphi^{-2}E$ of $w_3$.
  - The twelve tokens are $g\cdot w_i$, obtained by renaming letters.
- **Orbits and graphs.**
  - Lifted orbits by breadth-first search over $(y,j)$.
  - Connectors are letters that move their point.
  - Union-find token components, and the deduplicated component graph.
- **Charts.** $t=2\lambda$ with $|\lambda_i|\le20$. Images are $(\pm\varepsilon x+t,j)$, looked up exactly, and every other sheet was also looked up.
- **Orbit sizes, cross-checked with a copy of `tdcsg-orbit`:** the orbit of $0$ has $1\,433$, $30\,165$, $400\,519$ and $5\,673\,561$ points at levels 0–3. These orbits have one state per point.
- **Resources.** At most 4 processes at once, peak 1.6 GB.

### 3.2 Results

**Pointwise census (§4.1), orbit of $0$, level $1\to2$.** All as stated.
- 8 142 charts (both signs, all cosets).
- 1 318 have success above $5\%$.
- No chart outside $\Lambda_T$ hits the child at all (Proposition 3).
- No image is sheet-shifted.
- The two signs give identical counts for every $t$.
- The union covers $0.9316$ of the child.

**Structural census (§4.3).** All as stated.
- 801 plus-charts in $\Lambda_T$.
- Exactly one chart has both coherences equal to 1: $t=0$, with $24\,300$ token edges (directed) and $29\,128$ connector edges.
- The next best are $0.9865$ (two charts with $|t|=0.343$) and $0.9712$ (four charts with $|t|=0.555$, among them $(-4,6,-6,4)$, the chart centred at $-F$).
- $t=(2,4,0,4)$ has success $0.6765$ and token coherence $0$.
- 53 good charts.
- Every one of the $30\,165$ parent states is good for some good chart.
- Child coverage: $0.4190$ by the good-chart images, $0.4040$ by the good states' images.

**Transitions (§4.4).** Over all $30\,165$ states, see issue 6.
- Number of good charts per state: from 3 to 42, median 21.
- States whose good images lie in one component: $10\,009$.
- Largest mutual distance among the others: $2$ for $19\,952$ and $4$ for $204$. No other values occur.

**Spread (§4.4).** Components with at least 5 states and an image; plurality shares and distances from the plurality as stated, pairwise distances in issue 5.

| pair, chart | components | unsplit | split, distance from plurality | min plurality share (comps $\ge100$) |
|---|---|---|---|---|
| $1\to2$, $0$ | 89 | 0 | 89 at 2 | 0.800 (0.953) |
| $2\to3$, $0$ | 1 131 | 116 | 1 015 at 2 | 0.800 (0.960) |
| $1\to2$, $(-10,-6,-2,-12)$ | 89 | 78 | 9 at 2, 2 at 4 | 0.971 |
| $1\to2$, $(-6,-4,-2,-8)$ | 89 | 32 | 57 at 2 | 0.600 |

**Gluing near $0$ (§4.6).** For each child state $y'$ with $|y'|<0.2$:
- the parent orbit of $\varphi^3y'$ at the parent radius, by exact breadth-first search, identifying lifted copies of one point orbit;
- the main group is the parent orbit with the most such states;
- multi-source breadth-first search from the components of its near-$0$ states.

| child | states $\lvert y'\rvert<0.2$ / comps | parent orbits | largest parents | groups at distance 0 / 1 | near-0 diameter | max distance to near-0 set |
|---|---|---|---|---|---|---|
| $0$, level 1 | 245 / 11 | 9 | 1 433, 543, 543 | 9 / 0 | 3 | 2 |
| $0$, level 2 | 3 221 / 67 | 105 | 30 165, 590 (×4) | 105 / 0 | 4 | 2 |
| $0$, level 3 | 45 557 / 787 | 1 561 | 400 519, 8 166 (×4) | 1 557 / 4 | 4 | 2 |

Identical to the note's table.

**Random children.** The seeds are my own:
- physical point uniform in a box, kept if the rounded lattice point is in $D_1\cup D_2$;
- internal point uniform of modulus $\le25/(\varepsilon\delta)$;
- 12 seeds at each of the parent defects $1/30$ and $1/16$;
- children with more than 40 and at most $3\cdot10^5$ states.

13 children qualified (557 to $98\,379$ states; one more exceeded the cap). On all of them:
- every group is at distance $0$;
- the near-$0$ diameter is at most $4$;
- every component is within $3$ of the near-$0$ set.

Nine of the 13 collect their near-$0$ states from a single parent orbit of 40 or 155 points. This agrees with the note's random rows. It is a smaller sample.

**Not reproduced:**
- Computation 4.2 (margins);
- the distance and letter-distance histograms of §4.3;
- §4.5 (`lcov`) and §4.7 (`lune`);
- the note's own random seeds.

## 4. Assessment

**Is "(A5)/(A6) cannot be made local" a proof?** No.
- Proposition 7 proves something precise: a chart image of a parent word domain never fills a child word domain. Every boundary arc leaves a lune.
- It does not prove that the child-side facts (A5) and (A6) need can only be had globally. For example, a cell analysis of which child words act inside the lunes, uniform in $\delta$, is a local statement. Proposition 7 does not exclude that it suffices.
- §4.5 shows that one particular test, local validity of a chart, is not positional. But that test refers to child token components, which are global objects, so this is unsurprising. It does not show that no positional criterion exists.

So the conclusion is a well-supported judgement, now labelled as such. I share it. (A5) is (R2) of the component-graph note with several charts in place of one, and (A6) adds a gluing bound. Both are reverse-type uniform bounds of the kind the last three notes reduced to and could not prove. Both also follow trivially from (K). The atlas sharpens the bookkeeping, but it does not move the difficulty.

**Idea 46 (gluing by completeness near $0$).**
- *Why it is promising.* The statement it asks for, "every lattice point of the right class near $0$, with internal coordinate in a window, lies in one of boundedly many large token components", concerns the token graph alone, with no connectors. That is the setting where the programme has succeeded: (T) by the fence, and the one-line model set. A proof would make (A6) automatic for the parents whose near-$0$ states it covers.
- *What it still needs.* "Whose mutual distance is bounded" is a connector statement again, of (K) type. It is restricted to boundedly many named components, though, which the invariance of the type graph (component-graph note, Computation 4.5) might make a finite check.
- *First test.* The fraction of the window near $0$ filled by hub components, at two levels, as the idea says.

**Idea 47 (renormalize the radius).** The argument is right, and it can be sharpened.
- *The rim graph.* Fix a child orbit $O'$ at $r'$. Its states split into lifted orbits at the parent radius $r<r'$; this needs only orbit monotonicity, and I checked it in the computation. Call these the *$r$-orbits* of $O'$. The rim graph has the $r$-orbits as vertices, joined when a letter acting at $r'$ but not at $r$ (a "rim letter") moves a state of one into the other.
- *Why distances transfer.* Token edges and connectors at $r$ are also edges at $r'$. So distances in $\mathcal C(O')$ are at most the distances in each $r$-orbit's own component graph.
- *The bound.* A path in the rim graph of length $\ell$ gives a path in $\mathcal C(O')$ of length at most $(\ell+1)D(\delta)+\ell$. Hence $D(\varepsilon\delta)\le(R+1)D(\delta)+R$, where $R$ bounds the rim-graph diameters of all child orbits. With a uniform $R$, the recursion of Theorem 8 gives (B) from the same base.
- *What this removes.* There are no charts, no regions $G_\chi$, no coverage hypothesis (the $r$-orbits partition $O'$ exactly), and no forward transport lemmas.
- *What remains.* A single uniform bound on the diameter of a canonical graph built from the child. It is still a global, reverse-type statement, but a cleaner one than (A4)–(A6).
- *A first computation (exact, orbit of $0$, defect ratio $\varepsilon$):*

  | child | states | $r$-orbits | largest $r$-orbit | rim-graph edges | rim-graph diameter (exact) |
  |---|---|---|---|---|---|
  | level 1 | 30 165 | 449 | 5 242 | 584 | 12 |
  | level 2 | 400 519 | 1 307 | 62 163 | 1 700 | 14 |
  | level 3 | 5 673 561 | 4 815 | 803 274 | 6 234 | 14 |

  The number of $r$-orbits grows by a factor of 3 to 4 per level, while the diameter stays at 14. The rim graph is nearly a tree.

  This is the cleanest uniform quantity in this line of notes so far. I recommend it as the next object of study:
  - its diameter on random children at several radii;
  - its diameter for other defect ratios, since the argument does not need the ratio to be $\varepsilon$;
  - whether the rim letters that realize the diameter sit at finitely many tight corners. If they do, that is where a proof would have to look.

## 5. Suggestions

1. Specify $G_\chi$ in Conjecture 9. The natural choice is the set of good states of $\chi$, or a union of cells. Then re-measure (A4) pairwise on it: $s=2$ may hold there.
2. If the atlas line is continued, compute the full gluing graph $\mathcal P(O')$ of (A6) over all good charts on at least one child. Only its chart-$0$, near-$0$ part is known.
3. Pursue idea 47 in the rim-graph form of §4 before more atlas work.
