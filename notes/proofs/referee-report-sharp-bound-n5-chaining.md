# Referee report: `sharp-bound-n5-chaining.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: the free-token cut-off, the one-line window map, and two-dimensional token components" (`sharp-bound-n5-chaining.md`, commit `08b6d96`). Companions consulted: `sharp-bound-n5-invariant.md` ("line 4": Lemma 5, Theorem 7, Corollary 11, Conjecture B$^\ast$) and its referee report, `critical-radius-n5.md` Lemma 4.1, `boundary-contact.md` Theorem 3.4, and `../engine.md`.

## Summary

The proofs are sound. Every line of Lemma 1.1, Theorem 1, Proposition 2 and Proposition 6 was checked, and every constant re-derived. The finite computation behind Theorem 1 (Computation 1.2) was redone from scratch: the test centres were derived from the words, and the extents were recomputed in 80-digit arithmetic. All fifteen table entries and every decision in the proof agree. The theorem is correct, including the cases $|h|\ge0.15$ and $|h|>1.81$, lines parallel to $\mathbb R\bar E$, and $r=r_c$ off the chord.

All eleven rows of Computation 4 and all of Computation 5 were reproduced with an independent exact program. That includes the $20$-million-point orbit at $\varphi^{-6}/55$, with the same extreme word (17 447 letters, 3 104 tokens, runs $986,189,188,377,189,1175$). The orbit sizes were cross-checked with `tdcsg-orbit`.

The defects are of three kinds.
- **One negative claim was wrong** (Computation 3(1), repeated in the summary and in §5). The note said that words with the fewest connectors alternate dozens of times between the two line classes. That is a tie-breaking artifact of one breadth-first path. Searching for the fewest connectors first and then the fewest runs, the level-2 extreme state needs 2 connectors and only 2 runs. Over every state of that orbit, at most 11 runs are needed. The qualitative point survives in a corrected form: switching lines without a connector does save connectors. **Fixed** in the note.
- **The evidence for (K) was measured with the wrong quantity.** (K) quantifies over every starting point. So the $K_0$ an orbit needs is the diameter of its component graph, not the eccentricity $e$ of the seed. The diameter is 6 to 9 (computed exactly on six orbits), against "$K_0\le7$" in the note. **Fixed.**
- **Small items.** A margin was stated as $0.045$; it is $0.0447$. The case $|h|>0.15$ of Theorem 1(1) was left implicit. The window $W$ of §2.2 is the $\delta$-part of the window of Lemma 1.1. "Internal extent" is measured in $V$, not in $\{\sigma y\}$. The run lengths of Computation 5 match $\varphi^6$ times the reversed $1/55$ runs only to within $6\%$. **All fixed.**

Nothing found affects the logic of Proposition 6, which reduces (B) to Conjecture B$^\sharp$.

## 1. Verdicts

| result | verdict |
|---|---|
| Lemma 1.1 (blocked arcs at every offset) | **correct after a minor fix**: the margins are $\ge0.0447$, not $\ge0.045$; every decision re-derived |
| Computation 1.2 (extents of $U_1,U_2,U_3$ at $r_c$) | **reproduced independently**, every entry, with complete candidate enumeration in 80-digit arithmetic (§3.1) |
| Theorem 1(1) index bound $F_j<\varphi^3/\delta_h+1/\sqrt5$ | **correct after a minor fix**: the proof now says that $\lvert h\rvert>0.15$ is covered by item 2 ($8<F_7\le F_j$) |
| Theorem 1(2) at most 8 index values for $\lvert h\rvert\ge0.15$ | **correct** |
| Theorem 1(3) internal translation $<36.035/\delta_h+8.58$ | **correct** ($1.9021130\cdot4.51014=8.57880$, $2\sqrt5\varphi^3\lvert\sigma E\rvert=36.03415$) |
| Theorem 1(4), lines parallel to $\mathbb R\bar E$ | **correct** |
| Theorem 1, nothing acts for $\lvert h\rvert>1.81$; validity at $r_c$ for $h\ne0$ | **correct** |
| Remark (linear gap, double precision) | not checked; correctly labelled |
| Proposition 2 (one-line return map) | **correct**; every identity checked exactly, and the return times checked at 80 random $v$ (§3.2) |
| Computation 3(1) (mixed walks) | **wrong as stated, fixed**: the "dozens of alternations" are not forced (issue 1) |
| Computation 3(2) (connectors everywhere) | **reproduced**: 26 536 and 350 308 connector moves; largest bin 39 at level 1 (483 against 474 at level 2, a binning convention) |
| Computation 4 (token components, $e$, $D$, $P$) | **reproduced**, all eleven rows (§3.3); the column $D$ is a lower bound, and the exact diameter is 6–9 where computed |
| Computation 4′ (random token components) | not reproduced |
| Computation 5 (S4, $\varphi^{-6}/55$) | **reproduced exactly** (size, $\delta M\ge22.270$, word length, token count, run lengths, 12 connectors); "are those … multiplied by $\varphi^6$" now reads "within $6\%$" |
| Conjecture B$^\sharp$ | well posed. (T) is a finite-domain problem; (K) is plausible, but the evidence is thin (§4) |
| Proposition 6 | **correct**; the chain to (B) is complete and valid at every radius |

## 2. Issues

1. **Computation 3(1): minimal words need not alternate.** The note took the parent pointers of one 0-1 breadth-first search (connectors cost 1, tokens cost 0). That gives *a* word with the fewest connectors, and the one found had about 55 runs. Minimal words are far from unique. I ran a lexicographic search on (state, line class): it minimizes the number of connectors first and the number of single-line runs second. The level-2 extreme state ($\lvert V-V_0\rvert=1\,165.00$) is reached with 2 connectors and **2** runs. Every state of the level-2 orbit is reached with the fewest connectors and at most **11** runs. On the other orbits the maximum is 5, 10, 11, 13 (levels 0–3), 14, 16, 19 ($1/55$ and its two renormalizations along row 6), and 15, 16, 18 ($1/30$ sequence). The claim "the same holds for the state that needs the most connectors" fails for the same reason.

   What does hold is this. If a change of line class is allowed only right after a connector, the largest number of connectors needed rises from $3,4,5$ to $4,6,8$ (levels 0–2), from 6 to 10 ($1/55$) and from 4 to 8 ($1/30$). So direct switches are used, and token components are genuinely two-dimensional. Two more measurements support this.
   - The largest component built from the tokens of *one* line class has rescaled extent $10.96,11.02,11.04$ at levels 1–3. With both classes it is $16.05,16.18,16.20$ (same bounding-box convention). Along the $1/55$ and $1/30$ sequences it is $15.38$ against $23.65$, and $22.22$ against $33.48$.
   - About $60\%$ of the points in large components where tokens of both classes act lie at distance above $0.6$ from $\mathbb RE$ or from $\mathbb R\bar E$ (levels 1, 2, $1/55$, $\varphi^{-3}/55$).

   The note now states this. §5 S3 also cited the artifact; it now rests on the growth of $P$. The conclusion "the window first-return map is not the dynamics" survives, on Computation 3(2) and these data. One caveat: Computation 3(2) counts all connector moves between large components, not the ones that minimal words need.
2. **(K) is about the diameter, not the eccentricity.** For a word map at $z$, the endpoint state determines the map. So "every word map at every point with at most $K_0$ connectors" says that the component graph (in the lifted state space) has diameter at most $K_0$. The seed's eccentricity $e$ is only a lower bound for the diameter, and $2e$ an upper bound. I computed the diameter exactly (iFUB, the exact eccentricity-bounding algorithm) on six orbits: $6,6,7$ (levels 0–2), $9$ ($1/55$), $9$ (row 6), $6$ ($1/30$). Seven sweeps give $\ge8$ at level 3, $\ge9$ on rows 7 and 8, and $\ge8$ on rows 10 and 11. The note's "$K_0\le7$" is **fixed** to "at least 9 and at most 14 on the orbits computed". Proposition 6 can use the weaker form (K′) instead (§5, item 1).
3. **Margin in Computation 1.2.** The two tightest decisions are $\ell\ge0.24471>\tfrac15$ on $U_3$, and $4.22743<2\sqrt5-\tfrac15=4.27214$. Both have margin $0.0447$. **Fixed** ("at least $0.044$"). This is cosmetic: 60-digit arithmetic settles both.
4. **Theorem 1(1) for $\lvert h\rvert>0.15$.** Lemma 1.1(1) needs $\lvert h\rvert\le0.15$. The proof's "(item 1) or (item 2)" covers larger $\lvert h\rvert$ only implicitly, through $8<F_j$. **Fixed** with one sentence. A remark that needs no fix: the bound $\lambda\le0.0895<\varphi^{-5}=0.0902$ in fact gives $j\ge8$, which is stronger than the stated $j\ge7$.
5. **§2.2, the window $W$.** The window of Lemma 1.1(1) is $\lvert\ell\rvert<\delta_h$, with $\delta_h=\delta+h^2$ for small $\lvert h\rvert$. The interval $W=\{\lvert\sqrt5v+\gamma\eta\rvert<1\}$ is its sub-window $\lvert\ell\rvert<\delta$. **Fixed.**
6. **Internal extent.** The bounding-box diagonal depends on the frame. The note's numbers are measured in $V=\{\zeta^{-2j}\sigma y\}$: they match mine in $V$ ($15.64$ at level 1), not in $\{\sigma y\}$ ($16.05$). **Fixed** in the definition. Row 7 gives $23.19$ in $V$ against $23.20$ in the note, and level 3 gives $15.7555$ against $15.75$. Both are rounding.
7. **Computation 5, run lengths.** $\varphi^6$ times the reversed $1/55$ runs is $969,179,197,377,179,1184$, against $986,189,188,377,189,1175$. The two agree to within $5.6\%$, not exactly. **Fixed** ("within $6\%$").
8. **Not a defect, but worth knowing: what the growth of $P$ shows.** $P$ counts single-line runs *plus* connectors, and its runs may use any token, not only $T$-assigned chord-run segments. B$^\ast$ bounds the number of chord-run segments and allows any number of connectors of bounded total effect. So $P$ is not the B$^\ast$ count, and its growth ($6,9,11,12$ over levels 0–3; $13,15,17$ along the $1/55$ sequence) is suggestive only. The lexicographic run counts (issue 1) grow too, and they are closer to B$^\ast$. The note's wording ("do not support") is appropriate.

## 3. Reproduction

All code is the referee's own and was written for this report. The orbit engine was used only for cross-checks.

### 3.1 Computation 1.2

`ext.py` (mpmath, 80 digits) does the following.
- It derives the test centres from the words: $P_m=g_m^{-1}(p_m)$, with $g_m$ the composite of the earlier global rotations. It confirms the composite translations $2\varphi^{-1}E$, $2\varphi^{-1}E$ and $-2\varphi^{-2}E$, and drops the repeated centre of $w_1$ and of $w_2$.
- It finds the extremes of $s$, $h$ and $\ell$ over $U_i(r_c)$, alone or intersected with the bands $\lvert h\rvert\le0.15$, $h\ge0.15$ and $h\le-0.15$.

The enumeration is complete. A linear function on a compact intersection of disks and half-planes attains its extremes at one of three kinds of point: an intersection of two boundaries, the extreme point of a single disk, or the end of a band segment. Candidates are kept if they violate every constraint by at most $10^{-40}$, which only enlarges a range. Every rejected candidate violates some constraint by at least $0.008$. So no decision is close to the working precision.

| | $h$-range | $s$-range | $\ell$, $\lvert h\rvert\le0.15$ | $s$, $h\ge0.15$ | $s$, $h\le-0.15$ |
|---|---|---|---|---|---|
| $U_1$ | $[-1.809017,0.221910]$ | $[-2.255067,-0.599035]$ | $[-4.227425,0]$ | $[-1.895985,-0.958117]$ | $[-2.255067,-0.599035]$ |
| $U_2$ | $[-0.221910,1.809017]$ | $[-0.637033,1.018999]$ | $[0,4.227425]$ | $[-0.637033,1.018999]$ | $[-0.277951,0.659917]$ |
| $U_3$ | $[-0.221910,0.221910]$ | $[-0.250564,1.014496]$ | $[0.244711,4.227425]$ | $[0.104015,1.014496]$ | $[-0.250564,0.659917]$ |

Every entry of the note's table is this one rounded outward. Further checks:
- $\max\lvert\ell\rvert=8.4721360=4+2\sqrt5$ to the digits shown.
- $\gamma=2\operatorname{Re}(\bar uN)=3\varphi-1$ and $2\operatorname{Re}(\bar uE)=\sqrt5$, to 80 digits.
- The decisions of Lemma 1.1. Item 1: $\ell\ge0.24471>\tfrac15$ on $U_3$ in the band; the lifts by $\pm2E$ miss every domain, by margin $0.0447$; $\lvert m\rvert\ge2$ gives $\lvert\ell\rvert>8.744>8.4721$. Item 2: the union of the $s$-ranges is $[-0.637033,1.041883]$ for $h\ge0.15$ and $[-2.277951,-0.599035]$ for $h\le-0.15$. Both have length $1.678916$, and the free arc has normalized length $0.160542>\varphi^{-4}=0.145898$. Item 3: $\lvert h\rvert\le1.809017$.

### 3.2 Proposition 2

The proof was checked step by step. The checks: $n(\varepsilon\xi)=-\varphi^3n(\xi)+\xi$, from $\sigma\varepsilon=-\varphi^3$ and $\varphi^3+\varphi^{-3}=2\sqrt5$; the sign and order arguments, which need $\lvert\xi\rvert<\tfrac12$ and $\varphi^3>1$; and $\varepsilon\sigma(\varepsilon)=-1$. A numerical check (`prop2.py`, 50 digits) used $W=(-0.3,0.6)$ and 40 random $v$ at each of $\delta=1/55$ and $1/30$. In every case $R_{\varepsilon\delta}=R^{-1}_\delta$ with $\xi_{\varepsilon\delta}=\varepsilon\xi^-_\delta$ and the stated return time, $R_{\varepsilon^2\delta}=R_\delta$, and the rescaled displacements are opposite. The return times $-144\to610$ and $89\to1597$ quoted in the note appear.

### 3.3 Orbits

`tc.c` (C, exact). It does six things.
1. Lifted breadth-first search over states $(y,j)$. Points are integer 4-vectors. The disk test is the exact sign of $\rho-\lvert y\mp1\rvert^2$ in $\mathbb Z[\varphi]$, with 128-bit integers.
2. The twelve tokens are derived from the words by the symmetries, and a token acts when each of its letters acts.
3. Union-find gives the token components. The component graph is built from the letter moves between components. $e$ comes from breadth-first search on the component graph, and independently from a 0-1 search on states; the two agree everywhere. The exact diameter comes from iFUB.
4. $P$ comes from a 0-1 search on (state, line class), as in the note's §6 mode 1. Two variants were added: the lexicographic search, and the search where a class switch is allowed only after a connector.
5. $\delta M\ge$ is the exact value $\lvert V_2-V_1\rvert^2=a+b\varphi$ of the farthest pair on the convex hull of $V$. It is a lower bound for $M$ by an explicit pair, whatever floating point does in the hull.
6. A shortest letter word between the extreme states is found and tokenized greedily.

The seeds of rows 6 and 8 were checked to be $\varepsilon$ and $\varepsilon^2$ times $(-500,-26,-293,-335)$, which lies in the $1/55$ orbit.

| $\delta$ | states | large | top $\delta\cdot$ext | $e$ | diameter | $P$ | $\delta M\ge$ |
|---|---|---|---|---|---|---|---|
| $1/10$ | 1 433 | 19 | 11.39 | 3 | 6 (exact) | 6 | 10.749 |
| $\varepsilon/10$ | 30 165 | 23 | 15.64 | 4 | 6 (exact) | 9 | 12.899 |
| $\varepsilon^2/10$ | 400 519 | 11 | 15.73 | 5 | 7 (exact) | 11 | 12.985 |
| $\varepsilon^3/10$ | 5 673 561 | 15 | 15.76 | 5 | $\ge8$ | 12 | 12.980 |
| $1/55$ | 111 107 | 15 | 23.13 | 6 | 9 (exact) | 13 | 22.237 |
| $\varphi^{-3}/55$, row 6 | 1 448 901 | 14 | 23.63 | 5 | 9 (exact) | 15 | 22.259 |
| $\varphi^{-3}/55$, row 7 | 1 467 539 | 16 | 23.19 | 7 | $\ge9$ | 19 | 22.259 |
| $\varphi^{-6}/55$ | 20 057 921 | 20 | 23.65 | 6 | $\ge9$ | 17 | 22.270 |
| $1/30$ | 54 210 | 21 | 32.25 | 4 | 6 (exact) | 9 | 24.658 |
| $\varphi^{-3}/30$ | 747 936 | 15 | 33.49 | 5 | $\ge8$ | 13 | 24.607 |
| $\varphi^{-6}/30$ | 9 929 377 | 16 | 33.51 | 5 | $\ge8$ | 15 | 24.629 |

- Every entry the note gives agrees, apart from the rounding in issue 6. The note's $D\ge$ column is consistent with these values.
- The extreme state ($\max\lvert V-V_0\rvert$) needs $P=4,3,4,3$ at levels 0–3 and $5,6$ at $1/55$ and row 6, as stated.
- The largest component at levels 2 and 3 has $37\,946$ and $518\,136$ points, as stated.
- The S4 table checks: $\delta M=22.237$, $22.259$, $22.270$ at $1/55$, $\varphi^{-3}/55$, $\varphi^{-6}/55$. $M\ge21\,978.915$ at $\varphi^{-6}/55$, with $\lvert V_2-V_1\rvert^2=133518028+216036684\varphi$. At $\varphi^{-3}/55$ both seeds give $7433192+12027116\varphi$, as stated.
- The extreme words: $975$ letters, $172$ tokens, runs $66,10,21,11,10,54$ at $1/55$. $4\,111$ letters, $729$ tokens, 7 runs separated by connectors at row 6. $17\,447$ letters, $3\,104$ tokens, $17\,435$ token letters, 12 connectors, runs $986,189,188,377,189,1175$ at $\varphi^{-6}/55$.
- In the row-6 word the runs alternate between the classes $\iota$ and $\iota\nu$, that is, between the two directions on lines parallel to $\mathbb R\bar E$. They do not alternate between the two chord lines. "Run" in Computation 5 therefore means a maximal stretch of one *symmetry* class, as in line 4.

Engine cross-checks (`tdcsg-orbit orbit -n 5`): `closed-1/55` from `pow:470,202,166,493` gives 111 107; `re:221/55,53/55` from `pow:2118,110,1241,1419` gives 1 448 901; `re:7/2,9/5` from $0$ gives 400 519.

Peak memory was 5.0 GB, for the $20$-million-point orbit.

**Double precision.** Internal extents, the hull and the binning are double precision, and the note labels the extents so. Everything presented as exact (orbit sizes, $e$, $D$, $P$, the extreme pairs, the words) is exact. The $\delta M$ values are exact values of explicit pairs. That they are the diameter rests on a double-precision hull, but they are used only as lower bounds.

**Not checked:** Computation 4′; the Remark; the claims in Computation 5 that all tokens are $T$-assigned and that the connectors contribute $22.83$; the offsets $0.002$–$0.69$ in Computation 3(1).

## 4. Assessment of Conjecture B$^\sharp$

**(T) is a well-posed finite-domain problem.** Write $X=sE+t\bar E$. The six domains are $U_1,U_2,U_3$ and their mirror images $\bar U_i$. Each is an intersection of at most six disks of radius $r$, hence compact and convex. The token graph joins $X$ to $X+\tau_iE$ on $U_i$ and to $X+\tau_i\bar E$ on $\bar U_i$. $E$-moves change only $s$, and $\bar E$-moves change only $t$. So a token path has two indices $(k,l)\in\mathbb Z^2$, the net numbers of steps along each line. Each coordinate performs the golden rotation modulo 2, and the internal translation is $\sigma$ of $(s\text{-change})E+(t\text{-change})\bar E$. Since $s$ and $t$ are bounded, (T) is equivalent to this: on every component, $k$ and $l$ take $O(1/\delta)$ values. That is a two-dimensional analogue of the three-distance argument, for the $\mathbb Z^2$-action of two commuting golden rotations on $(\mathbb R/2\mathbb Z)^2$, with blocked sets cut out by explicit circles. One more structural fact helps: $U_i(r)\subseteq U_i(r_c)$, so the token graph at $r$ is a subgraph of the one at $r_c$. The data support (T) with $C_T\approx34$: the largest mixed component is about $1.5$ times the largest single-line one at every level (issue 1).

The difficulty is real, and the note names it correctly. The blocked window for $E$-moves sits at $s\approx b^\ast-\gamma h/\sqrt5$, and $h$ is proportional to $t$. A walk can therefore slip round the window by changing $t$. Rows with $\lvert h\rvert\ge0.15$ allow only 8 consecutive $E$-positions, but a staircase can use many short rows.

**(K) is plausible, but this is the right uniformity only in a weaker form.** As stated, (K) is uniform over every point of $\mathbb C$, every orbit and every $\delta\le\delta_0$, and it is equivalent to a uniform bound on the diameter of every component graph. The evidence is eleven orbits.
- Along each renormalization sequence the diameter is stable: $9,9,\ge9$ along $1/55$, and $6,\ge8,\ge8$ along $1/30$.
- The seed eccentricity moves by one or two ($6,5,6$; $4,5,5$; $3,4,5,5$), and it differs between two seeds at the same radius (5 and 7 at $\varphi^{-3}/55$).

That is consistent with a renormalization limit. It says nothing about the supremum over all orbits at a radius: random orbits were only sampled for (T), not for (K).

(K) is also stronger than Proposition 6 needs. Write (K′) for the statement that *some* state of each orbit reaches every state with at most $K_0$ connectors. Under (K′), $\operatorname{diam}V\le2\bigl((K_0+1)C_T/\delta+1.903K_0\bigr)$, so (K′) gives the same conclusion with a factor 2. (K′) is measured by $e$, at most 7 in the data.

The lexicographic data (issue 1) also show the following. The number of single-line runs needed grows with the level while the number of connectors does not. So connectors, not runs, are the quantity a renormalization argument can hope to keep bounded. This supports replacing B$^\ast$ by B$^\sharp$.

## 5. Suggestions

1. **State (K′) instead of (K)** in Proposition 6: from one state of each orbit, at most $K_0$ connectors. It is what the eccentricity data measure, and it gives B$^\sharp\Rightarrow$ Conjecture A with constant $2\bigl((K_0+1)C_T+1.903K_0\delta_0\bigr)$.
2. **(T), the most promising provable next statement.** Prove the two-dimensional cut-off first *away from the crossing of the chord lines*. Every token component that stays in $\{\lvert h_E\rvert\ge\eta\}\cup\{\lvert h_{\bar E}\rvert\ge\eta\}$, for a fixed $\eta$ such as $0.15$, would have internal diameter $O_\eta(1/\delta)$, or even $O_\eta(1)$. On such a set Theorem 1(2) bounds one of the two index directions by 8 per line. Since the token graph at $r$ is a subgraph of the one at $r_c$, this may even be checkable once at $r_c$: the arrangement of the translated circles is a finite cell complex on $(\mathbb R/2\mathbb Z)^2$, and the exploration can be certified in exact arithmetic like the cut set of `critical-radius-n5.md` Theorem 4.2. (T) then reduces to the neighbourhood of the origin, where both lines are close and the window picture of Theorem 1 applies to both coordinates at once.
3. **(K), the most promising provable next statement.** Prove the two-dimensional analogue of Proposition 2 for token components. Multiplication by $\varepsilon$ maps lattice points and windows at $\delta$ to those at $\varepsilon\delta$. Show that it maps each large token component at $\delta$ into one token component at $\varepsilon\delta$, outside $O(\delta)$-lunes, with the connector edges between large components carried along. The data suggest that this map takes the component graph at $\delta$ onto that at $\varepsilon\delta$ in its large part: the number of large components (14–20 along $1/55$), their rescaled extents and the diameter (9) are all stable. Start with the orbit of $0$ along $\varepsilon^k/10$, where the tube theorems of `sharp-bound-n5-orbit-of-zero.md` already control the run structure.
4. **Measure (K) over many orbits**, not only extreme ones: the diameter of the component graph for a few hundred random seeds at $1/55$ and $\varphi^{-3}/55$. The program described in §3.3 does one orbit of $10^6$ points in seconds.
5. **Record where direct switches happen in the words that minimize connectors** (not only where both classes act). If they all happen in $O(\delta)$-neighbourhoods of finitely many points, the window formulation of S2 could be revived in two dimensions.
