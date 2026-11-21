# Referee report: `theorem1-converse.md` and `boundary-contact.md`

Referee: Claude (independent of the authoring agent)

Both documents were read line by line against the setting of arXiv 2302.12950: closed disks $D_1, D_2$ of radii $r_1, r_2$ centred at $\mp1$, with $a$ and $b$ the piecewise rotations and $GG=\langle a,b\rangle$ a group of bijections of the plane. The paper's Theorem 1 says that some $GG_{n_1,n_2}(r)$ is infinite if and only if $\operatorname{lcm}(n_1,n_2)\notin\{2,3,4,6\}$. The paper proves only the "if" direction and omits the "only if" direction (text extract, lines 86–88).

## Verdicts

| Document / statement | Verdict |
|---|---|
| `theorem1-converse.md`, Theorem 5.1 (finite for all radii when $m\in\{1,2,3,4,6\}$, orbit bound $N$) | **correct** |
| Proposition 4.2 (f.g. group, uniformly bounded orbits, faithful ⇒ finite) | **correct** |
| Proposition 2.4 ($n_1,n_2\ge2$: $\Gamma$ discrete ⇔ $m\in\{2,3,4,6\}$) | **correct** |
| Theorem 6.5 (invariant finite atom partition) | **correct** |
| Proposition 7.1 (disjoint and tangent disks) | **correct** |
| Remark 8.2 (the "if" direction fails when some $n_i=1$) | **correct** |
| `boundary-contact.md`, Theorem 3.1 (orbit monotonicity as sets) | **correct** |
| Example 3.2 (word-level failure, no generator-preserving homomorphism) | **correct** (computations re-done exactly); the framing "the paper's reason is false" is slightly overstated (issue 1) |
| Theorem 3.4 (group monotonicity), Corollary 3.6 | **correct** |
| Theorem 4.1, Corollary 4.2 (right stability, $\mathcal I(p)=[r^*(p),\infty)$) | **correct** |
| Theorem 5.1 (boundary-contact dichotomy), Corollary 5.2 | **correct** |
| Proposition 6.1 (open disks) | **correct after minor fixes** (issue 2) |
| §7 (other one-parameter families) | **sketch, essentially correct**; not at the level of detail of the rest (issue 4) |

I found no fatal problem and no real gap. The issues below are minor or cosmetic.

## Issues

1. **`boundary-contact.md`, status paragraph and Example 3.2: "the paper's stated reason is false as literally stated."** Minor (framing). The paper's sentence (extract, lines 81–82) reads "the size of the orbit of any given point cannot decrease as $r$ increases—all group elements that affect it are still available". Example 3.2 does refute the word-level reading: a fixed word acts differently at different radii, and no generator-preserving homomorphism $G_r\to G_{r'}$ exists. The sentence also has a reasonable charitable reading: "every move applied to the point is still applicable". That reading is exactly the chain argument of Theorem 3.1. *Repair:* say "imprecise; read at the level of group words it is false (Example 3.2), and the intended meaning is made rigorous by Theorem 3.1".

2. **`boundary-contact.md`, Proposition 6.1(1), proof.** Minor gap in exposition.
   - The proof says "membership agrees, and the argument of Theorem 4.1 applies". In Theorem 4.1, invariance gives $O_r(p)\subseteq S$ and monotonicity gives $S\subseteq O_r(p)$. Here $r\le r_0$, so invariance and monotonicity both give the *same* inclusion $O_r(p)\subseteq S$. The inclusion that is actually needed, $S\subseteq O_r(p)$, is not supplied by "the argument of Theorem 4.1".
   - The statement is still true. Every generator at radius $r$ agrees on $S$ with the corresponding generator at $r_0$, so every $r_0$-chain from $p$ (which stays inside $S$) is an $r$-chain.
   - Separately, $\delta'$ is a minimum over a possibly empty set. This happens, for example, when $p$ lies in neither open disk. That case needs the convention $\delta'=+\infty$, together with $r>0$.
   - *Repair:* replace the sentence with the chain argument, and add the convention for $\delta'$.

3. **`boundary-contact.md`, Corollary 4.2 and Definition 3.5.** Cosmetic.
   - Corollary 4.2 evaluates $O_{r^*(p)}(p)$, which needs $r^*(p)>0$. This is true but not stated. Orbits are finite for $r\le1$ (disjoint or tangent disks, `theorem1-converse.md` Proposition 7.1), so $r^*(p)\ge1$.
   - Definition 3.5 says $\mathcal F$ is "$(0,r_c)$ or $(0,r_c]$". It can also be $(0,\infty)$, for example when $n\in\{1,2,3,4,6\}$. Writing $r_c=\infty$ covers this, but it should be said.
   - *Repair:* add one sentence for each.

4. **`boundary-contact.md`, §7.** Minor. The three bullet points are sketches. For example, the analogue of Theorem 5.1 along a family needs the hypothesis "finite for all $t<t_0$". Part 1 then needs a choice of $t$ such that $r_k(t)>r_k(t_0)-\Delta$ for $k\in J$ and $r_k(t)=r_k(t_0)$ for $k\notin J$. I checked that this works. The status table does not claim §7, which is appropriate. *Repair:* label §7 "sketch" or write out the two modified proofs.

5. **`boundary-contact.md`, §8.** Minor. It cites a working note `twodisk_continuation.md` ("§2.3", "Cauchy–Hadamard analogue"). No such file exists anywhere under `/Users/eric/Github/TDCSG`. A reader cannot check these comparisons. *Repair:* add the note, point to where it lives, or recast §8 without the reference.

6. **`theorem1-converse.md`, status paragraph: "two independent proofs".** Cosmetic. The §6 proof avoids Proposition 4.2. It still reuses Lemmas 2.1, 2.2 and 3.1 and the bound on $(u,t)$ from Theorem 5.1 step 2. "Two proofs of the finiteness step" would be more accurate.

7. **`theorem1-converse.md`, Remark 8.1.** Cosmetic. The list "the proofs in §§3–6 use only these facts" leaves out two things that §6 also uses: the disks are connected (convex), used in Lemma 6.4(2), and they are bounded by circles, used to define $\Sigma$. The conclusion for open or mixed disks is unaffected. *Repair:* add "each $D_k$ is a (closed or open) round disk".

8. **`theorem1-converse.md`, definition of "discrete" before Proposition 2.4.** Cosmetic. The definition is orbit-based (every orbit meets every bounded set finitely), not the usual "discrete subgroup of $\mathrm{Isom}(\mathbb C)$". For groups of the form $\mu_m\ltimes T$ the two notions agree, and the proposition is correct under the stated definition. *Repair:* a short remark would help readers.

9. **`theorem1-converse.md`, §9 numbers.** Information only. I reproduced "largest orbit 38" for $(6,6)$, $r=2$ (see below). I did not reproduce the permutation-group order of about $2.07\cdot10^{39}$.

## Answers to the specific points raised

**(a) Proposition 4.2 and the lemma in `boundary-contact.md` Proposition 3.3.** The argument is complete, and it is the standard finite-index-subgroup argument rather than the "variety generated by $S_N$" route.
- $H_x=\pi^{-1}(\mathrm{Stab}_G x)$ has index $|Gx|$, because $\pi$ is surjective.
- The free group $F_k$ has at most $(j!)^k$ subgroups of index $j$ (via the coset action).
- Faithfulness gives $\ker\pi=\bigcap_{x\in X} H_x$. Faithfulness is automatic here, because $G$ is defined as a group of bijections of $X=\mathbb C$, the very set it acts on.
- The family $\{H_x\}$ is a subset of the finite set $\mathcal H_N$, even though $X$ is uncountable. So the intersection is finite and has finite index.

The bound $|G|\le\prod_{H\in\mathcal H_N}[F:H]$ is valid.

**(b) Lattice and constant.** The lattice is correct in every case:

| $m$ | $\omega$ | $L$ |
|---|---|---|
| 1 | $1$ | $\mathbb Z$ |
| 2 | $-1$ | $\mathbb Z$ (the translations actually lie in $2\mathbb Z$; the bound is crude but valid) |
| 4 | $-\mathrm i$ | Gaussian integers $\mathbb Z[\mathrm i]$ |
| 3, 6 | $e^{-2\pi\mathrm i/m}$ | Eisenstein integers $\mathbb Z+\mathbb Z\omega$ (relations $\omega^2=-\omega-1$ and $\omega^2=\omega-1$ checked) |

- For unequal orders, $\zeta_k=\omega^{m/n_k}\in L$. So $\Gamma\subseteq\mu_m\ltimes L$, and $N=m\cdot\#\{t\in L:|t|\le2R\}$ follows from $|z|\le R$ and $|uz+t|\le R$.
- Checked exactly for the pairs $(2,3),(3,6),(2,4),(4,2),(4,4),(1,6),(1,4),(2,6),(2,2),(3,3),(6,6),(1,1)$ (below).
- Corollary 5.2 ("both divide 4 or both divide 6") is correct.

**(c) The atom arrangement.**
- $\Sigma$ is infinite but locally finite. Its centres lie in $L$ because $\pm1\in L$ and $\gamma(L)=L$.
- Only finitely many circles of $\Sigma$ meet $U$.
- A circle that misses a disk has constant position function on that disk, by connectedness.
- Atoms are defined by position relative to *all* circles of $\Sigma$, with the value $0$ for points on a circle. So $\Gamma$ permutes atoms exactly (Lemma 6.2), and atoms never straddle $D_k$, whether closed or open (Lemma 6.3).
- The induction in Theorem 6.5 is sound.
- I verified the claim of Remark 6.6 for $n=4$, $r=1.2$. The circle centred at $B^2(-1)=3$ meets $D_2$, and its image under $A$, centred at $-1-4\mathrm i$, misses $U$.

**(d) Proposition 2.4.**
- I re-derived the commutator translation $(c'-c)(\alpha-1)(1-\beta)$. With centres at distance 2 it gives $t_0=2(\zeta_1-1)(1-\zeta_2)\ne0$.
- The Bezout step gives $\mathbb Z[\zeta_1,\zeta_2]=\mathbb Z[\omega]$ for $n_1\ne n_2$.
- The rank argument is correct: $\varphi(m)\ge4>2$ uses the irreducibility of the cyclotomic polynomial $\Phi_m$.
- The direction "$m\in\{2,3,4,6\}$ ⇒ discrete" is immediate from Lemma 2.2.
- Both directions hold.

**(e) Remark 8.2.** Correct. For $(n_1,n_2)=(1,5)$, $a=\mathrm{id}$ and $G=\langle b\rangle\cong C_5$, although $\operatorname{lcm}=5\notin\{2,3,4,6\}$. For $(1,1)$, $G$ is trivial and $\operatorname{lcm}=1$. So the paper's "if" direction needs $n_1,n_2\ge2$. The note correctly identifies what it proves as the omitted "only if" direction.

**(f) Monotonicity.**
- Example 3.2 recomputed exactly in $\mathbb Q(\mathrm i)$:
  - $(b\circ a)(p)=-\tfrac12$ at $r=1$;
  - $(b\circ a)(p)=1+\tfrac32\mathrm i$ at $r=2$;
  - $[a_5,b_5](0)=-4\mathrm i$.
- Theorem 3.1 is genuinely proved. The orbit is the set of points reachable through non-trivial moves $z\mapsto A^{\pm1}z$ (allowed when $z\in D_1(r)$) and $z\mapsto B^{\pm1}z$ (allowed when $z\in D_2(r)$). Each such move is still allowed at every larger radius. Deleting trivial steps first is exactly what makes this work.
- No counterexample was found (below), including boundary starting points.

**(g) Stability and boundary contact.**
- In Theorem 4.1 only membership of *orbit* points matters. A non-orbit point that enters a disk is never reached, because a chain only visits orbit points. An orbit point on a boundary circle stays inside a closed disk as the radius grows.
- Hence $\mathcal I(p)=[r^*(p),\infty)$, and the infimum is attained.
- Theorem 5.1, parts 1–3, is correct, including the counting step in part 2. Each $y$ occurs in at most two pairs, and compactness gives the accumulation point.
- The open-disk variant is correct, subject to issue 2.
- The "does not show" list and the open problems (footnote 4 at group level, whether $r_c=r_c^{\rm orb}$, where the contact occurs, whether (B) can occur without (A)) are stated accurately. They are not overclaimed.

## Computational checks

All checks used exact arithmetic in $\mathbb Q(\zeta_m)$ with `Fraction` coefficients, reduced modulo $\Phi_m$. Disk membership was decided by the exact sign of $r^2-|z-c|^2$. For $m=5$ that sign is computed in $\mathbb Q(\sqrt5)$ by integer comparisons. Scripts are in `/private/tmp/claude-501/-Users-eric-Github-riemann-hypothesis/8e07d302-d180-4cc0-ac7d-117a36aae2f9/scratchpad/ref1/` (`cyc.py`, `t1.py`–`t4.py`).

1. **Example 3.2:** all three values confirmed.
2. **Theorem 5.1 orbit bound.**
   - Pairs: the 12 pairs listed under (b).
   - Squared radii $(r_1^2,r_2^2)\in\{(1/4,9/4),(9/4,9/4),(4,1),(9/4,25/4),(4,4)\}$, so unequal radii were included.
   - Starting points: all points of a mesh-$1/3$ grid in lattice coordinates that lie in $U$, plus the boundary points $-1+r_1$ and $1-r_2$.
   - Every orbit was finite with size $\le N$; the largest ratio of orbit size to $N$ was $0.14$.
   - Every orbit point had the form $uz+t$ with $u\in\mu_m$, $t\in L$ and $|t|\le2R$.
   - The largest orbit for $(6,6)$ at $r=2$ was 38, matching §9.
3. **Theorem 3.1 monotonicity, $n=3,4,5,6$, equal radii.**
   - Radii $r\in\{1,5/4,3/2,7/4,2,17/8,9/4,5/2\}$.
   - Starting points: a mesh-$1/2$ grid, plus the boundary points $\pm1\mp r\zeta^j$ for every radius in the list.
   - Test: $O_r(p)\subseteq O_{r'}(p)$ for all $r<r'$ where both orbits were finite.
   - For $n=5$, which has infinite orbits beyond the critical radius $\approx 2.149$, the test compared breadth-first balls of depth 6. Such balls are also monotone by the same chain argument.
   - 23,856 inclusion checks, 0 violations.
4. **Theorem 4.1 right stability (closed disks).**
   - $n=3,4,6$: every finite orbit at $r$ was recomputed at squared radius $r^2+10^{-9}$, giving 4,952 checks.
   - $n=3,4,5,6$: radius $r_1$ alone was bumped, giving 4,079 checks.
   - 0 changes.
5. **Proposition 6.1 (open disks), $n=3,4,5,6$.**
   - Left stability at $r^2-10^{-9}$: 3,730 checks, 0 failures.
   - Right side at $r^2+10^{-9}$: 366 finite open-disk orbits changed. Every one of them contained a point on a boundary circle, as part 2 predicts.

## What I did not check

- The paper's own "if" direction (infinite for some $r$ when $m\notin\{2,3,4,6\}$, $n_i\ge2$). The note does not claim it either.
- The permutation-group orders quoted in `theorem1-converse.md` §9, such as $\approx2.07\cdot10^{39}$.
- The comparisons with the missing working note in `boundary-contact.md` §8.
- Computations for $n\notin\{1,\dots,6\}$, and the unequal-order pair $(3,4)$, which needs $\mathbb Q(\zeta_{12})$.
- Theorem 6.5 numerically (the atom counts). It was checked by reading only.
- The standard facts that the proofs cite and that I accepted: irreducibility of $\Phi_m$, and that a discrete subgroup of $\mathbb R^2$ has rank at most 2.
