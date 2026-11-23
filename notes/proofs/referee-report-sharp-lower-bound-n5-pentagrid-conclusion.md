# Referee report: the conclusion of the pentagrid proof, its Lean coverage, and the deductions drawn from it

Referee: Claude (independent of the authoring agent)

Subject: §4 from "Orbits are uniformly bounded" on, and §5, of
[`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md) as rewritten in commit
`346c19b`; the deductions of commit `fa40d04` that Conjecture R$^\ast$
([`critical-radius-n5.md`](critical-radius-n5.md) §6.4, §8) and Conjecture 8.1
([`sharp-lower-bound-n5.md`](sharp-lower-bound-n5.md) §8) now hold; and the rest of
`git diff 997d8ce rework-notes -- notes/`. Sections 1–3, Lemma 4 and the confinement paragraph of
§4 are covered by [`referee-report-sharp-lower-bound-n5-pentagrid.md`](referee-report-sharp-lower-bound-n5-pentagrid.md);
I re-checked them only where the new text depends on them. Lean sources were read, not built.

## Summary

The new conclusion of the pentagrid proof is correct. From Lemma 1 I re-derived the point formula
$g(z)=p+2\zeta^{-j}(x-P(n))$, including the orientation conventions, the empty case and seeds on
the boundary circles. The orbit count $B=1+2\cdot5\cdot(2N+7)^5$ is a valid (in fact twofold)
over-count. The finiteness lemma for groups with bounded orbits is complete. The conjugate bound
$10N+32$ and the constant $(160\sqrt5+32r_c^2)/\delta$ are right, and need no restriction beyond
$0\le r<r_c$. The issues are wording and notation.

§5 describes the Lean development accurately in substance. Three phrases claim slightly more, or
something slightly different, than the Lean source in this worktree proves (issues 5–7).

The deduction that Conjecture R$^\ast$ and Conjecture 8.1 hold is **valid**. Neither conjecture
asks for any uniformity, rate or structure beyond termination at each level together with (C3)
and (C4). Both follow from (B) and Theorem 3.1 of `sharp-lower-bound-n5.md`. Lemma 2.2(3) there
proves that every level radius is non-norm, and I re-checked that proof. What remains is
presentation: both statements are still labelled "Conjecture", and a few nearby sentences still
treat them as open.

No statement for $n=8,10,12$ was upgraded. I found no change of mathematical meaning elsewhere in
the diff. The notes' descriptions of the Lean library match the `rework` branch (after `a28d880`),
not this worktree's Lean tree (issue 14).

## Verdicts

| item | verdict |
|---|---|
| (1) §4 "Orbits are uniformly bounded" | **correct after minor fixes** (issues 1–3) |
| (2) §4 "Bounded orbits give a finite group", including $r<0$ and $0\le r<1$ | **correct** |
| (3) §4 corollary: $\lvert\sigma(b)\rvert\le10N+32$ and $M(r)\le(160\sqrt5+32r_c^2)/\delta$ | **correct after minor fixes** (issue 4: one step cited from the proof, not the statement, of Lemma 4) |
| (4) §5 "What the Lean formalization proves" | **correct after minor fixes** (issues 5–8) |
| (5) Conjecture R$^\ast$ and Conjecture 8.1 "hold" | **correct**: the deduction is valid as written; presentation fixes (issues 9–13) |
| (6) Rest of the diff | **correct**: no change of meaning; nothing for $n=8,10,12$ upgraded (issue 14 is information) |

## What I checked

**Item 1.** Clockwise rotation about $c$ is $w\mapsto c+\zeta^{-1}(w-c)$. In Lean, `exp_rotationAngle_five` gives the factor $\zeta^4$. If $h(w)=\mu w+b$ is the map composed so far, a letter about $p$ acts at $h(z)$ iff $\lvert z-h^{-1}(p)\rvert\le r$, iff $\lvert x-(h^{-1}(p)+1)/2\rvert\le R$. The test is closed, so seeds on the boundary circles are covered, as in Lemmas 1–3. The pulled-back centres differ by $(h^{-1}(1)-h^{-1}(-1))/2=\mu^{-1}$, right minus left. So the left centre carries the sum-zero label $n$, and the right centre carries $n+e_j$ with $\zeta^j=\mu^{-1}$.

The last acting letter, about $p$, fixes $h^{-1}(p)$. Hence the final map $h'$ satisfies $h'(2P(n)-1)=p$, where $n$ is the label of that centre. This gives $b=p-\mu(2P(n)-1)$, and
$$h'(z)=\mu(2x-1)+p-\mu(2P(n)-1)=p+2\mu(x-P(n)).$$
Here $\mu=\zeta^{-j}$ is the linear part *after* the final letter. Inactive letters act as the identity at the current point, so $g(z)=h'(z)$. If no letter acts, then $g(z)=z$.

The side is determined by the layer: $p=-1$ iff $\sum n_j=0$. The final centre is the last vertex of the Lemma 1 walk, which lies in the retained graph and starts at $n^\ast\in\{0,e_0\}$. So the confinement paragraph applies to it, for every word and every $z$, and gives $\lvert n_j\rvert\le N+3$. Each coordinate takes $2N+7$ values, so the orbit has at most $1+2\cdot5\cdot(2N+7)^5$ points.

The confinement paragraph itself is sound. The edge $n\leftrightarrow n+e_k$ changes only coordinate $k$, so a path that moves coordinate $j$ from $a$ to $b$ crosses every level between them. The interior vertices of a simple path have degree at least two in the retained graph. Lemma 4 is stated for every $x$, with no restriction on $\lvert x\rvert$.

**Item 2.** The action on an orbit $O$, after numbering, is a homomorphism $G\to S_{\lvert O\rvert}$, and it is determined by the images of the two generators. There are at most $\sum_{k\le B}(k!)^2$ such homomorphisms. An element of the kernel of the product map fixes every orbit pointwise, so it is trivial by faithfulness. $GG_5(r)$ is a subgroup of $\mathrm{Perm}(\mathbb C)$ generated by the two disk rotations (`GG_eq_closure`), so it acts faithfully. For $r<0$ the generators are the identity (in Lean, `diskPerm_eq_one_of_nonpos`). For $0\le r<1$ no special case is needed: Lemmas 1–4 and the count hold for every $0\le r<r_c$.

**Item 3.** We have $b=p+\mu-2\mu P(n)\in\mathbb Z[\zeta]$, $\lvert\sigma(\mu)\rvert=1$ and $\lvert\sigma(P(n))\rvert\le\sum\lvert n_j\rvert\le5(N+3)$. Hence $\lvert\sigma(b)\rvert\le2+10(N+3)=10N+32$. Next, $2L/\eta=2(\sqrt5/2)\cdot16/\delta=16\sqrt5/\delta$, and $32\le32r_c^2/\delta$ because $\delta\le r_c^2$. The bound $q\le2L/\eta$ needs $F_{k-1}\le L/\eta$. That holds by minimality when $k>3$. When $k=3$ it holds because $L/\eta=8\sqrt5/\delta\ge8\sqrt5/r_c^2\approx3.87$. The other embedding $\zeta\mapsto\zeta^3$ is the complex conjugate of $\sigma$, so it has the same modulus. No further restriction on $\delta$ is needed.

**Item 4.** I compared §5 with `FiveSharp.lean`, `FiveLens.lean`, `FiveWalls.lean`, `FiveWallLevels.lean`, `FiveCenterModel.lean`, `FiveCenterPaths.lean`, `FiveCenterBounds.lean`, `FiveCenterOrbits.lean`, `TDCSG/BoundedOrbits.lean` and `FiveStatements.lean`. They correspond as follows:
- `finiteBelowClosedFormFive` covers every $r<r_c$. It treats $r<0$ through `finite_GG_of_lt_one`.
- `lens` is Lemma 2, with the same non-strict hypothesis $\operatorname{Re}v\ge a-\eta$, $\eta=\delta/16$.
- `leaf_of_level` is Lemma 3. Its level condition is literally the "good" condition of §3.
- `exists_levels` replaces Lemma 4. It works on `AddCircle L` with rotation $\alpha/L=\varphi$, and uses dense integer multiples, open sets $U_i$ and a finite subcover. It yields $-N\le lo<-2<2<hi\le N$.
- `confined` and `centerBox_of_walls` are the confinement step, with box $\lvert n_j\rvert\le N+1$.
- `finite_GG_of_centerBox` is the orbit description: the point $\pm1+2(x-P(n))/\zeta^j$, with the sum-one label on side $+1$.
- `MulAction.finite_of_encard_orbit_le` is the general lemma: a finitely generated group acting faithfully with uniformly bounded orbits is finite.
- Nothing in Lean gives an explicit $N$, the bound $10N+32$, or a rate.

**Item 5.** The statements are as follows:
- R$^\ast$: for every $k\ge0$, $K(r_k)$ is a finite union of arcs satisfying (C3) and (C4).
- 8.1: there are non-norm $r_j\uparrow r_c$, for instance the levels, at which $K(r_j)$ is a finite union of arcs.
- Theorem 3.1: at a non-norm radius, $GG_5(r)$ is finite iff $\mathcal F(r)$ is finite iff the closure terminates, "and in that case $K(r)$ is a finite union of arcs satisfying (C1)–(C4)".

Neither conjecture quantifies over anything uniform in $k$. Neither asks for a rate or a combinatorial type; that is Conjecture R, which is correctly still a conjecture. The chain of the deduction is:
1. (B) gives $GG_5(r_k)$ finite, because $r_k<r_c$.
2. $r_k$ is non-norm by Lemma 2.2(3). I re-checked this: $\varepsilon=2\varphi-3\equiv1\pmod 2$, so $10\rho_k=30+10\varphi-\varepsilon^k$ is a $2$-adic unit. Hence $v_2(\rho_k)=-1$ is odd, and item 2 applies, since $2$ is inert in $\mathbb Z[\zeta_5]$.
3. Theorem 3.1 then gives both conjectures. Its "in that case" clause is supported by the (C4) argument in its proof (3)⇒(1).

The deduction is not circular, because the pentagrid proof uses no certificate. It also holds for all $k\ge0$, as R$^\ast$ requires.

## Numbered issues

1. **Pentagrid §4, "Orbits are uniformly bounded", first sentence. Severity: minor (missing step).** Lemma 1 concerns a sequence of letters, while $g$ is a group element, and "no letter of $g$" presupposes a word. *Replacement:* "Let $g\in GG_5(r)$ and $z\in\mathbb C$. Each generator has order five, so $g$ is a product of the two generators without inverses; fix such a word. If no letter of this word acts at $z$, then $g(z)=z$. Otherwise Lemma 1, applied to its acting letters, gives …"

2. **Same paragraph, notation. Severity: minor.** The letter $j$ names the rotation index ($\mu=\zeta^{-j}$, the triple $(p,j,n)$) and, in the same sentence, the coordinate in "$\lvert n_j\rvert\le N+3$". *Replacement:* write $\mu=\zeta^{-k}$ with $k\in\{0,\dots,4\}$, $g(z)=p+2\zeta^{-k}(x-P(n))$, and "the triple $(p,k,n)$".

3. **Same paragraph, the count $B$. Severity: information.** The count is correct, but $p$ is not independent of $n$: $p=-1$ iff $\sum_jn_j=0$, because the left pulled-back centre has the sum-zero label. *Optional addition after the formula:* "($p$ is determined by the coordinate sum of $n$, so the factor $2$ in $B$ could be dropped.)"

4. **Pentagrid §4, sentence after the corollary. Severity: minor (citation).** "$N\le2L/\eta=16\sqrt5/\delta$ (Lemma 4)" cites a bound that is in the proof of Lemma 4, not in its statement ("$N=O(1/\delta)$"). When the first admissible Fibonacci index is $k=3$, the bound also uses $L/\eta\ge1$. *Replacement:* "Since $N=q\le2L/\eta=16\sqrt5/\delta$ (proof of Lemma 4; if $q=F_3$ this uses $L/\eta=8\sqrt5/\delta\ge8\sqrt5/r_c^2>1$) and $0<\delta\le r_c^2$, this gives …" Alternatively, add "$N\le 16\sqrt5/\delta$" to the statement of Lemma 4.

5. **Pentagrid §5, second paragraph, "for each coordinate and each window center". Severity: minor (overstatement relative to this worktree).** In this worktree `exists_walls` and `CenterBox` quantify only over centres with $\lVert x\rVert\le4$, and `finite_GG_of_centerBox` assumes $r\le4$. (`Five/Confinement.lean` on the `rework` branch has no such restriction.) *Replacement, if §5 is to describe this tree:* "for each coordinate and each window centre $x$ with $\lvert x\rvert\le4$, which covers every seed in the union of the disks since $r<r_c<4$, …". If §5 describes the `rework` tree, no change is needed (see issue 14).

6. **Pentagrid §5, first paragraph, "the integer labels of active centers (Lemma 1)". Severity: minor (different statement).** Lean does not formalize Lemma 1 as stated (a walk attached to each word, and the formula $b=p-\mu(2P(n)-1)$). It proves an invariant of orbit points by induction over the generators (`Framed`, `framed_orbit`). Every orbit point $y$ carries a sum-zero label $n$ and an index $j$ with $2(x-P(n))=\zeta^j(y+1)$, and each label of the pair $n,n+e_j$ that lies in the window is reachable. *Replacement:* "the integer labels of active centres (the content of Lemma 1, proved as an invariant of orbit points rather than of words)".

7. **Pentagrid §5, second paragraph, last sentence. Severity: minor (imprecise).** "A walk from a starting label can cross a good cut only by a final edge into a leaf". A walk may step into the leaf and back again; "final" is accurate only for simple paths. *Replacement:* "a walk from a starting label that crosses a good cut steps into a leaf, from which it can only step back, so every reachable label lies within one step of the region between the cuts."

8. **Pentagrid §5, third paragraph. Severity: information.** The list of results with no Lean counterpart is accurate for the explicit quantities. In this worktree, however, `FiveConjugate.lean` is present: `finiteBelowClosedFormFive_iff` and `finite_GG_iff_conjugatesBounded`. So the qualitative statement $M(r)<\infty$ for each $r<r_c$, without a rate, follows in Lean in one line, although no theorem states it. The file is removed on `rework` (commit `a28d880`). *Optional addition, only if that file is kept:* "Boundedness of the conjugates for each fixed $r<r_c$, without a rate, follows in Lean from `TDCSG.Five.finiteBelowClosedFormFive_iff`."

9. **`critical-radius-n5.md` §6.4, "Conjecture R$^\ast$"; `sharp-lower-bound-n5.md` §8, "Conjecture 8.1" and the status paragraph (item after the numbered list). Severity: presentation.** Both are now theorems but are still labelled conjectures. *Replacement headings:* "**Corollary R$^\ast$** (stated as a conjecture before (B) was proved)" and "**Corollary 8.1 (termination)** (formerly Conjecture 8.1)". Update the references in the status lists and §8/§10 tables accordingly.

10. **`critical-radius-n5.md` §6.4, paragraph "A certificate form of (B)", and the last bullet of "Why R$^\ast$ suffices". Severity: minor (missing citation).** "at the levels $r_k$, which are non-norm radii" gives no source. *Replacement:* "at the levels $r_k$, which are non-norm radii by Lemma 2.2(3) of `sharp-lower-bound-n5.md`, …". In the last bullet, after "The content of R$^\ast$ is therefore that the closure terminates at every level, and that (C4) holds", add: "Both follow from (B) by Theorem 3.1 of `sharp-lower-bound-n5.md`."

11. **`critical-radius-n5.md` §7, items 3 and 4. Severity: presentation (stale).**
    - Item 3 says certification "cannot be continued indefinitely without a uniform pattern such as Conjecture R$^\ast$". R$^\ast$ is now known, and it is not a uniform pattern. *Replacement:* "… without a uniform pattern such as Conjecture R, because the computation grows like a power of $\delta^{-1}$."
    - Item 4 lists "global finiteness at each level (Conjecture R$^\ast$; §6)" among the missing ingredients. *Replacement:* "global finiteness at each level (now known from (B); §6.4)".

12. **`critical-radius-n5.md` §8 table, rows "Conjecture R$^\ast$ (implies (B))" and "… Conjecture R$^\ast$ with its remarks (§6) … not yet refereed". Severity: presentation.** *Replacement for the first:* "R$^\ast$ (implies (B); at the levels equivalent to it by Theorem 3.1 of `sharp-lower-bound-n5.md`) | holds, as a consequence of (B), Lemma 2.2(3) and Theorem 3.1 of `sharp-lower-bound-n5.md` (§6.4); deduction refereed in `referee-report-sharp-lower-bound-n5-pentagrid-conclusion.md`". In the second row, restrict "not yet refereed" to §4.1 and to the remarks of §6 other than this deduction.

13. **`sharp-lower-bound-n5.md` §8, "Equivalent lattice form" and "What a proof must supply". Severity: presentation.**
    - The lattice form has no status, although it now holds, with an explicit constant. *Addition:* "It holds, with $R_k\le(160\sqrt5+32r_c^2)/\delta_k$, $\delta_k=\varepsilon^k/10$ (Corollary of §4 of `sharp-lower-bound-n5-pentagrid.md`; written proof only)."
    - *Replacement heading:* "What a renormalization proof would supply".

14. **Lean descriptions across the notes. Severity: information (consistency between branches).** Several notes describe the Lean library as it is on `rework` after `a28d880`: `certificates.md`, `engine.md`, `open-problem-critical-radius.md`, `critical-radius-n5/n8/n10/n12.md`, `ideas.md` and `overview.md`. Statements such as "the library has no certificate predicate" and the dropped pointer to `finite_GG_iff_conjugatesBounded` are true of that tree. They are false of this worktree's Lean tree, which still contains `Certificate.lean` (`TDCSG.Certificate`, `CutSetCertificate`, `ExistsCertificate`, `finite_GG_of_certificate`) and `FiveConjugate.lean`. *Action:* merge `rework-notes` only together with, or after, `a28d880`; otherwise these sentences are wrong for the code they ship with.

## Item 6: the rest of the diff

- **No upgrades for $n=8,10,12$.** Every changed status line for $n=8,10,12$ still says open: `certificates.md` §6, `relative-certificates.md` §10, `open-problem-critical-radius.md` §3, `critical-radius-n8/n10/n12.md`, `overview.md` item 5 and `ideas.md`. The open statements (R-bulk), (R-core), (R-bulk-t), (R-core-t), Conjecture 5.1, Conjecture S and the uniform connector bound all remain open. In the relative-certificates and combined notes only (B) was removed from the open lists, which is correct.
- **`overview.md`, "Finiteness criterion".** The former sentence ("the group is finite iff the conjugates are bounded", in Lean) is replaced by "the set of word maps is finite iff the conjugates are bounded, and finiteness of the word maps implies finiteness of the group". This matches `open-problem-critical-radius.md` §2 and is correct. The equivalence for the group is no longer stated, which is weaker in form but not wrong.
- **`critical-radius-n10.md` §5.** The new sentence correctly limits "exact critical radius" to $n=5$ and keeps $n=10$ conjectural.
- The rest is status wording, link targets, or the replacement of the removed Lean certificate names by the conditions (C1)–(C4). I found no change of mathematical content.

## What I did not verify

- No Lean code was built or run; the Lean comparison is by reading the source in this worktree. The `rework` branch files (`TDCSG/CriticalRadius/Five/*.lean`) were skimmed only, to confirm that issue 5 does not apply there.
- The archived notes cited from the companion repository TDCSG-archive (for example `sharp-bound-n5-conjugate.md`, Theorem 6, cited in `ideas.md`) are not in this worktree and were not checked.
- Theorem 3.1 and Lemma 3.0 of `sharp-lower-bound-n5.md` were taken as refereed (`referee-report-sharp-lower-bounds.md`). I re-read their statements and the (C4) argument, and re-checked only Lemma 2.2(3).
- Lemmas 2 and 3 of the pentagrid proof were not re-derived beyond what the new text uses. For Lemma 4 I re-checked only the inequality $q\le2L/\eta$.
