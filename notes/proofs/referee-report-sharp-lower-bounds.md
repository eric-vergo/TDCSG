# Referee report: `sharp-lower-bound-n5.md` and `sharp-lower-bound-n8.md`

Referee: Claude (independent of the authoring agents)

Scope: the two notes as of 21 November 2026, with the companions `critical-radius-n5.md`, `critical-radius-n8.md`, `boundary-contact.md`, `theorem1-converse.md`, `../certificates.md`, and the session programs in `sharp5/` and `sharp8/` (read only). The referee's own computations are in the session scratch directory `refsharp/` (scripts in `refsharp/code/`).

## Summary of verdicts

| # | claim | verdict |
|---|---|---|
| n5-1 | Lemma 2.2, Corollary 2.3 (non-norm radii; no lattice/ℚ(ζ) points on circles, no tangency, no triple points) | **correct** |
| n5-2 | Theorem 3.1 (at a non-norm radius: finite group ⇔ finite closure; (C3), (C4) automatic) | **correct after minor fixes** (issue 3) |
| n5-3 | Theorem 4.1 (lattice realisation, lattice window criterion), Theorem 4.3 (finite lattice bootstrap) | **correct** (constant C₀ should be made explicit; issue 4) |
| n5-4 | Lemma 6.1, Proposition 6.2 (Diophantine lune lemma, exact renormalization) | **correct**; the coverage statement needs to be quantified (issue 5); item 6.2(4) is heuristic (issue 6) |
| n5-5 | Theorem 5.2, level two (r ≤ r₂, δ = ε²/10) | **computed, not certified** (issues 1, 2) |
| n5-5' | Theorem 5.2, level one (δ = ε/10) and δ₋ | true, but **superseded**: implied by the exact engine certificates at δ = 1/50, 1/55 already recorded in `../certificates.md`; additionally **reproduced here by the exact engine directly at level one** (see Recomputation) |
| n5-6 | Orbit of 0 finite for r ≤ r₃; sizes and internal extents at levels 0–3 | **correct** (reproduced exactly by the Lean engine); scaling statements are evidence and labelled as such |
| n5-7 | Conjecture 8.1 equivalent to (B) | **correct** (the equivalence is a reformulation via Theorem 3.1 + monotonicity) |
| n8-8 | Lemmas 2.1–2.4 (coset, no tangency/lattice points on the families, δ_m closed form, 32 critical points in 8 classes) | **correct** (all recomputed); one false side claim on window disjointness (issue 9) |
| n8-9 | Lemmas 5.1, 5.2, Theorem 5.3, Lemma 5.4, Theorem 5.5 (general n) | **correct**, and general as claimed |
| n8-10 | Proposition 2.5 ("no affine lattice map renormalizes the centre set") | **correct but weak**; the summary line overstates it (issue 10) |
| n8-11 | Finiteness for r² ≤ r_c² − 1/35 | **correct (proved modulo the exact engine computation)**; re-checked here; superseded by the recorded δ = 1/36 certificate (issue 8) |
| n8-12 | Corollary 5.7 (Conjecture S ⇒ F₈) | **correct after minor fixes** (notation, issue 11); evidence is labelled, with one overstated word (issue 12) |

No fatal error was found in either note. The main problems are (a) the n = 5 level-two claim is presented as "proved modulo an exact computation" when it rests on one unrefereed floating-point-ordered C program with no independent check, and (b) both notes report as their headline new range a result that is weaker than what `../certificates.md` already records for the same engine.

---

## Issues

### Issue 1 (gap; n5 title, status item 1, §5.1, Theorem 5.2, §10): the level-two result is not certified

**Location.** Title ("certificates to level two"); status item 1 ("Proved modulo an exact finite computation that was carried out ... a new exact C implementation"); line "Throughout ... with a proved error bound"; §5.1 "Exactness"; Theorem 5.2; §10 table row; §8 "Verified: k = 0, k = 1, k = 2".

**What the claim rests on.** Level two (δ₂ = ε²/10, 4 929 752 canonical circles, 68 989 951 canonical maximal arcs) rests on exactly one program, `kcut4.c` (and its predecessor `kcut3.c`, which gives a byte-identical output; I confirmed `cmp s_L2.txt u_L2.txt` is empty, both 4 498 396 015 bytes). Its own (C2)/(C4) re-check pass is the same code, with the same angle function and the same comparison routines; it is not an independent check. No other program has read the level-two output.

**Floating point.** The note says ordering is done "with a proved error bound". Reading `kcut4.c`:
- the per-symbol angle error is not computed but hard-coded: `double err = 5e-15;` (line 92). The value is plausible: I estimate ≲ 4·10⁻¹⁵ from the cancellation-free evaluation of Re d, Im d/sin72°, |d|² and 4ρ − |d|² (each to a few ulp in relative terms), two `atan2` calls and one addition. But no derivation is written in the note, and it assumes that the platform `atan2` is accurate to about one ulp, which IEEE 754 does not guarantee.
- the error of the derived quantities that are actually compared is not accounted for. `relofs` computes `fmod(th − bth + 2·TWOPI, TWOPI)`, whose rounding at magnitude ≈ 19 is up to ≈ 1.8·10⁻¹⁵, and `st = u − cp·TWOPI`, `en = st + L` add more. The total is still ≈ 10⁻¹⁴, five orders of magnitude below NEAR = 10⁻⁹.
- every decision taken through `cmpo`/`relofs` aborts if two distinct symbols are computed within NEAR. This a-posteriori guard is the right design. With any true error below about 5·10⁻¹⁰ it makes every such decision correct. The non-norm lemma is **not** used to bound the separations a priori: Corollary 2.3 shows that distinct symbols are distinct points, but it gives no lower bound on their angular distance. So the 5·10⁻¹⁵ bound is not "proved sufficient" from a minimum separation. Its sufficiency is observed at run time, through the absence of aborts. That is legitimate, provided the bound itself is valid.
- one ordering decision is unguarded: the `qsort` by `st` in `add_arc_raw` compares raw doubles. I believe it is harmless, because the stored arcs on a circle are disjoint with lengths ≥ NEAR (enforced by `relofs`), so their starts are separated by more than the error. But that is an argument about the program, not something the note states.

**Is termination of a float-guided closure a certificate under Theorem 3.1?** Only if every ordering decision was correct. Theorem 3.1 (3)⇒(1) needs the *true* union of the stored arcs to be invariant. A wrong ordering can make the closure stop early with a non-invariant set. The program's own (C2) pass uses the same decisions, so it cannot detect such an error. So the level-two claim is: "conditional on the correctness of `kcut4.c`, including an unproved a-priori bound on libm `atan2`, the closure terminates". That is a computation by a single unrefereed implementation. It is not an exact certificate.

**Repair.** Re-label level two everywhere as "computed (one implementation, floating-point ordering with a run-time margin guard; not independently checked)", and the title as "... certificates to level one, computation at level two". Remove "exact" from "exact C implementation" and "proved" from "proved error bound". Alternatively write out the error analysis (including the `relofs` and `qsort` points above). An independent level-two check would need either a symmetry-reduced mode in the engine's checker or a streaming checker. The engine at its measured ≈ 0.65–0.8 kB per maximal arc would need of order 10² GB for the unreduced ≈ 2.8·10⁸ arcs, so it is not feasible as is.

### Issue 2 (gap in independence; n5 status item 1, §5.1, Table 5.1, Theorem 5.2, Caveat 1): the "referee's independent checker" was modified by the author

`refcheck2.py` and `refcheck3.py` import the referee's `cut.py` unchanged (I confirmed `diff sharp5/cut.py ref4/cut.py` is empty), but they **override `theta`**, the one floating-point geometric primitive, with the author's own formula (the same conjugate trick as `kcut4.c`). `refcheck3.py` also overrides `covered` to canonicalise under the symmetry group. So at level one and at δ₋ the "independent" check shares with the generator its angle code and, for δ₋, its symmetry reduction. The (C1)–(C4) logic is independent; the geometry is not. Both checkers are also floating-point (the log reports `worst_angle_err=8.29e-11`). The note should say this. In fact the level-one and δ₋ claims are better supported by other means: the exact engine certificates at δ = 1/50 and 1/55 in `../certificates.md` (checker without floating point) imply both by monotonicity, since 1/55 < 1/50 < δ₋ ≈ 0.02016 < ε/10 ≈ 0.02361. The referee also certified level one directly with the engine (see Recomputation).

**Repair.** Describe `refcheck2/3.py` accurately ("the referee's (C1)–(C4) logic with the author's angle function"). Cite the engine certificates of `../certificates.md` as the primary support for every radius up to δ = 1/55, and the referee's level-one engine certificate.

### Issue 3 (minor; n5 Theorem 3.1 (1)⇒(2)): wrong citation for "finite group ⇒ 𝒯(r) finite"

The proof cites Lemma 4.1 of `critical-radius-n5.md` for "if GG₅(r) is finite then 𝒯(r) is finite". That lemma proves the converse direction (4.1(3)). The needed direction is true at a non-norm radius. By the argument in the proof of Theorem 4.1, the set of points sharing the itinerary of z along w has non-empty interior, so μ_w(z) is a local isometry by which the group element w acts on an open set. A group element is a piecewise isometry with finitely many pieces, so a finite group has finitely many such local isometries. At a general radius the boundary points need exactly this argument.

**Repair.** Prove 4.1's "S has interior" step first (or as a lemma), and cite it in 3.1 (1)⇒(2) and in 4.1 (1)⇔(2).

The rest of Theorem 3.1 checks out:
- the induction of the Claim (both cases, including e = q and the requirement R⁻¹e ≠ c′, which follows from e ≠ c);
- the deduction of (C4) through "γ starts at y";
- (C3) from Corollary 2.3(2).

### Issue 4 (minor; n5 Theorem 4.3): the constant C₀

The proof of Theorem 4.3 is correct:
- the induction on word length;
- test centres in W_R;
- the choice of a face F of the W_R-arrangement whose closure contains z and which lies on the inner side of the at most two circles through z (it exists by Corollary 2.3);
- F bounded and inside |y| ≤ 3r + 3;
- the unit-scaling argument for a lattice point in B(x₀, f) × B(0, M).

Multiplication by ε changes the ratio of the two radii by φ⁶ per step, so C₀ must absorb a factor up to φ⁶ beyond (covering radius)². Repair: state C₀ = φ⁶ρ_cov² (or any explicit valid value) with ρ_cov the covering radius of Λ for the product-of-disks norm. The remark that f(R) is "polynomially small" is an unproved aside and should be labelled as such.

### Issue 5 (minor, overclaim of scope; n5 status item 4, §6, §8 item 1): the lune lemma is vacuous at the computed levels

Lemma 6.1 and Proposition 6.2 are correct. I re-derived (6.1), the congruences μ ≡ ε^k (mod 10) and N(μ) ≡ (−1)^k (mod 10), the bound |σ(ℓ_P)| ≤ 2|σy − σP||σP − p|, the scaling ε²φ³ = ε of the hypothesis, and g∘Ψ_P = Ψ_{g(P)}∘g. All were also tested exactly (see Recomputation; zero failures).

The hypothesis is very restrictive at small k. Because |y − P|·|σ(y − P)| ≥ 1 for y ≠ P, it forces |y − P| < 1/(200|σP − p|) ≈ 1/309 *and* |y − P| < φ^{−3k/2}/√10. I tested lattice points y = P + ε^kη with η ∈ [−3, 3]⁴ for one tight pair (P, p). The number satisfying the hypothesis is:

| k | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| points satisfying the hypothesis (of 2 401) | 1 | 1 | 1 | 15 | 53 | 171 | 723 | 1 871 |

The single point at k = 0, 1, 2 is y = P itself. For |η|, |σ(η)| ≤ 1 the threshold is k₀ = 4, and for ≤ 2 it is k₀ = 6. So "the exact, k-independent description of the disk tests near the tight points" applies to the levels that were actually computed (0–2) only at P. It cannot be confronted with the §5 and §7 data.

**Repair.** In §6, state the explicit k₀(η-window) and the table above (or an equivalent bound). In the status paragraph, add "asymptotically, from a level k₀ that grows with the normalized window".

### Issue 6 (minor; n5 Proposition 6.2(4)): an informal statement inside a "proved" proposition

Item (4) proves only the identity g∘Ψ_P = Ψ_{g(P)}∘g. The rest ("a chain ... that shadows ... with the disks not tight at P_i decided by margin, is carried ... step by step") has no precise hypotheses. In particular:
- g(P) need not be a tight point;
- "decided by margin" must hold at both levels k and k + 1.

**Repair.** Either state it as a lemma, with these hypotheses written out, or move it to a remark.

### Issue 7 (minor; n5 Table 5.1, "non-norm" column at δ = 1/20)

The entry "no (v₂ even, σρ > 0)" gives reasons that only show Lemma 2.2's sufficient tests fail. In fact ρ = 59/20 + φ is a norm from ℚ(ζ₅):
- N(59 + 20φ) = 4261 is a prime ≡ 1 (mod 5), so the primes above it split completely in ℚ(ζ₅);
- v₂(ρ) is even, and 2 is inert;
- ρ and σρ are both positive.

By the product formula the remaining Hilbert symbol at √5 is also trivial, and Hasse's norm theorem (the extension is cyclic) applies. **Repair:** "no (a norm, by the Hasse norm theorem)", or "not covered by Lemma 2.2".

### Issue 8 (gap in reporting; n5 status item 1 and §5; n8 status item 1, §3, §7): the headline ranges ignore `../certificates.md`

- **n = 5.** The note says "Before this note the bound was δ = 1/10", but `../certificates.md` §5 records exact engine certificates, checked by the engine's float-free checker, up to δ = 1/55 (r_c − r ≈ 0.004235). Those already imply the note's level-one and δ₋ results. The only genuinely new range in the n = 5 note is level two, which is the uncertified one (issue 1).
- **n = 8.** The note's r_* uses δ = 1/35, while `../certificates.md` records δ = 1/36 as certified and checked by the same engine and checker (r_c − r ≈ 0.008135, slightly deeper).

**Repair.** In both notes, cite `../certificates.md` and state the best certified radius from it (n = 5: δ = 1/55; n = 8: δ = 1/36). Present 1/35 (n = 8) and level one (n = 5) as consistent re-derivations, and level two (n = 5) as an uncertified computation beyond it.

### Issue 9 (minor; n8 §5.3): the windows U_k are not disjoint for k = 1, 2

"U_k = ⋃(ξ + ε^kQ), a disjoint union for k ≥ 1 and κ ≤ 1" is false. The smallest sup-norm distance between two of the 32 critical points is exactly ε² = 3 − 2√2 ≈ 0.1716 (recomputed). The squares are disjoint iff 2κε^k < ε², so for κ = 1 they are disjoint iff k ≥ 3. At k = 1, 2 they overlap.

This does not affect Theorems 5.3 and 5.5 or Corollary 5.7, which need only nesting. It does affect:
- the definition of the zoom Z_k and of 𝒫_k, which is ill-defined on overlaps;
- the §6.4 runs that use U₂ with κ = 1.

**Repair.** Require 2κε^k < ε², i.e. κ < ε^{2−k}/2, or k ≥ 3 when κ = 1. Note that the U₂ annulus data were taken with overlapping squares.

### Issue 10 (minor; n8 status item 3, last bullet, and Proposition 2.5): what is actually proved

Proposition 2.5 proves only this: a map c ↦ αc + β or αc̄ + β with α ∈ ℚ(ζ)^× that is a physical isometry is also an internal isometry. That statement is correct. The class of maps is the right one: the ℚ-linear maps respecting the splitting are the ℚ(√2)-linear maps x ↦ αx + βx̄, and the physical isometries among them are exactly the two stated forms. But the proposition says nothing about maps that are not physical isometries, about piecewise or local maps, or about the window. The phrase "no affine lattice map renormalizes the centre set" needs the unstated premise that a renormalization must be a physical isometry. **Repair:** state that premise in the summary, e.g. "no lattice affine map that is a physical isometry expands internal space; hence no exact global recursion of the centre set by such a map".

### Issue 11 (minor; n8 §5.3/§5.5): parameter notation in (S2)

𝒫_k(θ) is defined with θ = δ/ε^k. But (S2) sets r_m² = r_c² − θ_*(3√2 − 2)ε^m, so the parameter actually used is θ_*(3√2 − 2), not θ_*. Corollary 5.7 is unaffected (only "same parameter at m and m − 2" is used), but the notation should be made consistent.

Corollary 5.7 is otherwise correct:
- the orbits of 𝒫_m are the sets O ∩ U_m;
- (S2) together with the base gives a finite innermost factor;
- (S1) gives the other factors at r_c, by Lemma 5.4;
- parity is handled by k₁′ ∈ {k₁, k₁ + 1};
- monotonicity finishes.

### Issue 12 (minor; n8 status item 5, first bullet): "recur exactly" in an evidence item

The germ sets match fully only for m = 2 → 4 (27/27). For 3 → 5 only 20 of 23 are shared (§6.1), and only from 200–6 000 floating-point samples. "Its germs recur exactly with period two" should read "the sampled germ sets agree exactly for 2 → 4 and in 20 of 23 germs for 3 → 5". Otherwise §§4 and 6 are clearly labelled evidence, the floating-point disk tests are disclosed (§6 Method), and no proof step uses them (§7, Gap 2). The 83/90/95% agreement figures and the core maxima 188/224/223 are labelled as sample statistics.

### Issue 13 (cosmetic)

- n5 §5 heading says "Finiteness up to level one" but the section claims level two.
- n5 Table 5.1, δ₋ row: the checker log reports 263 331 circles and 1 906 995 arcs against the table's 263 330 and 1 906 993. The difference is the extra full copy of ∂D₂ that `refcheck3.py` inserts for (C1), plus full circles counted as arcs. The table should say which count it gives.
- n8 Lemma 2.4(4): the second direction is 0.71444… rad, which rounds to 0.7144, not 0.7145.
- n8 §5.2 proof of Lemma 5.4: the cited facts are `boundary-contact.md` Lemmas 2.1 and 2.3; it is fine, but it should note that a⁻¹ = A⁻¹ on D₁ because A(D₁) = D₁.

---

## Detailed checks of the items asked about

**(1) Lemma 2.2 / Corollary 2.3 (n = 5).** Correct.
- (1) uses that σ commutes with complex conjugation.
- (2): 2 has order 4 mod 5, so (2) is inert in ℚ(ζ₅) and unramified over ℚ(√5), and v₂(w w̄) is even.
- (3): 10ρ_k ≡ ε^k (mod 2) is a 2-adic unit and v₂(10) = 1. I recomputed 29 + 10φ, 117 + 40φ (v₂ = −3) and 12 + 21φ ≡ φ (mod 2), and σ(ρ₋) = −0.0979.

The worry about intersection points not lying in ℚ(ζ) is answered correctly by the note:
- for tangency, two equal circles are tangent only externally, at the *midpoint* of the centres, which lies in ℚ(ζ) and at distance r from a centre in ℚ(ζ);
- for a triple point, the three centres are distinct and not collinear (three collinear points have no common equidistant point), so the common point is their circumcentre. The circumcentre is given by (|a|²(b − c) + |b|²(c − a) + |c|²(a − b))/(ā(b − c) + b̄(c − a) + c̄(a − b)), which lies in ℚ(ζ) because ℚ(ζ) is closed under conjugation, and it lies on a circle of radius r about a.

Both cases reduce to item 1. Generic crossing points are never needed.

**(2) Theorem 3.1.** Correct after issue 3.

**(3) Theorems 4.1 and 4.3.** Correct.
- Theorem 4.1: the set S of points sharing the itinerary contains a sector at z, since at most two circles pass through z and they cross transversally. ℤ[ζ₅] is dense, |t| ≤ 2 + 2r, and Λ is discrete in ℂ × ℂ.
- Theorem 4.3: see issue 4. The bootstrap H(R) is a finite computation, since the word maps at y correspond to the orbit of (y, j).

**(4) Lemma 6.1 / Proposition 6.2.** Correct; see issue 5 for the hypotheses and the lattice points covered, issue 6 for item (4), and Recomputation for the tests.

**(5) Computational claims.** See issues 1, 2 and 8. Classification:
- level two is **computed, not certified**;
- level one and δ₋ are **certified**, via the engine certificates at 1/50 and 1/55 and the referee's direct engine run at level one;
- "matches earlier arc sets byte for byte at nine radii" is consistent with `../certificates.md` and the referee logs, but was not re-run here.

**(6) Orbit of 0.** Reproduced exactly (Recomputation). By orbit monotonicity (`boundary-contact.md` Theorem 3.1) |O_r(0)| ≤ 5 673 561 for r ≤ r₃. The scaling statements in §7 are evidence, and the note labels them so.

**(7) Conjecture 8.1 ⇔ (B).**
- (B) ⇒ 8.1: at every non-norm level r_k < r_c the group is finite, so the closure terminates (Theorem 3.1).
- 8.1 ⇒ (B): Theorem 3.1 and group monotonicity.
- Also (B) ⇔ r_crit(5) = r_c, using Theorem A and monotonicity.

The equivalence is correct, and it is a reformulation, not a reduction to an easier statement.

**(8) n = 8 algebraic lemmas.** All recomputed. One side claim is false (issue 9).

**(9) Theorem 5.3, Lemma 5.4, Theorem 5.5.** Checked line by line.
- *Lemma 5.1*: the last visit to W along a chain from a point of O ∩ W. Orbits are equivalence classes because the generating set is symmetric.
- *Lemma 5.2*: all three cases are covered (O ∩ V ≠ ∅; O ∩ V = ∅ ≠ O ∩ W, where O = R_V(w); O ∩ W = ∅).
- *Theorem 5.3*: the chaining is valid because β(W_i; W_{i−1}) ≥ 1 (take L = 0), so the max(1, ·) terms propagate. "Re-entering" orbits are handled because Lemma 5.1 cuts at the last visit, so an orbit that leaves and re-enters a window is charged once per visit point, and β bounds each piece. Boundary points need no separate treatment: chains are defined pointwise with the closed-disk convention, and nothing about cells is used. Finiteness follows from bounded orbits (`theorem1-converse.md` Proposition 4.2, valid for any finitely generated group of bijections).
- *Lemma 5.4*: deleting trivial steps keeps the remaining intermediate points outside W, and each remaining step at radius r is a step at r′ ≥ r.
- *Theorem 5.5*: follows.

All of this is general: it holds for any symmetric finite set of piecewise maps that are monotone in a parameter in this sense, in particular for all n.

**(10)** See issue 10.

**(11)** Re-checked (Recomputation). The δ = 1/35 certificate is VALID under the engine's exact checker. Its SHA-256 is not listed in `../certificates.md`; it is recorded below.

**(12)** S ⇒ F₈ is proved (issue 11). The evidence is labelled, apart from issue 12.

**Titles and status paragraphs.**
- n = 5: the title and status item 1 overclaim (issues 1, 2, 8). Status items 2–4 are accurate, apart from the scope remark of issue 5.
- n = 8: the title and status are accurate. Item 1 should cite 1/36 (issue 8), and item 3's last bullet should be qualified (issue 10).
- Both notes state plainly that the target conjecture is open.

---

## What I recomputed (exact record)

All runs used the repository engine `/Users/eric/Github/TDCSG/.lake/build/bin/tdcsg-orbit`, read only and not rebuilt, plus my own Python (`python3 -I`) in `refsharp/code/`.

1. **n = 8 lemmas** (`n8lemmas.py`, exact arithmetic in ℤ[ζ₈]):
   - exactly 32 lattice points on ∂D₁(r_c) ∪ ∂D₂(r_c), none on both circles, equal to the set {∓1 + u(2 ± i)(1 − ζ)};
   - 8 classes of size 4 under {±z, ±z̄};
   - exactly the four stated centres in 1 + 2ℤ[ζ] for circles of radius r_c through p* (searched over coefficients in [−6, 6]);
   - all 32 tangency centres lie in 1 + 2ℤ[ζ], and (−3, −2, 2, −4) is among them;
   - normal directions mod π/4: 0.0709 and 0.7144;
   - Lemma 2.3 identity exact for m = 1, …, 12, with δ₄ = −683 + 483√2, δ₅ = −3107 + 2197√2, δ₆ = −20219 + 14297√2, and √2-coefficients −2, −30, −44, −488, −2202, −14302;
   - Lemma 2.1 residues: no failures;
   - smallest sup-distance between critical points = ε² (issue 9).
2. **Lune lemma** (`lune5.py`, `lune5b.py`, exact signs in ℤ[φ], hypothesis evaluated in 60-digit decimal):
   - the eight tight pairs (P, p) found are ±E, ±Ē and the lens corners (the lens corners are tight for both p);
   - 76 832 lattice points y = P + ε^kη, with η ∈ [−3, 3]⁴ and k = 0…3, over all pairs gave:
     - (6.1) exact on all points;
     - ν_{k+1}(Ψy) = εν_k(y) on all points;
     - N(μ) ≡ (−1)^k (mod 10) on all points;
     - on the 144 points satisfying the hypothesis: ν ≠ 0, disk test = half-plane test, and membership carried to levels k + 1, k + 2, k + 3 with the hypothesis preserved, with 0 failures;
     - 7 624 points outside the hypothesis where disk and half-plane tests disagree, so the hypothesis is not vacuous;
   - Lemma 6.1(1) bound: ratio ≥ 1.63 near a tight point, and ≥ 1485 over 50 000 random points;
   - coverage table in issue 5.
3. **Orbit of 0, n = 5** (`tdcsg-orbit orbit -n 5 --start 0`, exact; r² given as `re:` specs):

   | level | r² | |O(0)| | max\|σ\| | decisions |
   |---|---|---|---|---|
   | 0 | (29 + 10φ)/10 | 1 433 | 53.75 | float filter, 0 on a boundary circle |
   | 1 | (33 + 8φ)/10 | 30 165 | 273.21 | float filter, 0 on a boundary circle |
   | 2 | (17 + 18φ)/10 | 400 519 | 1 165.0 | float filter, 0 on a boundary circle |
   | 3 | (85 − 24φ)/10 | 5 673 561 | 4 933.19 | float filter, 0 on a boundary circle |

   All agree with §7 of the n = 5 note.
4. **kcut3 vs kcut4**: `cmp` finds the level-one canonical outputs (`s_L1.txt`, `u_L1.txt`) identical, and the level-two outputs (`s_L2.txt`, `u_L2.txt`, 4 498 396 015 bytes each) identical. The level-two logs `L2.log` and `L2b.log` agree with Table 5.1.
5. **n = 8 certificates** (`tdcsg-orbit check-certificate`, re-run on the authors' files in `sharp8/`):
   - δ = 1/35: file `c8_1_35.txt`, 181 638 590 bytes, SHA-256 `d08fa0d01e118e941c32c3e7105596cf15ec9980a93fa556d32f4ffad54a26df`. Result: **VALID**, circles 248 500 (2 full), maximal arcs 3 764 582, (C2) image arcs 8 940 960, (C4) endpoints 78 384; 1 223 s, 2.97 GB.
   - δ = 1/16: file `c8_1_16.txt`, SHA-256 `72ee52fb…0b4`, which matches `../certificates.md`. Result: **VALID**, circles 129 380, maximal arcs 882 710, (C2) image arcs 2 092 704, (C4) endpoints 17 012; 274 s.
   - Both match Table 3.1 of the n = 8 note.
   - The 1/20 file was not re-checked; its SHA-256 is recorded in `../certificates.md`.
   - I did not regenerate the 1/36 certificate that `../certificates.md` records.
6. **n = 5 level one with the exact engine.** I generated it with `tdcsg-orbit certify -n 5 --r2 re:41/10,4/5`, that is, r² = (33 + 8φ)/10 = 3 + φ − ε/10 exactly:
   - The run closed in 1 067 s with 4.5 GB.
   - Counts: 1 007 612 circles (2 full), 6 796 360 maximal arcs, 83 680 778 pieces, 45 680 (C4) endpoints, 0 failures.
   - Decisions made exactly: 0 halves, 0 orders; 0 equalities of points with different symbols.
   - Certificate `refsharp/n5_L1.cert`: 370 546 027 bytes, SHA-256 `db6ecf226414108c151facf5b09d2a6eb1d8c1ec5d673bab738388e9707db352`.
   - `check-certificate` gives **VALID**: (C2) image arcs 17 580 640; 2 419 s, 5.5 GB.
   - The engine's arc set equals the set of (centre, start symbol, end symbol) triples of the authors' `kcut.c` output `k_L1.txt` exactly (6 796 358 arcs + 2 full circles, none on one side only; script `code/cmpcert.py`).

   So finiteness for r² ≤ 3 + φ − ε/10 now has an exact certificate from a generator and a float-free checker, and it independently confirms `kcut.c` at this radius. In Table 5.1, the piece count 83 680 776 differs by 2 from the engine's, the same implementation-dependent offset noted in `../certificates.md`.

   I did not attempt level two (issue 1).

## What I did not check

- Level two for n = 5 by any independent program (infeasible here; issue 1).
- The byte-identity claims at the nine radii of n5 §5.1, and the symmetry-reduction cross-checks at 1/10, 1/20 and level one beyond the `cmp` above. I did not re-run `kcut.c`.
- `lat.py`, `merge.py` and the §7 observations 1–4 (sectors, nesting, merging, distances). I reproduced only the orbit sizes and internal maxima.
- The n = 8 §§4 and 6 floating-point experiments (none is used in a proof).
- `verify.py` on the n = 8 1/16 certificate, and the 1/20 certificate (I did not re-run either).
- The Lean engine's own correctness. I rely on `../certificates.md` §7 and its referee report for that.
- Whether Conjecture S is plausible. In particular, (S1) at r_c could fail if r_c has infinite orbits that avoid all critical windows; nothing here rules that out.
