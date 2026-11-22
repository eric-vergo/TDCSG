# Two-Disk Compound Symmetry Groups

Research on the two-disk systems GG_n(r) of the paper

> R. A. Hearn, W. Kretschmer, T. Rokicki, B. Streeter, E. Vergo,
> *Two-Disk Compound Symmetry Groups*, arXiv:2302.12950 ([`2302.12950v1.pdf`](2302.12950v1.pdf)).

Two closed disks of radius r are centred at −1 and 1 in the plane. One generator rotates the left
disk clockwise by 2π/n and fixes everything outside it; the other does the same for the right disk.
GG_n(r) is the group of bijections of the plane they generate (more generally GG_{n₁,n₂}(r₁, r₂),
with different orders and radii). The paper's Theorem 1 says that GG_n(r) is infinite for some r
exactly when n ∉ {2, 3, 4, 6} (the set must also contain 1, see "Findings about the paper" below),
and the paper estimates the critical radius r_crit(n) = sup{r : GG_n(r) finite} numerically, with
closed forms conjectured for n = 5, 8, 10, 12.

The repository contains a Lean 4 / Mathlib proof library, an exact computation engine written in
Lean, research notes, written proofs with independent referee reports, and small finiteness
certificates.

## Layout

| Path | Contents |
|---|---|
| `TDCSG/` | The proof library (Lean 4, Mathlib); `TDCSG.lean` is the root module. Compact statements of the main results are in `TDCSG/Statements.lean` |
| `TDCSG/Compound/` | The general definition: compound symmetry groups of an indexed family of closed balls in a pseudometric space, each ball carrying a group of its own isometries, and their general theorems; `TDCSG.GG` is the two-disk instance |
| `TDCSG/CriticalRadius/` | The critical radius `TDCSG.criticalRadius n`, the infinite orbits for n = 5, 8, 10, 12, the Galois-conjugate orbit structure for n = 5 (`FiveConjugate.lean`), the cut-set certificate definitions (`Certificate.lean`), and compact statements in `TDCSG/CriticalRadius/Statements.lean` |
| `TDCSGCompute/` | The exact engine and the `tdcsg-orbit` executable (core Lean, no Mathlib): orbits, threshold sweeps, GG_n(r) as a permutation group, cut-set certificates with an independent checker, and relative (window-clipped) certificates; see [`notes/engine.md`](notes/engine.md) |
| `certificates/` | Small finiteness certificates (`.cert`, format of [`notes/certificates.md`](notes/certificates.md)) and two small relative certificates at r_c (`.rcert`, format of [`notes/relative-certificates.md`](notes/relative-certificates.md)), with their SHA-256 sums |
| `notes/` | Research notes: [`overview.md`](notes/overview.md) (programme and conventions), [`arithmetic.md`](notes/arithmetic.md), [`analytic-continuation.md`](notes/analytic-continuation.md), [`experiments.md`](notes/experiments.md), [`engine.md`](notes/engine.md), [`certificates.md`](notes/certificates.md), [`gap-structure.md`](notes/gap-structure.md), [`rank-conjecture.md`](notes/rank-conjecture.md), [`large-n-table.md`](notes/large-n-table.md), [`relative-certificates.md`](notes/relative-certificates.md), [`open-problem-critical-radius.md`](notes/open-problem-critical-radius.md) (the critical-radius problem stated for specialists), [`ideas.md`](notes/ideas.md) (open directions), and the referee report [`referee-report-engine-campaign.md`](notes/referee-report-engine-campaign.md) |
| `notes/proofs/` | Written proofs, each with an independent referee report (`referee-report-*.md`) and, for the first Lean round, an independent Lean check (`lean-check-thread1.md`) |
| `2302.12950v1.pdf` | The paper |

## Building

The project uses Lean `v4.35.0` (see `lean-toolchain`) and Mathlib at revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` (see `lakefile.toml`). With
[elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get   # download the prebuilt Mathlib (large; skip if .lake/packages is already populated)
lake build
lake test            # self-test of the orbit engine
.lake/build/bin/tdcsg-orbit orbit -n 5 --r2 closed-1/100   # an exact orbit computation
```

`lake build` builds the proof library and the engine; `lake test` runs the engine's self-test
(known finite cases, rows of the certificate tables, tangency and cap cases, tampered
certificates). The commands that generate and check certificates, and the caps the large runs
need, are in [`notes/certificates.md`](notes/certificates.md); those for relative
(window-clipped) certificates at the critical radius, symmetry-reduced closures and intervals of
validity are in [`notes/relative-certificates.md`](notes/relative-certificates.md).

## Results

Every claim below has one of these statuses: **proved in Lean**; **refereed written proof** (a
note in `notes/proofs/` and an independent referee report); **proved modulo a certified
computation**; **computed, not certified**; **conjecture**; **open**.

### (a) Proved in Lean

No `sorry`, no `native_decide`, no extra axioms: every theorem of `TDCSG` depends only on
`propext`, `Classical.choice` and `Quot.sound`. Theorem names are in the namespaces
`TDCSG.Statements` (file `TDCSG/Statements.lean`) and `TDCSG.CriticalRadius` (file
`TDCSG/CriticalRadius/Statements.lean`), unless a file is named.

- **Definitions.** For a family of closed balls `closedBall (c i) (r i)` in a pseudometric space
  `X`, each with a group `H i` of isometries of the ball, `TDCSG.ballPerm` extends an isometry of
  a ball to a permutation of `X` (the identity outside the ball), and
  `TDCSG.compoundSymmetryGroup c r H` is the group of permutations of `X` generated by all these
  extensions (`TDCSG/Compound/Basic.lean`). The disks, the generators `permA`, `permB` as
  permutations of ℂ, the group `TDCSG.GG n₁ n₂ r₁ r₂`, orbits (`TDCSG/Basic.lean`,
  `TDCSG/Group.lean`): `GG` is the compound symmetry group of the two disks about ∓1, each with
  the cyclic group generated by its rotation, and `TDCSG.GG_eq_closure` shows it is the group
  generated by `permA n₁ r₁` and `permB n₂ r₂`. Also `TDCSG.criticalRadius n`, the infimum of the
  radii with infinite group (`TDCSG/CriticalRadius/Basic.lean`).
- **General compound symmetry groups** (`TDCSG/Compound/Basic.lean`). The extension is an
  injective homomorphism (`ballPerm_injective`); the group is monotone in the `H i`
  (`compoundSymmetryGroup_mono`), fixes every point outside the union of the balls and maps the
  union onto itself (`apply_eq_of_notMem_ballUnion`, `image_ballUnion`), so orbits lie in the
  union together with the base point (`orbit_subset_insert_ballUnion`); finitely many balls with
  finitely generated `H i` give a finitely generated group, which is finite as soon as its orbits
  are uniformly bounded (`finite_compoundSymmetryGroup_of_encard_orbit_le`); orbits are monotone
  in the balls (`orbit_subset_orbit_of_eqOn`, `finite_of_forall_orbit_subset`); for finitely
  many pairwise disjoint balls the group is the product of the `H i` (`mulEquivPi`,
  `natCard_compoundSymmetryGroup`). The monotonicity and disjoint-disk results below are
  corollaries.
- **Monotonicity.** Orbits grow with the radii (`orbit_mono`); finiteness of the group passes to
  smaller radii (`finite_GG_of_le`; also `infinite_GG_of_le`, `finite_GG_of_lt`,
  `infinite_GG_of_lt`).
- **The omitted half of Theorem 1.** If lcm(n₁, n₂) ∈ {1, 2, 3, 4, 6}, the orbits are uniformly
  bounded (`exists_encard_orbit_le`) and the group is finite for all radii, equal or unequal
  (`finite_GG`). The bounds are stated as existing; the written proof gives them explicitly.
- **Bounded orbits.** A finitely generated group acting faithfully with uniformly bounded orbits is
  finite (`finite_of_encard_orbit_le`).
- **Boundary contact.** A finite orbit is unchanged for slightly larger radii
  (`exists_orbit_eq_of_finite`); the radii at which a point has an infinite orbit are empty or a
  closed half-line [r₀, ∞) with r₀ > 1 (`infinite_orbit_radii`); at r₀ the orbit touches a boundary
  circle or accumulates on one from inside (`boundary_depth`,
  `touchesBoundary_or_accumulatesInside`, `of_not_touchesBoundary`).
- **Small radii.** For r₁, r₂ ≤ 1 every orbit is finite (`finite_orbit_of_le_one`); for equal
  radii r < 1 the group is finite (`finite_GG_of_lt_one`), which gives the lower bounds
  `one_le_criticalRadius_*` below.
- **Disjoint disks.** For r₁ + r₂ < 2 the group is isomorphic to C_{n₁} × C_{n₂} and has order
  n₁n₂ (`nonempty_mulEquiv_of_add_lt_two`, `card_GG_of_add_lt_two`).
- **Infinitude at the closed-form radii.** GG_n(r) is infinite for every r at or above
  √(3+φ) (n = 5, `infinite_GG_five`), √(10−5√2) (n = 8, `infinite_GG_eight`), √(4−φ) (n = 10,
  `infinite_GG_ten`) and √(40−22√3) (n = 12, `infinite_GG_twelve`), through explicit infinite
  orbits: of 0 for n = 5, 10 (`infinite_orbit_zero_five`, `infinite_orbit_zero_ten`), and of the
  lattice point p* for n = 8, 12 (`mem_orbit_pStar_eight_pow`, `mem_orbit_pStar_twelve_pow`,
  whose closure data are checked by kernel reduction, `decide +kernel`). Hence
  1 ≤ r_crit(n) ≤ the closed form for n = 5, 8, 10, 12 (`criticalRadius_five_le`,
  `criticalRadius_eight_le`, `criticalRadius_ten_le`, `criticalRadius_twelve_le` and
  `one_le_criticalRadius_*`).
- **The orbit structure for n = 5** (`TDCSG/CriticalRadius/FiveConjugate.lean`, namespace
  `TDCSG.Five`). The integer model of ℤ[ζ₅] is a commutative ring, and the Galois map σ: ζ ↦ ζ²
  is a ring homomorphism of it whose composite with the embedding is the second complex
  embedding (`Cyc.galois`, `Cyc.embed_galois`). Every element of GG_5(r) acts at each point as
  x ↦ ζʲx + t with t ∈ (1 − ζ)ℤ[ζ] (`exists_affine`); a subset of ℤ[ζ] bounded in both
  embeddings is finite (`Cyc.finite_setOf_norm_le`); and GG_5(r) is finite exactly when the
  Galois conjugates σ(t) of the translation parts are bounded
  (`finite_GG_iff_conjugatesBounded`), a condition that holds for r < 1 and fails for
  r ≥ √(3+φ). The unproved proposition `FiniteBelowClosedFormFive` (finiteness for every
  r < √(3+φ)) is equivalent to that condition below √(3+φ)
  (`TDCSG.Five.finiteBelowClosedFormFive_iff`) and implies `CriticalRadiusEqFive`
  (`criticalRadiusEqFive_of_finiteBelowClosedFormFive`).
- **From certificates to finiteness.** `TDCSG.finite_GG_of_certificate`
  (`TDCSG/CriticalRadius/Certificate.lean`): if the certificate theorem holds and a certificate
  exists at r₀, then GG_n(r) is finite for all r ≤ r₀; and `finiteBelowFive_of_certificate`,
  `le_criticalRadius_five_of_finiteBelow` and their analogues for n = 8, 12. The certificate
  theorem itself is the unproved proposition `TDCSG.CutSetCertificate n`, and the existence of a
  certificate is the unproved proposition `TDCSG.ExistsCertificate n r`; both enter only as
  hypotheses. So no Lean theorem yet gives finiteness at any r > 1 for n = 5, 8, 10, 12. The
  propositions `FiniteBelowFive`, `FiniteBelowEight`, `FiniteBelowTwelve` state finiteness at the
  refereed ranges δ = 1/10, 1/7, 1/20; there is no `FiniteBelowTen`. The exact values are the open
  propositions `CriticalRadiusEqFive`, `…Eight`, `…Ten`, `…Twelve`.

### (b) Refereed written proofs, not in Lean

- **Explicit bounds** behind the Lean statements: the orbit bound and group-order bound of the
  Theorem 1 converse, and the stability margin
  ([`theorem1-converse.md`](notes/proofs/theorem1-converse.md),
  [`boundary-contact.md`](notes/proofs/boundary-contact.md); report
  [`referee-report-thread1.md`](notes/proofs/referee-report-thread1.md)). The tangent case
  r₁ + r₂ = 2 with unequal radii, with |G| ≤ n₁n₂(n₁+n₂−1)! (Proposition 7.1(2) there), is wider
  than the Lean statement `finite_orbit_of_le_one`.
- **Analytic radius.** For n = 5 and n ≥ 7, invariant real-analytic functions on the two open
  disks are forced to be constant exactly when r > r_A(n) = sec(π/n)
  ([`analytic-radius.md`](notes/proofs/analytic-radius.md); report
  [`referee-report-thread6.md`](notes/proofs/referee-report-thread6.md)).
- **Regularity scale.** Classes with unique continuation have threshold r_A; bump-function
  classes have a threshold of at least max(2, d_n); on (r_A, max(2, d_n)) a log-convex
  Denjoy–Carleman class has only constant invariants if and only if it is quasi-analytic
  ([`regularity-scale.md`](notes/proofs/regularity-scale.md); report
  [`referee-report-regularity-scale.md`](notes/proofs/referee-report-regularity-scale.md)). Some
  parts written after the report are marked there as not yet refereed.
- **Theorem A for n = 5, 8, 10, 12** (the infinite orbits formalized above), with all data in the
  notes ([`critical-radius-n5.md`](notes/proofs/critical-radius-n5.md),
  [`critical-radius-n8.md`](notes/proofs/critical-radius-n8.md),
  [`critical-radius-n10.md`](notes/proofs/critical-radius-n10.md),
  [`critical-radius-n12.md`](notes/proofs/critical-radius-n12.md); reports
  [`…-n5`](notes/proofs/referee-report-critical-radius-n5.md),
  [`…-n8-n12`](notes/proofs/referee-report-critical-radius-n8-n12.md),
  [`…-n10`](notes/proofs/referee-report-critical-radius-n10.md)).
- **The cut-set certificate theorem.** A finite union of arcs satisfying (C1)–(C4) forces GG_n(r)
  to be finite (Theorem 4.2 of `critical-radius-n5.md`, Theorem 3.1 of `critical-radius-n8.md`).

**The sharp-lower-bound series.** Five refereed notes attack finiteness below the closed forms. None
proves it: **r_crit(n) = closed form remains open for all four n = 5, 8, 10, 12.** A self-contained
statement of the problem for specialists, with the current status of every ingredient, is
[`notes/open-problem-critical-radius.md`](notes/open-problem-critical-radius.md).

- **n = 5, non-norm radii** ([`sharp-lower-bound-n5.md`](notes/proofs/sharp-lower-bound-n5.md);
  report [`referee-report-sharp-lower-bounds.md`](notes/proofs/referee-report-sharp-lower-bounds.md)).
  Proved: at a radius r² that is not a norm from ℚ(ζ), (C3) and (C4) hold automatically and GG_5(r)
  is finite if and only if the cut-set closure terminates; the lattice window criterion; the
  Diophantine lune lemma and exact local renormalization at tight points (Lemma 2.2, Theorems 3.1,
  4.1, 4.3, Lemma 6.1, Proposition 6.2). Conjectured: termination along non-norm radii r_j ↑ r_c
  (Conjecture 8.1, equivalent to finiteness below r_c). Level two is computed, not certified.
- **n = 8, nested windows** ([`sharp-lower-bound-n8.md`](notes/proofs/sharp-lower-bound-n8.md); same
  report). Proved: orbit sizes are bounded by a product of restricted-orbit factors over nested
  windows, all but the innermost taken at r_c itself, and Conjecture S implies finiteness below
  √(10−5√2) (Theorems 5.3, 5.5, Corollary 5.7). Conjectured: Conjecture S. Evidence only
  (floating-point sampling): period-two renormalization of the induced pseudogroup.
- **Combined note, relative certificates** ([`sharp-lower-bound-combined.md`](notes/proofs/sharp-lower-bound-combined.md);
  report [`referee-report-sharp-lower-bound-combined.md`](notes/proofs/referee-report-sharp-lower-bound-combined.md)).
  Proved: one window-clipped closure at r_c bounds, for every r < r_c at once, the chains that avoid
  the windows, so finiteness below r_c reduces to bounded visits to the windows; (R-bulk) with
  (R-core) implies it (Theorem 4.2, Corollary 4.3, Propositions 4.4, 4.5, 6.3). Refuted (exact):
  level independence of the core orbit partition under φ⁻³ (levels 2 → 3).
- **n = 5, limit system** ([`sharp-lower-bound-limit-system.md`](notes/proofs/sharp-lower-bound-limit-system.md);
  report [`referee-report-sharp-lower-bound-limit-system.md`](notes/proofs/referee-report-sharp-lower-bound-limit-system.md)).
  Proved: the straight-cut limit of the fixed-word system is trivial (orbits of at most 190 points);
  modulo an exact computation, the nine non-tight critical classes are rigid from level 4, so the
  problem lives at the four tight points ±E, ±Ē; (R-bulk-t) with (R-core-t) implies finiteness
  (Theorems 4.2, 6.1, Corollaries 4.3, 4.4). Refuted (exact): φ⁻³ matching of first-return sets at
  the tight points, at every tested level pair up to 4 → 5. Conjectured: period two with unit φ⁻⁶
  (Conjecture 5.1).
- **n = 12** ([`sharp-lower-bound-n12.md`](notes/proofs/sharp-lower-bound-n12.md); report
  [`referee-report-sharp-lower-bound-n12.md`](notes/proofs/referee-report-sharp-lower-bound-n12.md)).
  Proved: 48 critical points in 12 classes; the levels m = 1, 2, 3 are norms; the lune lemma for
  n = 12, no parity obstruction, the frozen-point lemma; modulo an exact computation, 40 critical
  points are rigid from level 0; with certified relative certificates, finiteness below r_c reduces
  to the 8 tight points (Theorems 5.1, 5.4, Corollary 4.2, Lemmas 3.1, 3.3, 6.2, 6.3). Refuted
  (exact): the exact period-one inductive step from every starting level m₀ ≤ 3; whether it holds
  from a deeper level is open. Conjectured: eventual period one through monotone growth of
  first-return sets (§8; Proposition 8.1 there is not yet refereed).

### (c) Proved modulo a certified computation

GG_n(r) is finite for every r ≤ r_*, r_*² = r_c² − δ, by the certificate theorem (refereed, not in
Lean) applied to a certificate at r_* and group monotonicity. The ordinary cut-set certificates
were generated by `tdcsg-orbit certify` and accepted by `tdcsg-orbit check-certificate`, a separate
float-free checker sharing only the exact arithmetic layer; the four at δ = 1/55, 1/36, 1/47, 1/180
were regenerated byte for byte and re-checked in an independent verification. The checkers are
tested programs, not kernel-checked proofs; their correspondence with `TDCSG.ExistsCertificate` is
by inspection of the definitions; and the Lean theorem linking certificates to finiteness takes the
certificate theorem as the unproved hypothesis `CutSetCertificate`. Values are from
[`notes/certificates.md`](notes/certificates.md) and
[`notes/relative-certificates.md`](notes/relative-certificates.md) §10, which record every run and
checksum.

| n | r_c (proved in Lean to be an upper bound) | refereed r_* | best certified r_* (δ) | kind of certificate | open window r_c − r_* |
|---|---|---|---|---|---|
| 5 | √(3+φ) ≈ 2.148961 | 2.125567 (δ = 1/10) | 2.144727 (δ = 1/55) | ordinary cut-set certificate | 0.004235 |
| 8 | √(10−5√2) ≈ 1.711412 | 1.669154 (δ = 1/7) | 1.705008 (δ = 547/25000 = 0.02188) | symmetry-reduced window-free closure, (C1)–(C4) checked by `check-relative-certificate` (ordinary certificate at δ = 1/36, r_* = 1.703278) | 0.006404 |
| 10 | √(4−φ) ≈ 1.543362 | 1.522979 (δ = 1/16) | 1.536454 (δ = 1/47); 1.536455 (r² < ρ₁, δ ≈ 0.0212735) by the interval of validity | ordinary cut-set certificate, extended by the interval of validity | 0.006908 |
| 12 | √(40−22√3) ≈ 1.376547 | 1.358264 (δ = 1/20) | 1.374528 (δ = 1/180); r² < ρ₁, δ ≈ 0.0055543, by the interval of validity | ordinary cut-set certificate, extended by the interval of validity | 0.002019 |

"Refereed r_*" is the range whose computation was reproduced during refereeing (by an independent
implementation) and is the range of the Lean propositions `FiniteBelow…`. The open window
(r_*, r_c) is open in every case. Since r_* > r_A(n) in all four cases, r_A < r_crit holds there
modulo the same computations. The best entries for n = 8, 10, 12 rest on arguments proved in
`relative-certificates.md` and refereed correct in
[`notes/proofs/referee-report-relative-certificates.md`](notes/proofs/referee-report-relative-certificates.md):

- **n = 8.** The closure stores one circle per orbit of z ↦ ±z, ±z̄; the union of the listed arcs
  and their images is an ordinary certificate because the system is invariant under these
  symmetries (§§2, 7 there). It lies past the level-5 jump δ₅ ≈ 0.0272 of
  `sharp-lower-bound-n8.md`, and gives the base (levels 4 and 5) of its Conjecture S for phases
  θ* ≥ 0.80014 (the note's θ* = 4/5 puts r_5 at δ ≈ 0.0218762, just beyond it). During refereeing
  the file was regenerated byte for byte and accepted again by the relative checker, which is the
  only checker that has read it.
- **n = 10, 12.** `tdcsg-orbit validity-interval` computes the exact radius ρ₁ at which the symbolic
  arcs of the δ = 1/47 and δ = 1/180 certificates stop being valid, so GG_n(r) is finite for every
  r² < ρ₁ (§8 there). The same arcs moved to a radius just below ρ₁ were accepted by
  `check-certificate`. The gain in δ is about 2·10⁻⁴ relative.

**Relative certificates at r_c** (`tdcsg-orbit certify-relative` and
`check-relative-certificate`; `relative-certificates.md` §§5–6). Restricted (window-clipped)
closures at r_c itself, checked float-free from the file alone, including the critical points and
the exact disjointness of the windows: for n = 5, windows 1–8 of `sharp-lower-bound-combined.md`
Table 5.1, with circle and maximal-arc counts equal to that note's (window 9 was not run, for lack
of memory); for n = 8 one window shape, for n = 10 two and for n = 12 four. Through the refereed
Theorem 4.2 of the combined note (with the general-n bound 1 + 20nF of `relative-certificates.md`
§2, refereed correct) each gives a uniform bound on window-avoiding chains for all r < r_c, not
finiteness of any GG_n(r). Exact coincidences (three circles through one point) are not confined
to the windows: for one n = 5 window, 248 of 579 lie in the bulk; the theorem needs no hypothesis
on them. The largest n = 5 window is also certified by the referee's interval-arithmetic
checker (outside the repository; `mpmath.iv` trusted).

**Theorem H** (`relative-certificates.md` §9; proved there, refereed correct after minor fixes): a
finite arc set containing both boundary circles and closed under the four rotations on
non-degenerate components, with no tangency or endpoint condition, makes GG_n(r') finite for every
r' < r; this makes a windowed storage of a cut set (a hybrid certificate) valid. A prototype hybrid
generator saved at most about 2.5× in memory, not enough for n = 5 level two, and was not developed
into a certificate format or checker.

### (d) Computed, not certified

- **n = 5, level two.** The cut set at δ = (13 − 8φ)/10 (r ≈ 2.147664) closes in one C program
  with floating-point ordering and a hard-coded error bound, outside the repository; no
  independent check ([`sharp-lower-bound-n5.md`](notes/proofs/sharp-lower-bound-n5.md) §5).
- **n = 12 at δ = 1/250.** The symmetry-reduced window-free closure closes, with (C3) and (C4)
  holding in the generator, but its check was stopped unfinished, so it is not certified
  (`relative-certificates.md` §7). It lies between levels 2 and 3 of `sharp-lower-bound-n12.md`.
- **Restricted closure for n = 5** at window 9 (the smallest) of `sharp-lower-bound-combined.md`
  Table 5.1: one floating-point program (`rcut.c`) only.
- **Single orbits.** The orbit of 0 for n = 5 is finite for r ≤ r_3 (r_c − r_3 ≈ 3.1·10⁻⁴), by an
  exact breadth-first search reproduced by the engine; this concerns one orbit, not the group.
- **Group orders inside the continuation gap** (r_A, r_c): certified lower bounds from generic
  orbits; that they are the orders depends on the sampling being complete
  ([`gap-structure.md`](notes/gap-structure.md)).
- **Rank conjecture data** for n = 7, 9, 11, 13 ([`rank-conjecture.md`](notes/rank-conjecture.md)).
- **The large-n table**: at r = g(33) the exact engine finds the tested orbits finite and moderate;
  the question is undetermined ([`large-n-table.md`](notes/large-n-table.md)).
- **Renormalization evidence**: sampled germ sets and zoomed induced partitions for n = 8
  (floating-point sampling, `sharp-lower-bound-n8.md` §6), core-visit counts for n = 5
  (`sharp-lower-bound-combined.md` §6.3), and the exploratory numbers of
  [`experiments.md`](notes/experiments.md) and [`arithmetic.md`](notes/arithmetic.md), of which
  those listed in [`engine.md`](notes/engine.md) have been reproduced exactly.

### (e) Open problems and conjectures

- **r_crit(n) equals the closed form for n = 5, 8, 10, 12** (finiteness on the open windows above):
  open for all four n. Current reductions, from the sharp-lower-bound series in (b): for n = 5,
  finiteness below r_c is equivalent to termination of the cut-set closure along non-norm radii
  r_j ↑ r_c, and follows from (R-bulk-t) with (R-core-t), statements about the four tight points;
  for n = 8 it follows from Conjecture S; for n = 12 it follows from statements about the 8 tight
  points. The renormalization these need is not found: exact φ⁻³ matching is refuted for n = 5,
  exact period one from levels m₀ ≤ 3 is refuted for n = 12, and period two (n = 5) and eventual
  period one through monotone growth (n = 12) are conjectures. n = 10 has no note of its own; its relative certificates at r_c give the window reduction
  through the general-n form of Theorem 4.2 (refereed correct in
  [`notes/proofs/referee-report-relative-certificates.md`](notes/proofs/referee-report-relative-certificates.md)).
  [`notes/open-problem-critical-radius.md`](notes/open-problem-critical-radius.md) states the
  problem for specialists, with questions.
- **The paper's footnote 4**: whether the group is infinite at the group-level critical radius. The
  per-point version is proved (above); the group version is open.
- **The rank conjecture**: the self-similarity is governed by the unit group of ℤ[ζ_n]⁺.
- **The large-n entries** of the paper's critical-radius table: true critical radii, or the onset
  of very large finite orbits.
- Further conjectures (r_c(n)² ∈ ℚ(ζ_n)⁺ for all n, complex dimensions of the critical fractal) are
  in [`overview.md`](notes/overview.md); open directions are collected in
  [`ideas.md`](notes/ideas.md).

### (f) Findings about the paper

- **Theorem 1, "if" direction.** It needs n₁, n₂ ≥ 2: for n₁ = 1, n₂ = 5 the group is ⟨b⟩ ≅ C_5 for
  every radius although lcm = 5 ∉ {2, 3, 4, 6}. The finiteness direction holds with lcm ∈
  {1, 2, 3, 4, 6} ([`theorem1-converse.md`](notes/proofs/theorem1-converse.md), Remark 8.2).
- **Monotonicity.** The paper's justification ("all group elements that affect it are still
  available") is imprecise: the same word acts differently at different radii, and there is no
  generator-preserving homomorphism between the groups. The conclusion is correct and is proved,
  in writing and in Lean ([`boundary-contact.md`](notes/proofs/boundary-contact.md), Example 3.2,
  Theorems 3.1, 3.4).
- **The closed forms for n = 8 and 12** were derived from the assumption that a limit point lies on
  a disk boundary. Infinitude at those radii is proved without it (in writing and in Lean):
  the limit point is a lattice point p* that lies on ∂D_L exactly at r_c. That these radii are the
  critical radii is open, as for n = 5 and 10. The paper's description of segments that "traverse
  angles of π/8" (n = 8) was not reproduced; the approach to p* found here is along a straight line
  ([`critical-radius-n8.md`](notes/proofs/critical-radius-n8.md) §2.6).
- **n = 10.** The paper's estimate 1.543357 lies just below the closed form √(4−φ) ≈ 1.543362,
  inside the open window, consistent with the stated accuracy of the table.

## Related material outside this repository

A comparison of the two-disk systems with an announced proof of the generalized Riemann hypothesis
and with the Hilbert–Pólya programme is kept outside this repository, in the owner's
riemann-hypothesis repository; see [`notes/overview.md`](notes/overview.md) §6.

## Licence and authors

Apache License 2.0; see [`LICENSE`](LICENSE). Authors: Eric Vergo and Claude (Anthropic). Lean
files carry a licence line and an `Authors: Eric Vergo, Claude` line, with no copyright line; notes
carry an authors line.
