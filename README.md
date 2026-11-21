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
| `TDCSG/CriticalRadius/` | The critical radius `TDCSG.criticalRadius n`, the infinite orbits for n = 5, 8, 10, 12, the cut-set certificate definitions (`Certificate.lean`), and compact statements in `TDCSG/CriticalRadius/Statements.lean` |
| `TDCSGCompute/` | The exact engine and the `tdcsg-orbit` executable (core Lean, no Mathlib): orbits, threshold sweeps, GG_n(r) as a permutation group, cut-set certificates with an independent checker, and relative (window-clipped) certificates; see [`notes/engine.md`](notes/engine.md) |
| `certificates/` | Small finiteness certificates with their SHA-256 sums, in the format of [`notes/certificates.md`](notes/certificates.md) |
| `notes/` | Research notes: [`overview.md`](notes/overview.md) (programme and conventions), [`arithmetic.md`](notes/arithmetic.md), [`analytic-continuation.md`](notes/analytic-continuation.md), [`experiments.md`](notes/experiments.md), [`engine.md`](notes/engine.md), [`certificates.md`](notes/certificates.md), [`gap-structure.md`](notes/gap-structure.md), [`rank-conjecture.md`](notes/rank-conjecture.md), [`large-n-table.md`](notes/large-n-table.md), [`ideas.md`](notes/ideas.md) (open directions), and the referee report [`referee-report-engine-campaign.md`](notes/referee-report-engine-campaign.md) |
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
need, are in [`notes/certificates.md`](notes/certificates.md).

## Results

Every claim below has one of these statuses: **proved in Lean**; **refereed written proof** (a
note in `notes/proofs/` and an independent referee report); **proved modulo a certified
computation**; **computed, not certified**; **conjecture**; **open**.

### (a) Proved in Lean

No `sorry`, no `native_decide`, no extra axioms: every theorem of `TDCSG` depends only on
`propext`, `Classical.choice` and `Quot.sound`. Theorem names are in the namespaces
`TDCSG.Statements` (file `TDCSG/Statements.lean`) and `TDCSG.CriticalRadius` (file
`TDCSG/CriticalRadius/Statements.lean`), unless a file is named.

- **Definitions.** The disks, the generators `permA`, `permB` as permutations of ℂ, the group
  `TDCSG.GG n₁ n₂ r₁ r₂`, orbits (`TDCSG/Basic.lean`, `TDCSG/Group.lean`), and
  `TDCSG.criticalRadius n`, the infimum of the radii with infinite group
  (`TDCSG/CriticalRadius/Basic.lean`).
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
- **Non-norm radii and the lattice window criterion.** At a radius r² that is not a norm from
  ℚ(ζ), conditions (C3) and (C4) hold automatically and GG_n(r) is finite if and only if the
  cut-set closure terminates; the Diophantine lune lemma and exact local renormalization at tight
  points ([`sharp-lower-bound-n5.md`](notes/proofs/sharp-lower-bound-n5.md), Lemma 2.2,
  Theorems 3.1, 4.1, 4.3, Lemma 6.1, Proposition 6.2; report
  [`referee-report-sharp-lower-bounds.md`](notes/proofs/referee-report-sharp-lower-bounds.md)).
- **Nested-window reduction.** Orbit sizes are bounded by a product of restricted-orbit factors
  over nested windows, all but the innermost taken at the critical radius itself; Conjecture S
  implies finiteness below √(10−5√2) for n = 8
  ([`sharp-lower-bound-n8.md`](notes/proofs/sharp-lower-bound-n8.md), Theorems 5.3, 5.5,
  Corollary 5.7; same report).
- **Relative-certificate theorem.** One window-clipped closure at r_c bounds, for every r < r_c at
  once, the chains that avoid the windows; so finiteness below r_c reduces to the windows, and
  (R-bulk) with (R-core) implies it
  ([`sharp-lower-bound-combined.md`](notes/proofs/sharp-lower-bound-combined.md), Theorem 4.2,
  Corollary 4.3, Propositions 4.4, 4.5, 6.3; report
  [`referee-report-sharp-lower-bound-combined.md`](notes/proofs/referee-report-sharp-lower-bound-combined.md)).

### (c) Proved modulo a certified computation

GG_n(r) is finite for every r ≤ r_*, r_*² = r_c² − δ, by the certificate theorem (refereed, not in
Lean) applied to a cut-set certificate at r_* and group monotonicity. Each certificate below was
generated by `tdcsg-orbit certify` and accepted by `tdcsg-orbit check-certificate`, a separate
float-free checker sharing only the exact arithmetic layer, and the four deepest were regenerated
byte for byte and re-checked in an independent verification. The checker is a tested program, not
a kernel-checked proof; its correspondence with `TDCSG.ExistsCertificate` is by inspection of the
definitions; and the Lean theorem linking certificates to finiteness takes the certificate theorem
as the unproved hypothesis `CutSetCertificate`. Values are from
[`notes/certificates.md`](notes/certificates.md), which records every run and checksum.

| n | r_c (proved in Lean to be an upper bound) | refereed r_* | certified r_* (δ) | open window r_c − r_* |
|---|---|---|---|---|
| 5 | √(3+φ) ≈ 2.148961 | 2.125567 (δ = 1/10) | 2.144727 (δ = 1/55) | 0.004235 |
| 8 | √(10−5√2) ≈ 1.711412 | 1.669154 (δ = 1/7) | 1.703278 (δ = 1/36) | 0.008135 |
| 10 | √(4−φ) ≈ 1.543362 | 1.522979 (δ = 1/16) | 1.536454 (δ = 1/47) | 0.006908 |
| 12 | √(40−22√3) ≈ 1.376547 | 1.358264 (δ = 1/20) | 1.374528 (δ = 1/180) | 0.002019 |

All four are ordinary cut-set certificates. "Refereed r_*" is the range whose computation was
reproduced during refereeing (by an independent implementation) and is the range of the Lean
propositions `FiniteBelow…`. The open window (r_*, r_c) is open in every case. Since r_* > r_A(n)
in all four cases, r_A < r_crit holds there modulo the same computations.

For n = 5 one restricted (window-clipped) closure at r_c itself, for the largest window of
`sharp-lower-bound-combined.md` Table 5.1, was certified by the referee's interval-arithmetic
checker (outside the repository; `mpmath.iv` trusted). It gives a uniform excursion bound for all
r < r_c (Theorem 5.2 there), not finiteness of any GG_5(r).

### (d) Computed, not certified

- **n = 5, level two.** The cut set at δ = (13 − 8φ)/10 (r ≈ 2.147664) closes in one C program
  with floating-point ordering and a hard-coded error bound, outside the repository; no
  independent check ([`sharp-lower-bound-n5.md`](notes/proofs/sharp-lower-bound-n5.md) §5).
- **Restricted closures for n = 5** at the eight smaller windows of
  `sharp-lower-bound-combined.md` Table 5.1: two by two independent floating-point programs, six by
  one program only.
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

- **r_crit(n) equals the closed form for n = 5, 8, 10, 12** (finiteness on the open windows above).
  Current reductions: for n = 5, finiteness below r_c is equivalent to termination of the cut-set
  closure along non-norm radii r_j ↑ r_c (`sharp-lower-bound-n5.md`, Conjecture 8.1), and follows
  from (R-bulk) together with (R-core) (`sharp-lower-bound-combined.md`, Proposition 6.3); for
  n = 8 it follows from Conjecture S (`sharp-lower-bound-n8.md` §5.5). The literal "exact
  rescaling" of the n = 5 core partition is refuted at levels 2 → 3.
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
  a disk boundary. Infinitude at those radii is now proved without it (in writing and in Lean):
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
