# Two-disk compound symmetry groups: research overview

Authors: Eric Vergo and Claude (Anthropic).

This note collects what is currently known or suspected about the two-disk systems GG_n(r) of
*Two-Disk Compound Symmetry Groups* (Hearn, Kretschmer, Rokicki, Streeter, Vergo, arXiv:2302.12950)
beyond the paper itself, and sets out a research program. The detailed material is in
[`arithmetic.md`](arithmetic.md), [`analytic-continuation.md`](analytic-continuation.md) and
[`experiments.md`](experiments.md). Written proofs are in [`proofs/`](proofs/).

## Conventions

### Labels

Each claim carries one label:

- **[proved]**: a short argument has been written out (by a model; not independently refereed);
- **[computed]**: found by computation;
- **[classical]**: a known theorem applied to this setting;
- **[conjecture]**: precise and testable, not tested;
- **[analogy]**: suggestive only.

### Preliminary numbers

Every number marked **preliminary** comes from exploratory Python scripts that are not part of this
repository. Those scripts store orbit points exactly, as integer vectors in ℤ[ζ_n], but decide
membership in the closed disks in double-precision floating point, with a tolerance of 1e-12 for
boundary ties. Results that sit exactly on a threshold (r = g(n), the second threshold r₁, the count
n² − 3n + 1, boundary contact) depend on how points on a boundary circle are classified, so they are
preliminary until an exact orbit engine (membership decided by the sign of |z ∓ 1|² − r² computed
exactly in ℤ[ζ_n]⁺) has reproduced them. That engine is planned in Lean. Values of r_c(n) quoted
without that mark are from the paper's Appendix A (six decimals, good to about 5e-6).

### Notation

- ζ = ζ_n = e^{2πi/n}; K = ℚ(ζ_n), a CM field; K⁺ = ℚ(ζ_n)⁺ = ℚ(cos 2π/n), its maximal real subfield;
  O = ℤ[ζ_n]; φ(n) is Euler's function and φ = (1 + √5)/2 the golden ratio.
- D_L(r) and D_R(r) are the closed disks of radius r about −1 and 1.
- a(z) = ζ⁻¹(z + 1) − 1 on D_L(r) and the identity elsewhere; b(z) = ζ⁻¹(z − 1) + 1 on D_R(r) and the
  identity elsewhere. Both rotate clockwise by 2π/n. GG_n(r) = ⟨a, b⟩. These are `TDCSG.genA` and
  `TDCSG.genB` in the Lean sources.
- r_c(n) is the critical radius: the least r at which GG_n(r) is infinite.
- g(n) = |2 − ζ_n| = √(1 + 8 sin²(π/n)).

### Closed forms of r_c²

The four known closed forms are written throughout these notes as elements a + b√d of K⁺:

| n | r_c(n)² | product form | minimal polynomial of r_c(n)² |
|---|---|---|---|
| 5 | 3 + φ | (a prime of norm 11) | x² − 7x + 11 |
| 10 | 4 − φ | (the Galois conjugate of 3 + φ) | x² − 7x + 11 |
| 8 | 10 − 5√2 | 5 · √2 · (√2 − 1) | x² − 20x + 50 |
| 12 | 40 − 22√3 | 2 · (7 − 2√3) · (2 − √3) | x² − 80x + 148 |

The product forms show the scale units √2 − 1 = tan(π/8) and 2 − √3 = tan(π/12) as factors. The
closed forms for n = 8 and 12 rest on the paper's assumption that a certain limit point lies on a disk
boundary; see §4.

## 1. Summary

1. **What GG_n(r) is, arithmetically** [proved]. Every element acts on each piece as z ↦ ζ^j z + t
   with t in the ideal (1 − ζ_n) of ℤ[ζ_n]. So GG_n(r) is the discrete group μ_n ⋉ (1 − ζ_n), cut
   down by a disk-shaped window at one archimedean place. An orbit is finite exactly when its images
   under the other complex embeddings of ℚ(ζ_n) stay bounded.
2. **The dynamics picks out the unit group** [computed, preliminary]. For n = 5, 8, 10, 12 the orbit
   size grows like a power of 1/(r_c − r) with a log-periodic oscillation. The period is the
   logarithm of a unit: φ³, 1 + √2, φ³, 2 + √3. Three independent computations agree on these units.
3. **Through the units, the system carries L-values at s = 1** [classical]. For D = 5, 8, 12,
   log ε_D = (√D/2)·L(1, χ_D) by the class number formula. Experiments found no trace of L-values
   beyond what the regulator already encodes.
4. **The most valuable outputs concern the two-disk systems themselves**: a proof of the half of
   Theorem 1 that the paper omits, a boundary-contact theorem at the critical radius, a baseline
   formula for r_c(n), a rank explanation for the n = 7 anomaly, and a possible issue with the large-n
   entries of the critical-radius table (§5).

## 2. The arithmetic structure of GG_n(r)

Details in [`arithmetic.md`](arithmetic.md).

- **Ideal** [proved]. The orbit of the origin spans exactly the ideal (1 − ζ_n). On the whole plane,
  the two rotations generate the translations by 2(1 − ζ)ℤ[ζ_n] together with the rotations by μ_n;
  GG_n(r) is the cut-down of that group to the two disks.
- **Finiteness criterion** [proved]. An orbit is finite if and only if the Galois conjugates of its
  translation parts stay bounded.
- **The omitted half of Theorem 1** [proved]. If lcm(n₁, n₂) ∈ {2, 3, 4, 6}, the ambient group is a
  discrete group of plane motions, so its cut-down to two disks is finite for every r. The underlying
  reason is that ℚ(cos 2π/n) = ℚ, i.e. the unit group of ℤ[ζ_n] is finite. This is the
  crystallographic restriction read as Dirichlet's unit theorem in rank zero.
- **Galois acts on the family, not on one system** [proved]. Conjugation permutes φ(n)/2 versions of
  the system, each windowed at a different archimedean place. Dirichlet characters mod n can enter
  only this way, and only even ones.
- **Not a fixed-window cut-and-project set** [computed, preliminary]. The conjugate spread of an orbit
  of size N grows like N^0.55–0.6.
- **n ↔ 2n** [computed]. r_c(10)² = 4 − φ is the Galois conjugate of r_c(5)² = 3 + φ. A search for the
  same relation for (7, 14) and (9, 18) at the table's precision found nothing (preliminary).

## 3. Units, regulators and renormalization

- **Closed forms occur exactly when ℚ(ζ_n)⁺ is quadratic**, i.e. φ(n) = 4: n = 5, 8, 10, 12. These are
  the cases of unit rank 1 [computed, against the paper's table].
- **Scale units divide r_c²** [computed]: see the product forms above.
- **Growth law** [computed, preliminary]. N(r) ~ (r_c − r)^(−α) with α ≈ 1.7–1.9, modulated
  log-periodically with period the logarithm of the conjugate unit. Extrapolating the thresholds
  recovers the known r_c to about 1e-6.
- **Rank conjecture** [conjecture]. The self-similarity group of the characteristic fractal is the
  group of cyclotomic units, of rank φ(n)/2 − 1.
  - For rank 1 there is exact one-scale self-similarity.
  - For n = 7 the rank is 2, so two independent scalings compete. Experiments see several unequal
    scale ratios there (preliminary). This would explain the pattern change the paper reports after a
    zoom of about 500,000.
  - A mechanism to test: periodic renormalization of interval exchanges over quadratic fields
    (Boshernitzan–Carroll; from memory, to be checked).
- **Complex dimensions** [conjecture]. An orbit-counting zeta function Σ (r_c − r_k)^s over the radii
  r_k at which the orbit grows would have poles on a vertical line with spacing 2π / log ε. This is
  the Lapidus picture of fractal strings (from memory, to be checked). The log-periodic oscillation is
  its numerical signature.

## 4. The analytic-continuation analogy

Details in [`analytic-continuation.md`](analytic-continuation.md).

- **Boundary contact** [proved]. If a point's orbit is infinite at radius r₀ and finite at radii
  arbitrarily close below r₀, the orbit accumulates on a boundary circle from inside. This is the
  analogue of "a power series has a singularity on its circle of convergence". It does not show that
  the paper's specific limit point lies on the boundary, which the closed-form radii for n = 8 and 12
  need.
- **Hecke groups** [proved/classical]. Adding the half-turn that swaps the disks gives a Euclidean
  Hecke group; for n = 3, 6 it is the (2,3,6) triangle group. The set {2, 3, 4, 6} also marks the
  arithmetic Hecke groups, for the same reason (ℚ(cos 2π/n) = ℚ), and the finiteness criterion has
  the shape of Takeuchi's arithmeticity criterion (from memory, to be checked).
- **The analogy inverts** [conjecture]. For functions invariant under both disk rotations, the
  identity theorem spreads the two local symmetries into the dense global group. Such functions
  should be forced to vanish above a radius r_A < r_c. So GG_n(r) staying finite up to r_c measures
  the *failure* of analytic continuation for piecewise maps. The gap r_c − r_A is computable.

## 5. Findings about the critical-radius table

Details in [`experiments.md`](experiments.md). All findings in this section are preliminary.

- **Baseline** [computed]. r_c(n) ≥ g(n) for all 95 table entries. g(n) is the radius at which the two
  n-gon orbits of the origin first touch. For n ≥ 79 every entry equals g(n) to rounding, except
  n = 84. Hence n²(r_c − 1) → 4π², which is geometry.
- **n ≡ 4 mod 8** [computed, preliminary]. At r = g the origin's orbit has exactly n² − 3n + 1 points
  (n = 12, …, 100). It stays that size until a second threshold
  r₁² = 1 + 8s² + 512 s⁶(1 − s²), s = sin(π/n). The table's excess r_c − g tracks r₁ − g.
- **Open issue** [computed, preliminary, unresolved]. An infinite orbit at r ≈ g(n) could not be
  reproduced for large n. For n = 33 the origin's orbit stays at 65,089 points up to g + 5e-5, and
  random lens points stay finite. Either the infinite orbits sit on a thin set the search missed, or
  the large-n table entries mark the onset of very large finite orbits and not the true critical
  radius. Because these runs sit exactly at r = g, the floating-point membership test matters here
  most.
- **No arithmetic residue** [computed, preliminary]. Residuals of r_c(n) from the smooth curve do not
  correlate with h⁻, |L'/L(1, χ)|, φ(n)/n, the number of prime factors, or primality
  (all |ρ| ≤ 0.24). Nothing special appears at n = 23.

## 6. What does not enter the dynamics

- Class numbers, including n = 23: the class group never enters the dynamics.
- p-adic objects (Iwasawa theory, Ferrero–Washington): the two-disk side is archimedean.
- A Hilbert–Pólya operator from a single GG_n(r): the natural operators have pure point or Poisson
  spectra, and every length or scaling lies in a finitely generated group.

A comparison of the two-disk systems with an announced proof of the generalized Riemann hypothesis
and with the Hilbert–Pólya programme is kept outside this repository, in the owner's
riemann-hypothesis repository (`analysis/TWO_DISK_HILBERT_POLYA.md`). Its conclusion is that the
connection is thin, so this repository concentrates on the two-disk mathematics.

## 7. Research program

1. **Write up and formalize the two proved results**: the omitted half of Theorem 1 and the
   boundary-contact theorem. Written proofs go in [`proofs/`](proofs/); Lean statements and proofs in
   `TDCSG/`.
2. **Build an exact orbit engine** that decides disk membership exactly, and use it to confirm or
   correct every preliminary number in these notes.
3. **Settle the large-n table question** (§5): find an infinite orbit at r ≈ g(n) for some n ≥ 30, or
   revise what the table reports.
4. **Test the rank conjecture** with deep exact orbits for n = 7, 9, 11, 13: do the scale ratios form a
   two-unit regulator lattice?
5. **Prove periodic renormalization for φ(n) = 4**, which would prove the closed forms for n = 8, 12
   (and the limit-point assumption) and identify the scale unit.
6. **Compute the orbit-counting zeta function** and its poles for n = 5, 8, 12.
7. **Measure r_A against r_c** (§4).
8. **Assemble over n**: look for a single object built from all GG_n whose partition function is an
   Euler product. This is speculative.

## 8. What was and was not checked

- The class-number identity was checked numerically to 15 digits, Φ_n(1) for n ≤ 16, and the n = 5/10
  conjugacy.
- The baseline formula g(n) was checked against all 95 table entries by one computation, and against
  n = 79 and n = 100 by hand.
- Orbit computations stored points exactly in ℤ[ζ_n] but tested disk membership in floating point;
  two independent scripts agree on the units. See "Preliminary numbers" above.
- The two proofs in §2 and §4 were each written by one model and have not been refereed.
- Literature citations marked "from memory, to be checked" need checking before use.
- Everything labelled [conjecture] or [analogy] is untested.
