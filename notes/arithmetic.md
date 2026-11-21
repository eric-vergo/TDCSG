# The arithmetic of two-disk systems

Authors: Eric Vergo and Claude (Anthropic).

A research note on the number theory behind GG_n(r): the cyclotomic lattice its orbits live in, the
role of units, and what does not enter. Labels, notation and the closed forms of r_c² follow
[`overview.md`](overview.md). Numbers marked *preliminary* come from exploratory Python scripts
(points exact in ℤ[ζ_n], disk membership in floating point, tolerance 1e-12) and await the exact
engine; see the overview.

Further notation: d = φ(n). "Internal space" means the complex embeddings σ_k (k ≠ ±1) of K other
than the identity and its conjugate, as in cut-and-project (model-set) constructions.

## 0. Basic structural facts

1. **Orbits live in an ideal coset** [proved]. Rotation about c = ±1 is w ↦ ζ⁻¹w + c(1 − ζ⁻¹). So every
   element of GG_n(r) sends a point z, on each piece, to some ζ^j z + t with t ∈ 𝔞 := (1 − ζ)O. The
   affine group involved is μ_n ⋉ 𝔞. For n = ℓ^k, 𝔞 is the totally ramified prime above ℓ. For any
   other n, 1 − ζ is a unit and 𝔞 = O.
2. **Finite ⇔ bounded in internal space** [proved]. O is a lattice in K ⊗ ℝ = ℂ^{d/2} (the Minkowski
   embedding). An orbit of a point of O is bounded in the physical coordinate (it stays in the two
   disks). So it is finite if and only if its images σ_k(orbit) are bounded for every k. An infinite
   orbit is the same thing as **escape to infinity in internal space**.
   - The "only if" half of Theorem 1 is a corollary. For n ∈ {1, 2, 3, 4, 6}, d ≤ 2, so there is no
     internal space and O is discrete in ℂ. For general z, the orbit sits in finitely many cosets
     ζ^j z + 𝔞.
   - The condition d ≤ 2 is the same as "the unit rank of K⁺ is 0". The crystallographic restriction
     and the Dirichlet unit theorem meet here: a coincidence of conditions, not of mechanisms.
3. **Galois conjugation acts on the family, not on the system** [proved]. σ_k carries the orbit of 0
   under GG_n(r) to the orbit of 0 under the "same" maps (rotation by ζ^{−k} about ±1). Those maps are
   now gated by a window in the σ_k⁻¹-coordinate. So Gal(K/ℚ)/±1 permutes d/2 windowed systems; it is
   not a symmetry of any one of them. The only symmetries of one system are z ↦ −z (which swaps the
   disks) and complex conjugation (which inverts a and b), a Klein four-group.
4. **The window is a single archimedean place** [proved]. GG_n(r) is the discrete group μ_n ⋉ 𝔞 ⊂
   ∏_v Aff(ℂ_v) with a compact window imposed at one archimedean place v₁ and none at the others. This
   makes it a pseudogroup of cut-and-project type. The critical radius r_c is the window size at which
   the window stops confining the internal dynamics.

## 1. Dictionary

| Two-disk object | Arithmetic object | Label |
|---|---|---|
| Positions reachable from 0 | the ideal 𝔞 = (1 − ζ_n) ⊂ ℤ[ζ_n] | [proved] |
| Generators a, b | μ_n = U(1)(K/K⁺)(O) acting on the rank-1 Hermitian lattice (O, xȳ), plus translations | [proved] |
| Finite for all r ⇔ n ∈ {1, 2, 3, 4, 6} | O discrete in ℂ ⇔ φ(n) ≤ 2 ⇔ the unit rank of K⁺ is 0 | [proved] |
| Infinite orbit | escape in internal space Σ_{k≠±1} ℂ_{σ_k} | [proved] |
| Exact self-similarity, closed-form r_c (n = 5, 8, 10, 12) | [K⁺ : ℚ] = 2 exactly for these n; interval exchanges over quadratic fields have eventually periodic Rauzy induction (Boshernitzan–Carroll, from memory, to be checked) | [computed] for the coincidence; [conjecture] for the mechanism (C1) |
| Scale factor of the fractal | a unit of K⁺: √2 − 1 = tan(π/8), 2 − √3 = tan(π/12), φ⁻³ for n = 5 (measured, preliminary) | [computed] |
| Growth of an orbit in internal space per generation | the conjugate of the scale unit, \|σ(ε)\| = ε⁻¹ | [computed, preliminary] (§3.2) |
| r_c² | a totally positive element of O⁺ that is a relative norm N_{K/K⁺} (because r_c = \|p + 1\| with p ∈ K) | [proved] that it is a norm, where r_c = \|p + 1\| |
| Prime factors of r_c² | an inert prime, a ramified prime, a split prime above 37, and the scale unit (§3.1) | [computed]; significance [analogy] |
| r_c(10)² = σ(r_c(5)²) | Galois conjugation inside ℚ(√5) | [computed] as an identity; not found for (7, 14), (9, 18) (§3.4) |
| GG_{2^k}, k → ∞ | the tower ℚ(ζ_{2^k})⁺, Galois group (ℤ/2^k)^×/±1 | [analogy] for any dynamical meaning |
| r_c(n) → 1 | n²(r_c − 1) → about 39.5 ≈ 4π²: archimedean geometry | [computed]; *not* arithmetic (§3.3) |
| n = 23 "two pieces" | h(ℚ(ζ₂₃)) = 3 | numerology only: the class group does not enter the dynamics (§4) |
| n = 7 pattern break at zoom about 5·10⁵ | [K⁺ : ℚ] = 3: unit rank 2, no periodic renormalization theorem; Pisot unit 1 + 2cos(2π/7) ≈ 2.247 | [analogy], with a concrete test (C2) |
| Theorem 2: translation lengths in ratio φ | ℤ-linear independence of lengths ⇒ minimality (Keane) | [classical] |
| χ-isotypic decomposition | only via the Galois action on the family of d/2 windowed systems (fact 3); even characters only | [analogy] |
| Mass of the genus of (O, xȳ) | ∝ h⁻ ∝ ∏_{χ odd} L(0, χ) | [classical]; the two-disk system sees only one class (§4) |

## 2. Conjectures and questions, each with a test

**C1 (finite-type renormalization ⇔ quadratic K⁺)** [conjecture].
- Claim: GG_n has an exactly self-similar characteristic fractal and an r_c² in K⁺ given by a
  finite-type renormalization if and only if φ(n) = 4, that is n ∈ {5, 8, 10, 12}. These are exactly
  the n for which the paper has closed forms. They are also exactly the "quadratic" rotation numbers
  of Kouptsov–Lowenstein–Vivaldi.
- Proposed mechanism: on invariant segments (as in Theorem 2) the critical dynamics induces interval
  exchanges with lengths in K⁺. Over a quadratic field, Rauzy–Veech induction is eventually periodic
  (Boshernitzan–Carroll, from memory, to be checked). The Perron eigenvalue of the period matrix is
  then a unit of K⁺, and that unit is the fractal's scale factor.
- Tests:
  1. For n = 5, 8, 12, extract the induced interval exchange on the Theorem-2-type segment and run
     Rauzy induction exactly in K⁺. Check that it is periodic and that its eigenvalue equals the scale
     unit.
  2. For n = 7, 9, run the same with exact arithmetic in the cubic field and check whether the
     induction is periodic.
- Prediction: r_c(n)² ∈ K⁺ for these n, with the unit of the periodic induction appearing as a
  factor, as it does for n = 8 and 12 (§3.1).

**C2 (the n = 7 break is an arithmetic event)** [conjecture].
- For n = 7, K⁺ = ℚ(cos 2π/7) has unit rank 2. A self-similarity under one unit ε contracts the
  physical coordinate and expands the two internal coordinates at different rates |σ₂ε| ≠ |σ₃ε|. The
  natural candidate is the Pisot unit λ = 1 + 2cos(2π/7) ≈ 2.247, with conjugates of absolute value
  about 0.555 and 0.802.
- So apparent self-similarity can persist for many generations until the slower internal coordinate
  becomes decisive.
- Test:
  1. Measure the zoom ratio between successive repeats in the n = 7 fractal, and the zoom at which the
     pattern breaks.
  2. Ask whether both are products of powers of units of ℚ(cos 2π/7). Note ln(5·10⁵)/ln λ ≈ 16.2;
     that is numerology until the repeat ratio itself is measured.
  3. The orbit scan of §3.2 shows the two internal coordinates growing at clearly different rates,
     about 1.64 and 1.97 per step (preliminary). That is consistent with C2, but too short to identify
     the units.

**C3 (internal-space dimension and complex dimensions)** [conjecture].
- Write N(δ) = |orbit of 0| at r² = r_c² − δ, and R(δ) for its maximal internal modulus.
- Measured for n = 5, 8, 12 (preliminary):
  - R ~ δ⁻¹ (R·δ stays bounded and oscillates).
  - N ~ δ^{−D} with D = log m / log ε, where ε is the scale unit and m the orbit multiplier per
    generation: m ≈ 13, 5.4, 9.0 and D ≈ 1.78, 1.91, 1.67.
- Conjectures:
  1. m is the Perron eigenvalue of an integer substitution matrix, so an algebraic integer, and
     possibly exactly 9 for n = 12.
  2. The Mellin transform ∫ N(δ) δ^{s−1} dδ, or equivalently the "orbit height zeta"
     Z_O(s) = Σ_{w∈O(0)} |σ(w)|^{−s} at r = r_c, has poles on the line Re s = D spaced by
     2πi / log ε. Here log ε is a multiple of the regulator of K⁺.
- Z_O is a *thinned* partial Hecke–Epstein zeta function of the ideal 𝔞 (the full lattice-in-window
  sum has abscissa 2). Its periodic pole lattice has the form of the zeta function of a curve over
  F_q, with q replaced by the fundamental unit. That last part is [analogy] only.
- Test: push the scans to more generations with an exact compiled orbit engine and fit log-periodic
  oscillations of N·δ^D.

**C4 (r_c² is a relative norm; where its primes can sit)** [conjecture].
- If r_c = |p + 1| with p ∈ K (true for n = 5, 8, 12), then r_c² ∈ N_{K/K⁺}(K^×). So every prime of
  K⁺ that is inert in K/K⁺ divides r_c² to an even power.
- Observed (§3.1):
  - n = 8: the factor 5 is inert in K⁺ = ℚ(√2) but splits in K/K⁺.
  - n = 12: 37 splits completely in ℚ(ζ₁₂).
  - n = 5, 10: the norm 11 ≡ 1 (mod 5), so 11 splits completely.
- Question: is the prime part of r_c² always made of primes ≡ 1 (mod n), or split in K/K⁺ (as here),
  together with the ramified prime?
- Test: any new closed form, for example from C1's Rauzy induction for n = 7 or 9.
- This is the only place where an inert/split dichotomy is forced in the two-disk world.

**C5 (2-power tower)** [conjecture].
- r_c(2^k)² ∈ ℚ(ζ_{2^k})⁺, if Conjecture R of [`analytic-continuation.md`](analytic-continuation.md)
  holds.
- If the fractal scales ε_k of GG_{2^k} are cyclotomic units, are they norm-compatible
  (N(ε_{k+1}) = ε_k)? That is what would make an Iwasawa-theoretic object out of the family.
- A cheap first check fails for the naive guess ε_k = tan(π/2^k): the relative norm of tan(π/16) to
  ℚ(√2) is −1, not √2 − 1.
- Test: measure the GG_16 scale factor (scan as in §3.2 with n = 16 near r_c = 1.148470) and test it
  against the cyclotomic units of ℚ(ζ₁₆)⁺.
- The expected answer is negative: the behaviour of r_c along the tower is archimedean (§3.3).

**C6 (two-piece fractals vs class number)** [conjecture, expected to fail].
- If the n = 23 two-piece phenomenon were caused by h(ℚ(ζ₂₃)) = 3, two-piece fractals would appear
  exactly for n with h > 1. In range, those are 23, 29, 31, 34, 37, 38, 39, 41, 43, 46, 47, 49, …;
  class number 1 holds for n ≤ 22 and for 24–28, 30, 32, 33, 35, 36, 40, 42, 44, 45, 48, 50, 54, 60,
  66, 70, 84, 90.
- The likely explanation is instead a ℤ/2 symmetry breaking: the reflection z ↦ −z̄ normalizes GG_n
  and swaps two orbit closures for odd n.
- Test: image the critical fractals for n = 21, 25, 29, 31, 39 and check for the two-piece property.

## 3. Computations

### 3.1 Closed forms

| n | r_c² | conjugate | trace | norm | factors in O_{K⁺} |
|---|---|---|---|---|---|
| 5 | 3 + φ = 4.618034 | 2.381966 | 7 | 11 | a prime of norm 11 (11 ≡ 1 mod 5) |
| 10 | 4 − φ = 2.381966 | 4.618034 | 7 | 11 | **the Galois conjugate of r_c(5)²** |
| 8 | 10 − 5√2 = 2.928932 | 17.071068 | 20 | 50 | the inert prime 5, the ramified prime √2 and the **scale unit tan(π/8)**; also r_c(8)² = 5·\|1 − ζ₈\|² |
| 12 | 40 − 22√3 = 1.894882 | 78.105118 | 80 | 148 = 4·37 | the ramified prime above 2, a split prime above 37 (7 − 2√3) and the **scale unit tan(π/12) = \|1 − ζ₁₂\|²** |

- [computed] All four values agree with the paper's table to 1e-6. For n = 10 the closed form gives
  r_c = 1.543362 against the table's 1.543357, a 5e-6 gap that the paper also shows.
- [computed, preliminary] For n = 5, 8, 10, elements w ∈ ℤ[ζ] with |w|² = r_c² exist with
  coefficients in [−3, 3]. For n = 12 none exist in that box; the 37-part is presumably larger.

### 3.2 Orbit of 0 approaching r_c

[computed, preliminary] Orbits computed by breadth-first search on integer vectors in ℤ[ζ_n], with the
disk test done in floating point in the identity embedding. Representative rows (δ = r_c² − r²):

| n | δ | orbit size | max internal modulus |
|---|---|---|---|
| 5 | 7.36e-2 | 9 477 | 143.1 |
| 5 | 1.52e-2 | 112 539 | 612.1 |
| 5 | 4.10e-3 | 1 469 085 | 2 592.9 |
| 8 | 6.13e-2 | 16 297 | 114.6 |
| 8 | 2.15e-2 | 87 247 | 277.6 |
| 8 | 9.77e-3 | 468 095 | 674.6 |
| 12 | 1.67e-2 | 23 813 | 192.3 |
| 12 | 3.47e-3 | 216 043 | 722.3 |
| 12 | 9.34e-4 | 1 945 733 | 2 700.3 |

- Internal growth per generation:
  - n = 5: 4.234, 4.278, 4.236, against φ³ = 4.236.
  - n = 8: 2.423, 2.430, against 1 + √2 = 2.414.
  - n = 12: 3.757, 3.739, against 2 + √3 = 3.732.
- δ shrinks by the same factor per generation: about 4.2, 2.5 and 3.71 respectively.
- Orbit-size multiplier per generation: about 12–13 (n = 5), 5.35–5.46 (n = 8), 9.01–9.09 (n = 12).
- So, numerically: **criticality is internal-space escape, renormalized by the Galois conjugate of the
  scale unit.** This is the cut-and-project duality between a contraction ε and an expansion σ(ε).
- n = 7 (two internal coordinates): the maxima grow by about 1.57–1.76 and 1.6–2.3 per step, averaging
  about 1.64 and 1.97 over four steps, with δ shrinking about 3.05 per step. There is no single clean
  ratio in this range. The product 1.64 × 1.97 ≈ 3.2 roughly matches the δ factor, which fits a
  norm-one unit.

### 3.3 Does r_c(n) → 1 carry arithmetic?

[computed] These fits use the paper's table values only, not orbit computations.
- f(n) = n²(r_c − 1) runs from 38.96 at n = 40 to 39.39 at n = 100. A smooth fit A + B/n + C/n² on
  n ≥ 40 gives A = 39.52, against 4π² = 39.478.
- **[conjecture] r_c(n) = 1 + (2π/n)² + o(n⁻²).** The rotation angle squared sets the width of the
  overlap lens. This is purely archimedean.
- The residuals (rms 0.012 against a table noise of about 0.002) are larger than noise for n ≲ 60.
  But φ(n)/n, parity and 3 | n or 4 | n together explain only about 10% of them.
- Qualitatively, primes are local minima of f (n = 37, 41, 43, 53, 59, 61, 67), and n with small
  φ(n)/n are local maxima (36, 42, 60). That is a mild dependence on the *dimension* of the internal
  space, not on class number, regulator or discriminant.
- n = 23 is not anomalous in f: its second difference (+2.77) is in line with the other primes
  (19: +4.33, 29: +1.45).
- 2-power n (8, 16, 32, 64) just follow the smooth curve.

### 3.4 Galois partners

- [computed] r_c(10)² = σ(r_c(5)²) exactly.
- [computed, preliminary] The analogous search for (7, 14) and (9, 18) looked for α ∈ ℤ[2cos(2π/m)]
  with coefficients up to 100, α ≈ r_c(m)², and some conjugate σ_k α ≈ r_c(2m)², at tolerance 1e-5
  relative. It finds no hits.
- On its own, r_c(7)² or r_c(9)² ∈ O⁺ with coefficients up to 100 gives only 2–3 candidates, the same
  count as random control targets. So in this range neither value is a "small" element of O⁺. That
  fits C1: no finite-type closed form for cubic K⁺.

## 4. What probably does not enter the dynamics, and why

1. **Class numbers and irregular primes (n = 23, 37).** The dynamics is attached to the pair
   (O, {±1}) and is invariant under scaling. Ideal classes would only enter through Hermitian lattices
   not isometric to (O, xȳ), and the two-disk system never sees them: a system with centres in another
   ideal is a scaled and rotated copy of GG_n. Also, h(23) = 3, which does not match "two pieces". The
   37 in N(r_c(12)²) = 4·37 is a split-prime factor, unrelated to 37 being irregular.
2. **Discriminant or regulator growth behind r_c → 1.** Those grow like n^{φ(n)}. r_c − 1 ≈ 4π²/n² is
   smooth and archimedean (§3.3).
3. **ℓ-adic objects.** Two-disk dynamics is entirely archimedean: one real place gives the window, the
   others give internal space. No ℓ-adic object appears. Any link to Iwasawa theory would need a
   norm-compatible system of dynamical units (C5), which is expected to fail.
4. **Dirichlet L-functions as "zeta functions of GG_n".** Characters enter only by diagonalizing the
   Galois permutation of d/2 windowed systems (fact 3), and only even characters. A generating
   function of orbit sizes has log-periodic poles governed by a unit (C3), not an Euler product.
   Nothing resembles L(s, χ) beyond the Hecke–Epstein background sum of the unwindowed lattice.
5. **Transcendental periods.** Two-disk geometry uses only cyclotomic lengths (sines and cosines),
   which are algebraic. No transcendental period appears.
6. **Definite Hermitian lattices.** A two-disk system is the rank-1, one-place-windowed shadow of an
   arithmetic affine unitary group μ_n ⋉ 𝔞 over a CM field. U(1) over K⁺ is definite at every infinite
   place, so U(1)(O) = μ_n is finite. What the two-disk system adds is a window at one place and
   translations, which turn a finite group into a possibly infinite pseudogroup.

## Literature pointers (from a brief search; to be checked)

- K. L. Kouptsov, J. H. Lowenstein, F. Vivaldi, "Quadratic rational rotations of the torus and dual
  lattice maps" (the quadratic cases q = 5, 8, 10, 12).
- J. H. Lowenstein, K. L. Kouptsov, F. Vivaldi, "Recursive tiling and geometry of piecewise rotations
  by π/7", Nonlinearity 17 (2004) 371–395 (the cubic case, directly relevant to C2).
- J. H. Lowenstein, F. Vivaldi, "Renormalization of a one-parameter family of piecewise isometries",
  arXiv:1406.6910. It reports more intricate renormalization in a handful of cubic cases.
- M. Boshernitzan, C. Carroll, on interval exchanges over quadratic fields (from memory, to be
  checked).
- J. Wu, TU Delft bachelor thesis (2025), extends the two-disk setup to three-disk and k-disk systems.
