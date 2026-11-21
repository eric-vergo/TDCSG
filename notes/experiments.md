# Two-disk compound symmetry groups: experiments

Authors: Eric Vergo and Claude (Anthropic).

Exploratory, data-driven work on GG_n(r). The aim is to find directions, not to prove anything.
Labels, notation and the closed forms of r_c² follow [`overview.md`](overview.md).

**Every number in this note that comes from an orbit computation is preliminary.** The exploratory
Python scripts behind them (not part of this repository) store points exactly, as integer vectors in
the power basis of ℤ[ζ_n] modulo Φ_n, but decide disk membership in double precision with a 1e-12
tolerance for boundary ties. Results at exact thresholds (r = g(n), r₁, the n ≡ 4 mod 8 count
n² − 3n + 1) depend on that test. They stand until an exact orbit engine reproduces them. Statements
derived only from the paper's Appendix A table, or from exact algebra, are marked as such.

Further notation: θ = 2π/n and s = sin(π/n). r_c(n) is the paper's Appendix A value (six decimals; the
paper says it is good to about five). The paper's n = 10 entry is 5e-6 below the exact √(4 − φ), so
the table error is taken as about ±5e-6.

---

## Summary

| Label | Result |
|---|---|
| [computed] (table only) | F1. r_c(n) ≥ g(n) = \|2 − ζ_n\| = √(5 − 4cos θ) = √(1 + 8 sin²(π/n)) for all 95 tabulated n. For n ≥ 79 the two agree within table rounding. |
| [computed, preliminary] | F2. For n ≡ 4 (mod 8), a second threshold r₁(n)² = 1 + 8s² + 512 s⁶(1 − s²) explains the excess r_c − g ≍ n⁻⁶. In this class the origin's orbit at r = g has n² − 3n + 1 points. |
| [computed, preliminary] | F3. For n with φ(n) = 4 (n = 5, 8, 10, 12, exactly the four closed-form cases), orbit growth as r ↑ r_c is a power law with log-periodic modulation. Its period is the logarithm of a unit of ℚ(ζ_n)⁺: φ³, φ³, 1 + √2, 2 + √3. |
| [proved] (elementary), confirmed by computation | F4. The orbit of 0 spans the ideal (1 − ζ_n) of ℤ[ζ_n]: index p for prime powers p^k, all of ℤ[ζ_n] otherwise. |
| [computed, preliminary] | F5. The size N0(n) of the origin's orbit at r = g satisfies N0(n) = 1 + 2(n − 1)·(odd) for 49 of the 55 computed n ≢ 4 (mod 8). Its values form plateaus across consecutive n. |
| [analogy] (suggestive) | n = 20 has the same scale φ³ as n = 5 and 10. n = 7 (unit rank 2) shows several unequal scale ratios, which fits the paper's report of broken self-similarity. The Galois-conjugate "window" of the orbit grows like N^0.55–0.6. |
| Nothing found | Integer-relation search for r_c² beyond the four known cases. Correlations with h⁻, the Euler–Kronecker constant, L'/L(1, χ), φ(n)/n, ω(n) and primality. Random-matrix statistics of the orbit Markov operator (it is Poisson). An odd-n mod-4 effect. Anything special at n = 7 or 23 in the residuals. |

The arithmetic of ℚ(ζ_n) that clearly shows up is **units and the regulator** (F3) and the ideal
(1 − ζ) (F4). These enter through the self-similar renormalization, not through L-values. No
experiment found L(1, χ), L'/L(1, χ) or class-number information in the dynamics.

---

## E1. Asymptotics and closed forms of r_c(n)

### E1a. Leading asymptotics (table only)

The natural variable is r²: n²(r_c² − 1)/(4π²) → 2. A weighted fit over odd n ≥ 30 gives
c₀ = 1.9997 (with c₀ + c₁/n + c₂/n², χ²/dof ≈ 4 at σ_r = 2e-6). The even classes scatter much more
because of the anomalies below. Equivalently, r_c² ≈ 1 + 8π²/n² and r_c ≈ 1 + 4π²/n².

### E1b. The baseline g(n) = |2 − ζ_n| (F1)

The fitted leading terms match 1 + 8 sin²(π/n) = |2 − ζ_n|². Comparing the table directly:

| n range | count | r_c − g > 5e-6 | \|r_c − g\| ≤ 1e-6 | max \|r_c − g\| (n ≢ 4 mod 8) |
|---|---|---|---|---|
| 5–32 | 27 | 27 | 0 | 0.24 |
| 33–52 | 20 | 11 | 3 | 4.8e-5 |
| 53–78 | 26 | 1 (n = 60) | 17 | 3.9e-6 |
| 79–100 | 22 | 0 | 21 | 5e-7 |

- **No n has r_c < g** beyond rounding. The most negative residual is −0.5e-6.
- For n ≥ 79 every residual is within ±0.5e-6, i.e. pure rounding. The one exception is n = 84
  (1.1e-6), which is ≡ 4 mod 8 and matches the predicted excess (F2).
- Meaning: g is the distance from the left centre to b(0) = 1 − ζ⁻¹. It is the radius at which the
  two n-gon orbits of the origin first touch. Below g the origin's orbit has exactly 2n − 1 points
  (preliminary; checked for every n ≤ 72).
- Expansion: g = 1 + θ² − 7θ⁴/12 + O(θ⁶).

**Confidence.** The statement "r_c(n) − g(n) = O(n⁻⁶) with a small constant, and r_c ≥ g" is strongly
supported by the table: 22 consecutive n agree to rounding while r_c − 1 changes by a factor of 1.6.
The data cannot separate exact equality from an excess below about 1e-6 at n ≈ 80, i.e. anything below
about 2·10⁵·n⁻⁶.

**Important caveat** (preliminary). An infinite orbit at r ≈ g could not be reproduced for large n:

- For n = 33 the origin's orbit is 65 points just below g and 65 089 at g. It then stays the same up
  to g + 5e-5.
- The lens tips have small orbits (769 points).
- 40 random lens points, and 8 generic points within 1e-5 of 0, all have orbits ≤ 5·10⁴ at g ± 1e-7.

So either the infinite orbits at r ≈ g live on a thin set that was not sampled, or the paper's
criterion (at least 10¹⁰ images) fires at the onset of very large finite orbits. Which one is open.
These runs sit at an exact threshold, where the floating-point membership test matters most.

### E1c. The n ≡ 4 (mod 8) family (F2)

[computed, preliminary]
- For every n ≡ 4 mod 8 with 12 ≤ n ≤ 100 (12 values), the origin's orbit at r = g has exactly
  **n² − 3n + 1** points.
- It stays that size until a second threshold r₁(n). For n ≥ 44 it then jumps straight past 6·10⁴.
  **Contradicted by the exact engine:** at r = r₁ the orbit is finite for every n ≡ 4 (mod 8) up to
  100 except n = 84 (cap 2·10⁶ reached), and for n = 60 it has only 38 821 points. The count
  n² − 3n + 1 and the threshold r₁ are confirmed exactly; see [`engine.md`](engine.md) (ii).
- The point that triggers r₁ has a periodic coefficient pattern (1, −2, 2, 0, −2, 0, 2, …, 2, −1).
- PSLQ on the 30-digit value of r₁² for n = 44 gives a relation that holds for **all** n = 20, …, 100
  in this class to 1e-30:

  r₁² = 25 − 20cos θ − 16cos 2θ + 16cos 3θ − 4cos 4θ
      = g² + 32(1 − cos θ)³(1 + cos θ)
      = 1 + 8s² + 512 s⁶(1 − s²),

  so r₁² − g² = 8θ⁶ − 4θ⁸ + …, and η(n) := r₁ − g ≈ 4θ⁶. (The three expressions are equal as
  trigonometric identities; that the trigger threshold is r₁ is the preliminary part.)

| n | table r_c − g (1e-6) | η = r₁ − g (1e-6) | ratio |
|---|---|---|---|
| 12 | 137233 | 56638 | 2.42 |
| 20 | 7066 | 3342 | 2.11 |
| 28 | 785 | 475 | 1.65 |
| 36 | 191 | 108 | 1.76 |
| 44 | 43.0 | 32.9 | 1.31 |
| 52 | 14.5 | 12.2 | 1.19 |
| 60 | 11.2 | 5.19 | 2.15 |
| 68 | 3.4 | 2.46 | 1.40 |
| 76 | 1.2 | 1.26 | 0.92 |
| 84 | 1.1 | 0.69 | 1.65 |
| 92 | 0.4 | 0.40 | 0.89 |
| 100 | 0.2 | 0.24 | 0.87 |

**Confidence.** The table's excess r_c − g over this class spans six orders of magnitude, and it
tracks η ≈ 4θ⁶ within a factor of 0.9–2.4. So r_c − g ≍ n⁻⁶ is well supported. The exact r_c for this
class is not r₁ itself: it is about 1.2–2.4 × η for n ≤ 68, while for n ≥ 76 the difference is inside
table error.

### E1d. Integer-relation search for r_c² (table only)

Method: PSLQ on [r_c², 1, 2cos(2πk/m)], k < φ(m)/2, for m = n and m = 2n, with tolerance 4e-6 and
height ≤ 200. Chance control: rerun on 40 targets shifted at random by up to ±0.05 and record how often
a relation of equal or lower height appears.

| n | result |
|---|---|
| 5 | Recovered 3 + φ (chance 0.00) |
| 8 | Recovered 10 − 5√2 (chance 0.00) |
| 12 | Recovered 40 − 22√3, but chance 0.03: height 40 is close to what six digits can certify in degree 2 |
| 10 | Failed in ℚ(ζ₁₀)⁺, because the table entry is off by 5e-6 |

All other n gave relations whose chance rate was mostly 0.3–1.0. A few had low chance rates: n = 15
(0.03), 18 (0.00, denominator 3), 21 (0.00, height 2 but 2.7e-6 off), 30 (0.03), 42 (0.05). That is what
about 50 trials would produce by luck.

**Nothing found.** Six digits are too few for degree ≥ 3, since one needs about (d + 1)·log₁₀ H digits.

---

## E2. Arithmetic correlations

**Invariants computed** for n ≤ 100:
- h⁻ from the analytic class number formula. It reproduces the known values (h⁻(23) = 3, 29: 8,
  31: 9, 37: 37, 41: 121, 43: 211, 47: 695, 53: 4889, 59: 41241, 97: 411322824001).
- The Euler–Kronecker constant γ_K = γ + Σ_{χ≠1} L'/L(1, χ_prim).
- The mean of |L'/L(1, χ)| and the sum over odd characters. L and L' at 1 come from the digamma
  function and the Stieltjes constant γ₁.

**Targets** (after removing trends in log n and the n mod 8 class):
- log(r_c − g) for n = 13–60 (not 4 mod 8, N = 42; table only);
- log N0 for n = 13–72 (N = 49; preliminary).

**Result:** all 14 Spearman correlations have |ρ| ≤ 0.24 and permutation p ≥ 0.12. The Bonferroni
threshold is p < 0.0036. **Nothing found.**

**Odd n, n ≡ 3 vs 1 mod 4.** In 33–55, n ≡ 3 mod 4 has the larger excess in 5/5 neighbour comparisons
(p = 0.03). But it is 1/4 in 13–31 and 7/9 over 33–71. Noise.

**n = 7, 23:** the residuals show nothing special. The 7 → 9 → 11 decay is smooth. The paper's n = 23
two-piece fractal and the n = 7 scale break are not visible in r_c.

**N0(n) structure (F5)** [computed, preliminary]. N0(n) is the origin's orbit size at r = g, computed
for 5 ≤ n ≤ 72:
- N0 = 1 + 2(n − 1)·M with M odd, for n = 9, 11, 13–17, 19, 21–27, 29–35, 37–43, 45–47, 50, 51, 53–59,
  61, 62, 65, 66, 69–72.
- Exceptions: 5, 7, 8, 10, 18, 48.
- M forms plateaus: 17 for n = 13–16, 49 for 23–29 (except 28), 85 for 41–43, 129 for 39, 40, 46; and
  577 for both 32 and 66.
- For n = 49, 63, 64 and 67, N0 exceeds 4·10⁵.

This looks like combinatorial stability across n, not arithmetic. It did not correlate with any
invariant.

---

## E3. Direct simulation

### E3(i), (ii). Orbit growth and log-periodicity

**Algorithm.** An event-driven sweep in r. Keep the orbit O(r) and a heap of the distances |p ± 1| of
orbit points lying outside a disk. Pop the next threshold r_k, apply the rotation, and continue the
breadth-first search. This gives the step function N(r) and the threshold radii (r_k² lies in
ℤ[ζ_n]⁺; for n = 5 they are all A + Bφ). Thresholds are exact algebraic numbers, but ordering and
membership were decided in floating point, so the results below are preliminary.

The orbit grows in big multiplicative jumps that recur with a fixed pattern. Same-type jumps occur at
ε_k = r_c − r_k with ratio converging to a unit λ:

| n | φ(n)/2 | jump ratios of ε (same type) | λ | N growth per period | α (N ~ ε^−α) | profile corr. between periods |
|---|---|---|---|---|---|---|
| 5 | 2 | 4.167, 4.220, 4.233 | φ³ = 4.236 | 11.6, 13.3, 13.5 | 1.81 | 0.81 |
| 10 | 2 | 4.217 | φ³ | 15.2 | 1.93 | 0.87 |
| 8 | 2 | 2.410, 2.412 | 1 + √2 = 2.414 | 5.39, 5.35 | 1.92 | 0.95, 0.99 |
| 12 | 2 | 3.690, 3.721 | 2 + √3 = 3.732 | 8.98, 9.09 | 1.70 | 0.87, 0.96 |
| 20 | 4 | 4.10, 4.15 | φ³? (suggestive) | about 3.2 per jump | – | – |
| 7 | 3 | 9.33, 8.02, 10.4 (different jump types) | no single ratio | – | – | – |

- **Log-periodicity.** log N(ε) = −α log ε + P(log ε / log λ), with P periodic. Its amplitude is about
  1.4–1.9 in log N, i.e. N oscillates by a factor of about 4–6 around the power law. The profile
  correlation between successive periods rises with depth (0.95 → 0.99 for n = 8).
- **Complex dimensions** [conjecture]. In the language of Lapidus–van Frankenhuijsen (from memory, to
  be checked), a Dirichlet series Σ ΔN_k ε_k^s has poles on the line Re s = α, spaced by 2π/log λ:
  4.35 (n = 5, 10), 7.13 (n = 8), 4.77 (n = 12). Within one period there are 2–3 jump types (n = 5:
  ×3.5, ×1.7, ×2.0), so φ³ rather than φ is the minimal period.
- **Arithmetic reading.** The period is a multiple of the regulator of ℚ(ζ_n)⁺. For n = 8 and 12 it is
  exactly the fundamental unit; for n = 5 and 10 it is the cube of the fundamental unit φ.
- **Rank 1 matches closed forms.** The four n with closed forms are exactly those with φ(n) = 4, i.e.
  unit rank 1: a single scaling gives a geometric series and hence a closed form. For n = 7 (rank 2)
  the same-type ratios do not agree. This fits two incommensurate scalings and the paper's scale break
  at about 5·10⁵ zoom. It is inconclusive, because r_c(7) is only known to 1e-6.
- **Aitken extrapolation** of same-type thresholds recovers the known r_c to about 1e-6 from runs of
  4–20 million points: n = 5 gives 2.1489621 against 2.1489611; n = 8 gives 1.7114167 against
  1.7114123. It also gives r_c(20) ≈ 1.100581–1.100583.
- **Thresholds for n = 5**: r_k² = A + Bφ, with |A|, |B| up to about 4·10⁶. The gap r_c² − r_k² is
  small, but its Galois conjugate is large (about −10⁶). The thresholds are not governed by a bounded
  window.
- For n = 9, 16, 17, 28 the origin's orbit stays finite up to r_c (241, 6259, 2081, 2213 points). The
  critical point is elsewhere, so the scan needs a different seed point there.

### E3(iii). Spectrum of H = P_a + P_aᵀ + P_b + P_bᵀ on finite orbits

Orbits of 1433–3109 points for n = 5, 7, 8, 12 just below r_c. The operator was decomposed by the
Klein four-group generated by z ↦ −z (which swaps a and b) and z ↦ z̄ (which sends a to a⁻¹); H
commutes with both, as checked.

- **Level statistics:** the mean spacing ratio ⟨r⟩ is 0.37–0.42 in every sector. Poisson is 0.386,
  GOE 0.536, GUE 0.603.
- **Degeneracies:** large, at values 2 + 2cos(2πk/m) such as 2, φ², φ⁻², 2 + √3, 2 + 2cos(2π/7). These
  come from short cycles of the generators; about 35–45% of points are fixed by each generator.
- **Density of states:** spiky and supported in about (−3, 4], with heavy weight near 4. There are no
  clean Cantor-type gaps at these sizes.

The spectrum looks integrable or localized, not random-matrix-like. (A test with a Peierls phase was
run, but it mixes symmetry sectors, so its ⟨r⟩ is not meaningful and it is discarded.)

---

## E4. Lattice and cut-and-project structure

**ℤ-span of the origin's orbit** (Hermite normal form on 3000 points). The index in ℤ[ζ_n] is 5 for
n = 5, 2 for n = 8 and 1 for n = 12. So the span is exactly the ideal (1 − ζ_n), as predicted: every
generator is the identity mod (1 − ζ), and 1 − ζ is a unit unless n is a prime power. This is
elementary, but it is the only place the ramified prime shows up.

**Galois window** (preliminary). The maximum of |σ_k(p)| over the orbit (σ_k : ζ ↦ ζ^k, k ≠ ±1) grows
without bound:

| n | N grows by | max\|σ_k\| grows | max\|σ_k\| ~ N^β |
|---|---|---|---|
| 5 | 801 → 1.1·10⁵ | 34 → 612 | β ≈ 0.58 |
| 8 | – | – | β ≈ 0.55 |
| 12 | – | – | β ≈ 0.59 |

The filling fraction N / (physical area × internal ball volume / covolume) falls slowly: 0.029 → 0.012
for n = 5, 0.15 → 0.08 for n = 8, 0.18 → 0.06 for n = 12. So the orbit is not a model set with a fixed
window. It is a sparse, fractal-like subset of the Minkowski lattice, with internal dimension about
1.7–1.8 (1/β).

---

## What this means

1. **Real arithmetic content.** These are units, the regulator and the ideal (1 − ζ) of ℚ(ζ_n)⁺ and
   ℚ(ζ_n). If there is a route toward L-functions, it is the one these objects already carry:
   - the class number formula h·R ∝ the residue of ζ_K;
   - for n = 5, 8, 12, the quadratic fields ℚ(√5), ℚ(√2), ℚ(√3), whose fundamental units give the
     log-periodic periods.
   No trace of L(1, χ) for odd characters, of h⁻, or of L'/L appeared.
2. **The "complex dimensions".** These form a single arithmetic progression on a vertical line, set
   by one unit. That is the trivial self-similar case (a lattice string, in Lapidus's terms). A richer
   picture could only come from unit rank ≥ 2 (n = 7, 9, 11, 13, …), where two or more incommensurate
   scales could give a quasi-periodic (non-lattice) set of complex dimensions. That is the one
   experiment that could make the picture non-trivial.
3. **Spectra.** The natural orbit operator has Poisson statistics.

## Recommended next experiments

All of these need the exact orbit engine; the first three also need a compiled one.

1. **Unit rank ≥ 2 log-periodicity** (n = 7, 9, 11, 13). Use a compiled frontier search, as the paper
   did, to reach 10⁹–10¹⁰ orbit points. Then:
   - extract the threshold sequence and identify each threshold r_k² exactly in ℤ[ζ_n]⁺;
   - test whether ε_k follows a 2-parameter family u₁^a u₂^b of units (a regulator lattice);
   - compute the resulting complex-dimension set, which is quasi-periodic if the scales are
     incommensurate.

   This is the most promising arithmetic direction.
2. **High-precision r_c by Aitken extrapolation on exact thresholds,** to get 12–20 digits for
   n = 7, 9, 11, 13–19. That makes PSLQ in ℚ(ζ_n)⁺ (degree 3–9) meaningful and answers the paper's
   question of whether r_c is algebraic.
3. **Locate the infinite orbits at r ≈ g for large n** (for example n = 33, 49). Search systematically
   over piece-boundary points (images of disk-boundary arcs) at r = g + 10⁻⁹. Also test whether the
   paper's large-n values are really "onset of very large finite orbits".
4. **Prove r_c ≥ |2 − ζ_n|,** or find a counterexample, and prove the n ≡ 4 mod 8 count n² − 3n + 1
   and the r₁ formula. Look for analogous second-threshold families for the other anomalous classes
   (n = 38, 42, 32, 40; odd 39, 43, 51), using a seed point other than the origin.
5. **Renormalization or transfer operator for n = 5.** Derive the substitution matrix of the three
   jump types. Its Perron eigenvalue should be the N growth per period (about 13.5), so
   α = log λ_N / log φ³. Its Ruelle-type zeta function then gives the complex dimensions exactly.
6. **Spectra with a non-trivial coupling.** Try the Koopman operator on L² of the fractal at r_c,
   using the natural measure from the deepest orbits rather than finite orbits. Also weight the
   generators by characters of the translation module, for example e^{i⟨k, t⟩} for k in the dual of
   the ideal (1 − ζ). That is the only operator construction where Dirichlet characters mod n would
   enter naturally.
