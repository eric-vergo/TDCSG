# The rank conjecture: exact threshold sequences for n = 7, 9, 11, 13

Authors: Eric Vergo and Claude (Anthropic).

**Question** (thread 3 of [`overview.md`](overview.md)). For n = 5, 8, 10, 12 the growth of orbits
as r ↑ r_c is log-periodic with one period, the logarithm of a unit of ℤ[ζ_n]⁺ (unit rank 1;
[`engine.md`](engine.md), results (i)). The conjecture is that in general the self-similarity is
governed by the unit group of ℤ[ζ_n]⁺, of rank φ(n)/2 − 1: rank 2 for n = 7, 9, rank 4 for n = 11,
rank 5 for n = 13. In rank 2, two independent scalings could compete; the paper reports that the
n = 7 fractal changes pattern after a zoom of about 500,000.

All numbers below are **[computed]** with the exact engine (`thresholds`, `orbit` with conjugate
maxima, `group` to find seeds). "Finite" means an exhausted search; "cap" means the cap was reached
and nothing is claimed. The values r_c(n) quoted from the paper's Appendix A are numerical
estimates (six decimals, good to about 5·10⁻⁶ in r).

## Summary

| n | seed | depth reached | what the data show |
|---|---|---|---|
| 7 | origin | 9.44·10⁷ points (finite) at r² = 2.63598220; cap 10⁸ at the next threshold | A repeating pattern of three jump types (×5.3, ×1.8, ×3.2) over 2.7 periods. The period matches **one** Pisot unit u = θ⁻¹(1 + θ)³ (θ = 2cos(2π/7)) in all three embeddings: threshold differences shrink by 9.094 per period (σ₁(u) = 9.0978), and the conjugate spreads of the orbit grow by about 2.62–2.73 and 3.52–3.59 per period (1/\|σ₂(u)\| = 2.6039, 1/\|σ₃(u)\| = 3.4940). No second independent scale is visible at this depth. |
| 9 | generic point (2 − 10ζ)/7 (the origin's orbit is not critical) | 2.78·10⁶ points (finite) at r² = 1.98386769; cap 10⁸ at the next threshold | Only seven large steps before the cap; no period can be measured. |
| 11 | origin (not critical) | 101 points (finite) up to r² = 1.7291689, above the table r_c² | No seed near r_c found; no analysis. |
| 13 | origin | 10 291 points (finite) at r² = 1.4728315, just above the table r_c²; cap 10⁸ at the next threshold | Five thresholds in all; no period can be measured. |

**Depth for n = 7.** The deepest threshold reached lies 1.0·10⁻⁵ below r_c,tab² in r². A point
entering a disk at threshold t lies at distance about (r_c² − t)/(2r_c) from the critical circle, so
the orbit resolves spatial scales down to about 3·10⁻⁶ near the critical point: a zoom of about
3·10⁵ measured from the size of the disks, or about 400 measured from the first period of the
repeating pattern (gap 4.2·10⁻³). How the paper measures its zoom of 5·10⁵ is not stated in the
text used here. On the first reading the data stop just short of it; the next period of the pattern
(a further factor 9.1) would need about 34 times more points, some 2·10⁹, beyond this engine (about
10⁸ points within the memory limit). Either way these data can neither show nor rule out the
paper's pattern change.

## Units of ℚ(ζ₇)⁺

θ = θ₁ = 2cos(2π/7) has minimal polynomial x³ + x² − 2x − 1. The cyclotomic units θ and 1 + θ
generate the unit group modulo ±1 (index 1, class number 1); their logarithmic embeddings
(log\|σ_k\|, k = 1, 2, 3) are

| unit | k = 1 | k = 2 | k = 3 |
|---|---|---|---|
| θ | 0.2207 | −0.8096 | 0.5889 |
| 1 + θ | 0.8096 | −0.5889 | −0.2207 |

so the regulator is 0.5255. A unit that expands the physical plane and contracts both internal
planes (a Pisot unit) is θ^a(1 + θ)^b with the first coordinate positive and the others negative.
The smallest ones, with their physical value σ₁ and the internal expansion factors 1/\|σ₂\|,
1/\|σ₃\|:

| unit | σ₁ | 1/\|σ₂\| | 1/\|σ₃\| |
|---|---|---|---|
| 1 + θ | 2.2470 | 1.8019 | 1.2470 |
| θ⁻¹(1 + θ)² | 4.0489 | 1.4450 | 2.8019 |
| (1 + θ)² | 5.0489 | 3.2470 | 1.5550 |
| θ⁻²(1 + θ)³ | 7.2959 | 1.1588 | 6.2959 |
| **θ⁻¹(1 + θ)³** | **9.0978** | **2.6039** | **3.4940** |
| (1 + θ)³ | 11.3448 | 5.8509 | 1.9390 |

In rank 2 the physical values of units are dense in the positive reals (up to sign), so "a gap ratio
is close to some unit" is no evidence by itself. The test that has content is whether a single unit
matches the physical ratio **and** both internal growth rates.

## n = 7: the origin's orbit

The sweep from r = 0 with a cap of 10⁸ found 161 exact thresholds (194 s, single thread). The large
jumps (orbit growing by at least 1.5 times at one threshold) are:

| k | t_k = r_k² | orbit size for t_k ≤ r² < t_{k+1} | growth | r_c,tab² − t_k |
|---|---|---|---|---|
| 6 | 2.6318044646720 | 46 763 | ×5.29 | 4.188·10⁻³ |
| 9 | 2.6338721332211 | 86 163 | ×1.82 | 2.120·10⁻³ |
| 10 | 2.6340677992529 | 280 249 | ×3.25 | 1.925·10⁻³ |
| 24 | 2.6355436839756 | 1 537 885 | ×5.34 | 4.489·10⁻⁴ |
| 35 | 2.6357282325440 | 2 800 107 | ×1.81 | 2.643·10⁻⁴ |
| 46 | 2.6358075785848 | 9 508 813 | ×3.15 | 1.850·10⁻⁴ |
| 102 | 2.6359548469982 | 52 264 937 | ×5.33 | 3.769·10⁻⁵ |
| 153 | 2.6359797654946 | 94 359 561 | ×1.80 | 1.277·10⁻⁵ |
| 160 | 2.6359821980229 | ≥ 10⁸ (cap) | | 1.034·10⁻⁵ |

(r_c,tab = 1.623574 is the paper's value; the exact thresholds are listed by the command in
[`engine.md`](engine.md) as elements re:b₀,b₁,b₂ of ℤ[ζ₇]⁺, for example t₂₄ = 4389 − 2514θ₁ + 2812θ₂.)

**One repeating pattern.** The three jump types recur in the same order with nearly the same
growth factors (×5.29, 5.34, 5.33; ×1.82, 1.81, 1.80; ×3.25, 3.15). Between equivalent points of
consecutive periods the orbit grows by 32.9 and 34.0 times.

**The physical ratio.** Differences of thresholds of the same type do not depend on r_c:

| type | differences | ratio |
|---|---|---|
| ×5.3 (k = 6, 24, 102) | 3.7392·10⁻³, 4.1116·10⁻⁴ | 9.094 |
| ×1.8 (k = 9, 35, 153) | 1.8561·10⁻³, 2.5153·10⁻⁴ | 7.379 |
| ×3.2 (k = 4, 10, 46) | 1.4361·10⁻², 1.7398·10⁻³ | 8.254 |

The ×5.3 ratio equals σ₁(u) = 9.0978 to 0.04%. The other two are further off; for n = 5 the first
ratios also start low (4.167, 4.220, 4.233 → φ³ = 4.236), so slow convergence is possible, but with
two terms per type this is not decided.

**The internal planes.** The maximal moduli of the conjugates σ₂ (ζ ↦ ζ²) and σ₃ (ζ ↦ ζ³) over the
orbit, at the start of each plateau:

| orbit size | max\|σ₂\| | max\|σ₃\| |
|---|---|---|
| 1 419 | 13.44 | 27.57 |
| 3 109 | 13.44 | 40.37 |
| 8 531 | 23.67 | 50.24 |
| 46 763 | 37.28 | 116.74 |
| 86 163 | 37.28 | 152.15 |
| 280 249 | 62.36 | 187.53 |
| 1 537 885 | 97.74 | 418.85 |
| 2 800 107 | 97.74 | 543.36 |
| 9 508 813 | 162.99 | 667.72 |
| 52 264 937 | 267.20 | 1 474.69 |
| 94 359 561 | 267.20 | 1 910.42 |

Per period (same jump type to same jump type) max\|σ₂\| grows by 2.62, 2.73 (×5.3 type) and 2.61
(×3.2 type), and max\|σ₃\| by 3.59, 3.52 (×5.3), 3.57, 3.52 (×1.8) and 3.56 (×3.2). The predicted
factors for u are 2.604 and 3.494; the σ₃ factors decrease toward 3.494 from one period to the next.
No other small Pisot unit fits: θ⁻²(1 + θ)³, the unit nearest the ×1.8 ratio 7.38, would expand σ₂
by only 1.16 and σ₃ by 6.30 per period.

The two internal planes do grow at different rates (exponents max\|σ_k\| ~ N^β with β₂ ≈ 0.27,
β₃ ≈ 0.36), but these are the rates that the conjugates of the single unit u dictate. A second
independent unit would show up as a drift of the per-period factors away from (2.604, 3.494); over
two periods the factors scatter by a few per cent and show no systematic drift.

**Exactness.** The relation is asymptotic, not exact: same-type differences are not unit multiples of
each other. Their norms N(·) from ℚ(ζ₇)⁺ to ℚ differ (17 192 against 131 768 for the ×5.3 type,
76 888 against 947 128 for the ×1.8 type), while a unit multiple would have the same norm up to
sign. This matches the rank-1 cases, where no gap is exactly u^e times an earlier gap.

**Growth law.** Over one period N grows by about 33.4 while the gaps shrink by 9.098, so
N ~ (r_c² − r²)^(−α) with α = log 33.4 / log 9.098 ≈ 1.59, modulated log-periodically with period
log u.

**Estimating r_c(7).** The origin's orbit is finite (94 367 065 points) for r² < t₁₆₀ =
2.6359821980, i.e. r < 1.6235708, and reaches the cap of 10⁸ at t₁₆₀. Treating each jump type as a
geometric sequence with ratio u gives r_c² = t_last + (t_last − t_prev)/(u − 1):

| type | estimate of r_c² | r_c |
|---|---|---|
| ×5.3 | 2.6360056 | 1.623578 |
| ×1.8 | 2.6360108 | 1.623580 |
| ×3.2 | 2.6360224 | 1.623583 |

(Aitken extrapolation of the ×5.3 type gives the same 1.623578.) The spread of these estimates,
about 5·10⁻⁶ in r, is a fair measure of their uncertainty. They lie 4–9·10⁻⁶ above the table value
1.623574, at the edge of its stated accuracy. A finite orbit does not bound r_c from below (the group
is infinite as soon as any orbit is), and reaching the cap does not bound it from above; the bracket
"finite up to r = 1.6235708, cap from there" concerns the origin's orbit only.

## n = 9

The origin's orbit is not the critical one: it stays small up to r_c (241 points; see
[`experiments.md`](experiments.md)). To find a seed, the generic points (α + βζ)/7 of the disks were
used (`group --grid 7`). At r² = 1.9836 all 724 of their orbits are finite, the largest with 21 315
points; at r² = 1.9840 six of them reach the cap of 2·10⁶. One of these, (2 − 10ζ)/7, was swept with a
cap of 10⁸ (peak memory 10.3 GB):

| k | t_k | orbit size |
|---|---|---|
| 0 | 1.9815330806 | 7 542 |
| 1 | 1.9818343275 | 11 882 |
| 6 | 1.9831514958 | 14 266 |
| 8 | 1.9838175765 | 67 413 |
| 9 | 1.9838284152 | 661 899 |
| 12 | 1.9838403147 | 1 528 614 |
| 24 | 1.9838589960 | 2 160 678 |
| 28 | 1.9838663314 | 2 777 252 |
| 32 | 1.9838679875 | ≥ 10⁸ (cap) |

The orbit grows through only a handful of large steps and then passes from 2.78·10⁶ points to the cap
in a single threshold, at r = 1.4084985, which is 1.7·10⁻⁵ above the table value 1.408482. Another
generic point, (−12 + ζ)/7, keeps an orbit of about 4 500 points up to r² = 1.99138 (r = 1.41116)
and then reaches the cap of 2·10⁷ in one threshold. There is no repeating sequence of jumps to
measure a period from, so these data say nothing about the rank of the scaling group. Finding the
seed whose orbit grows through many thresholds (as the origin does for n = 7) would need a
systematic search of the kind used for n = 33 in [`large-n-table.md`](large-n-table.md).

## n = 11 and n = 13

The origin's orbit for n = 11 has 21 points at r = 1, 101 points from r = g(11) on, and stays at 101
points up to r² = 1.7291689 (r = 1.31498), above the table value r_c(11)² = 1.6656 (r = 1.290582); at
that threshold it reaches the cap of 10⁸ in a single step. So the origin is not the critical seed for
n = 11 either. The generic-point search used for n = 9 (grid 5, orbits capped at 10⁶) did not
finish within 30 minutes at r² = 1.6659, so no seed for n = 11 was found.

For n = 13 the origin's orbit has five thresholds in all (peak memory 10.9 GB):

| k | t_k | orbit size |
|---|---|---|
| 0 | 1 | 25 |
| 1 | g(13)² = 1.4581759 | 409 |
| 2 | 1.4661426 | 2 999 |
| 3 | 1.4728315 | 10 291 |
| 4 | 1.4730315 | ≥ 10⁸ (cap) |

t₃ lies 2.1·10⁻⁵ above the table value r_c(13)² = 1.4728104, and the orbit is still finite there; it
reaches the cap at r = 1.213685, 9·10⁻⁵ above the table's 1.213594, in a single threshold.

## What is established and what is not

- **Established** (exact computation): the 161 thresholds of the origin's orbit for n = 7 up to
  10⁸ points, their orbit sizes, the conjugate maxima at the plateaus, the norms of their
  differences, and the threshold sequences of the n = 9 seed and of the origin for n = 11, 13.
  A second starting point for n = 7 was not obtained (the seed search did not finish).
- **Supported by the data, not proved**: for n = 7, within 2.7 periods, the self-similarity is
  governed by the single Pisot unit θ⁻¹(1 + θ)³ in all three embeddings; no second independent scale
  appears. This is consistent with the rank conjecture in the weak sense that the scale is a unit of
  ℤ[ζ₇]⁺, but does not show that the full rank-2 group acts.
- **Not reached**: a further period of the n = 7 pattern, where a second scale or the paper's
  pattern change after a zoom of 5·10⁵ could show up, and any analysis of n = 9, 11, 13 beyond
  locating seeds.
