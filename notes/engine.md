# The exact orbit engine

Authors: Eric Vergo and Claude (Anthropic).

`tdcsg-orbit` computes orbits of GG_n(r) with exact arithmetic in ℤ[ζ_n] and certified disk
membership. It is written in Lean 4 (core library only, no Mathlib import) as the library
`TDCSGCompute` and the executable `tdcsg-orbit`. Labels and notation follow
[`overview.md`](overview.md). Every result in the results section below is **[computed]** with
this engine; none of it relies on a floating-point decision.

## Design

| Module | Contents |
|---|---|
| `TDCSGCompute/Ball.lean` | Fixed-point ball arithmetic: π (Machin), cos and sin with rigorous remainder bounds, trigonometric tables at any precision, exact decoding of doubles |
| `TDCSGCompute/Field.lean` | ℤ[ζ_n] for any n ≥ 3: Φ_n, products, multiplication by ζ^{±1}, complex and Galois conjugation, norm-squared, the real-subfield basis, exact signs of real elements |
| `TDCSGCompute/Disk.lean` | Certified membership in the closed disks: floating-point filter with a proven error bound, exact fallback |
| `TDCSGCompute/Store.lean` | Compact point set: fixed-width coefficients in one byte array, open-addressing hash table of 32-bit indices, automatic widening |
| `TDCSGCompute/Orbit.lean` | Breadth-first orbit search (serial, and a Task-parallel variant) |
| `TDCSGCompute/Thresholds.lean` | Exact threshold sweep: the sorted radii at which an orbit grows |
| `TDCSGCompute/Spec.lean` | Parsing of radii, points and real elements |
| `TDCSGCompute/SelfTest.lean`, `Main.lean` | Self-tests and the command line |

**Arithmetic.** An element of ℤ[ζ_n] is its integer coefficient vector in the power basis
1, ζ, …, ζ^{d−1}, d = φ(n), taken modulo the cyclotomic polynomial Φ_n (computed from
X^m − 1 = ∏_{e|m} Φ_e, so every n ≥ 3 works; the tests cover n ≤ 200 for Φ_n and up to 100 for the
arithmetic). Because Φ_n is monic and irreducible this representation is unique, so equality and
zero tests are coefficient comparisons. Coefficients are arbitrary-precision integers during
computation. Real elements of ℚ(ζ_n)⁺ are also shown in the ℤ-basis 1, θ_1, …, θ_{m−1} of
ℤ[ζ_n]⁺, θ_k = ζ^k + ζ^{−k} = 2cos(2πk/n), m = d/2 (written `re:b0,b1,…`); for n = 5, 8, 10, 12 the
output also gives the form A + Bφ, A + B√2, A + Bφ, A + B√3.

**Generators.** a(z) = ζ⁻¹(z + 1) − 1 and a⁻¹(z) = ζ(z + 1) − 1 when |z + 1| ≤ r, b(z) = ζ⁻¹(z − 1) + 1
and b⁻¹(z) = ζ(z − 1) + 1 when |z − 1| ≤ r, the identity otherwise. Each is one pass over the
coefficients (a shift plus a multiple of Φ_n).

**Storage.** Points are stored in insertion order in one byte array, d coefficients of 1, 2, 4 or 8
bytes each in two's complement; the hash table holds 32-bit indices at load factor at most 2/3. The
insertion order is the breadth-first frontier, so there is no separate queue. Every coefficient is
range-checked before it is stored; if one does not fit, the whole array is re-encoded at the next
width. A coefficient beyond 64 bits, or more than 2³² − 2 points, stops the run with an error. There
is no silent wraparound anywhere.

**Search.** Breadth-first search from a starting point under a, a⁻¹, b, b⁻¹, reporting the number of
new points per generation, the maximum of |σ_k(z)| for each embedding σ_k (k coprime to n,
1 ≤ k < n/2; k = 1 is the physical plane), and how each membership decision was made. It stops
when no new point appears (**finite**, exact size) or when the cap is reached (**cap reached**; no
claim about finiteness).

**Thresholds.** Since a point inside a disk at radius r is moved the same way at every larger
radius, the orbit only grows with r. It changes exactly at the values t = |z ± 1|² ∈ ℤ[ζ_n]⁺ at which
a current orbit point enters a disk. The sweep keeps a heap of the points outside each disk keyed by
that value, pops the smallest key together with every key exactly equal to it, and continues the
search at r² = t. Keys are compared with certified float enclosures, and exactly whenever the
enclosures overlap.

## Correctness of disk membership

A squared radius is an exact element r² = N/q, N ∈ ℤ[ζ_n]⁺, q a positive integer. For w = z ± 1,
z lies in the closed disk exactly when Δ = r² − |w|² ≥ 0. The decision is the sign of Δ, made in one
of two certified ways (full argument in the docstrings of `Disk.lean`, `Field.lean`, `Ball.lean`).

1. **Filter.** The doubles t_i, s_i standing for cos(2πi/n), sin(2πi/n) have a certified error δ
   (computed exactly from their bit patterns against a ball enclosure; δ = 2⁻⁵⁴ in practice). For
   coefficients below 2⁵³ the dot products X̂ = fl(Σ c_i t_i ± 1), Ŷ = fl(Σ c_i s_i) have the standard
   error bound γ_{d+1}Σ|c_i||t_i| (Higham, eq. (3.5)) plus δΣ|c_i|. Propagating this through
   Q̂ = fl(X̂² + Ŷ²) gives a bound E_Q on |Q̂ − |w|²|; the double r̂² has a certified error ε_r. The
   filter decides only if |fl(r̂² − Q̂)| > 2(ε_r + E_Q), where all bounds carry a slack factor 2 that
   absorbs the rounding of the bounds themselves. Then the sign of the computed difference is the
   sign of Δ.
2. **Exact path.** Otherwise D = N − q|w|² is computed in ℤ[ζ_n]. D = 0 is decided by the
   coefficients (the point is on the boundary circle, hence in the closed disk). If D ≠ 0, its value
   Σ D_i cos(2πi/n) is enclosed in a ball, doubling the precision until the ball excludes 0. This
   terminates: D is a nonzero algebraic integer of ℚ(ζ_n)⁺, so |N(D)| ≥ 1, while its other m − 1
   conjugates are at most B = Σ|D_i|; hence |D| ≥ B^{−(m−1)}, and a precision of m(log₂B + 3) + 64
   bits always decides. Exceeding that bound would be reported as an error; it has never happened.

The balls rest on π from Machin's formula and on Taylor series of cos and sin for |x| ≤ 4, where
the alternating tail is bounded by the last summed term. Every ball operation is an enclosure.

What has not been done: none of this is proved in Lean. The argument is written out in the
docstrings and exercised by the tests (boundary points recognised exactly, filter decisions agreeing
with exact decisions, signs of (√2 − 1)^k up to k = 80, which need about 100 bits).

## How to run

```sh
lake build tdcsg-orbit          # also built by `lake build`
lake test                       # runs `tdcsg-orbit --selftest`
.lake/build/bin/tdcsg-orbit orbit -n 5 --r2 closed-1/100 --cap 10000000
.lake/build/bin/tdcsg-orbit orbit -n 33 --r2 touch+1/10000 --format lines
.lake/build/bin/tdcsg-orbit thresholds -n 12 --cap 1000000 --upto closed --rc closed --unit fund
.lake/build/bin/tdcsg-orbit info -n 8
```

- `--r2 SPEC` gives r² exactly: `touch` (g(n)² = 5 − 4cos(2π/n)), `closed` (3 + φ, 10 − 5√2, 4 − φ,
  40 − 22√3 for n = 5, 8, 10, 12), `r1` (25 − 20cos θ − 16cos 2θ + 16cos 3θ − 4cos 4θ), `fund` (the
  fundamental unit), each optionally followed by `+q` or `-q`; `re:b0,b1,…`; `pow:c0,c1,…`; or a
  rational (`7`, `-3/4`, `1.0362`, `2.5e-7`). `--r Q` gives a rational radius instead.
- `--start P`: `0`, `a0`, `b0`, `zeta:k`, or `pow:c0,c1,…` (any length; reduced modulo Φ_n).
- `orbit` options: `--cap`, `--threads`, `--no-conj`, `--width` (initial bytes per coefficient),
  `--format text|lines`.
- `thresholds` options: `--cap`, `--upto SPEC` (stop before a threshold ≥ SPEC), `--from SPEC`
  (start from the orbit at that radius), `--rc SPEC` (print gaps r_c² − t_k with 12 digits and
  their successive ratios), `--unit SPEC` (test every gap for being exactly u^e times an earlier
  gap, e = 1, …, 6), `--max-steps`.
- `--format lines` prints tab-separated records: `param`, `gen`, `conj`, `stat`, `threshold`,
  `result`.

## Tests

`lake test` (or `tdcsg-orbit --selftest`) runs about 4,500 checks in a few seconds: ring identities
(commutativity, associativity, distributivity, ζ^n = 1, Σζ^k = 0, conjugation and σ_kσ_l = σ_{kl},
multiplicativity of |·|², real-basis round trips) for 20 values of n up to 100; π, cos 72°, cos 45°
enclosures; the certified table error; exact signs of ±(√2 − 1)^k, k ≤ 80; membership of points
exactly on the boundary at r = g and at g² ± 10⁻³⁰; agreement of filter and exact decisions; finite
orbits for n ∈ {3, 4, 6} at r ∈ {1, 3/2, 2, 5/2, 3, g} from three starting points; growth below
3 + φ and the cap at 3 + φ for n = 5; 2n − 1 points just below g; agreement of the serial and
parallel searches and of the sweep with direct searches; widening and loud overflow of the
storage; and the exact results below (n ≡ 4 mod 8 counts and r₁, n = 33 at g, rows of the
preliminary table).

## Performance

Measured on the development machine (Apple M2 Ultra), single thread:

| Case | Points | Rate | Memory |
|---|---|---|---|
| n = 12, r² = r_c² − 10⁻³, orbit | 1.94·10⁶ (finite) | 1.1·10⁶ points/s | 19 bytes/point (data and table) |
| n = 5, 8, 10, 12 at r² = r_c², orbit | 5·10⁷ (cap) | 0.6·10⁶ points/s | 2.2 GB resident (44 bytes/point with growth peaks) |
| n = 5, 8, 10, 12, threshold sweep | 3·10⁷ (cap) | 0.6·10⁶ points/s | 2.0–2.3 GB resident (about 70 bytes/point) |
| n = 33, lens point, threshold sweep | 8·10⁷ (cap) | 0.43·10⁶ points/s | 8.7 GB resident (110 bytes/point) |
| n = 33, origin at r₁(33)², orbit | 10⁸ (cap) | 0.41·10⁶ points/s | 7.8 GB resident; largest orbit explored |
| n = 7, 9, 11, 13, orbit with conjugates | 3·10⁶ | 0.8, 0.64, 0.46, 0.40 ·10⁶ points/s | 23–35 bytes/point |

- The cost per point grows roughly linearly with d = φ(n). Almost all decisions are made by the
  filter: in the runs above the exact path was needed only for points exactly on a boundary circle
  (between 0 and 11,000 per run) and for a handful of points within 10⁻¹² of one.
- **Threads.** The `--threads T` variant expands each generation in parallel Tasks and inserts the
  results serially. Measured on n = 12 (1.9·10⁶ points) with T = 1, 2, 4, 8, 16 it gives no speed-up
  (1.08 vs 1.04–1.09 ·10⁶ points/s): the run time is dominated by hash-table probes, which are
  memory-latency bound and serial in this design. The serial search is the default.
- **Feasible depth for n = 7, 9, 11, 13** within 32 GB: with 2-byte coefficients an orbit search
  needs about 25–35 bytes per point in steady state and up to about twice that during table growth,
  so about 5·10⁸ points for n = 7, 9 and 3–4·10⁸ for n = 11, 13 (half that if coefficients outgrow
  2 bytes and the store widens to 4). The threshold sweep also keeps a heap entry per point outside
  each disk (70–110 bytes per point in all, measured), so about 2–3·10⁸ points. At 0.4–0.8·10⁶ points/s these
  runs take 10–20 minutes; memory, not time, is the limit. The paper's 10¹⁰ images are out of reach
  without packing the heap and using 8-byte table slots with stored hash bits.

## Results

All runs below use exact membership. "Finite" means the search was exhausted; "cap" means the cap
was reached and nothing is claimed.

### (i) Orbit growth of the origin as r ↑ r_c, n = 5, 8, 10, 12

**Preliminary table reproduced exactly.** Every row of the table in
[`arithmetic.md`](arithmetic.md) §3.2 is reproduced with r² = r_c² − δ for the quoted δ:
9 477, 112 539, 1 469 085 (n = 5), 16 297, 87 247, 468 095 (n = 8), 23 813, 216 043, 1 945 733
(n = 12), all finite, with the same maximal internal moduli (143.1, 612.1, 2 592.9; 114.6, 277.6,
674.6; 192.3, 722.3, 2 700.3).

**At r_c² itself** (the exact closed forms) the origin's orbit reaches the cap of 5·10⁷ for all four
n. The maximal internal moduli at the cap are 15 201 (n = 5), 5 886 (n = 8), 5 654 (n = 10) and
14 326 (n = 12).

**Thresholds.** The sweep from r = 0 up to r_c with a cap of 3·10⁷ found 320, 331, 205 and 103 exact
thresholds t_k = r_k² for n = 5, 8, 10, 12. All are elements of ℤ[ζ_n]⁺; for example n = 12,
t = 19 − 10√3 (= r₁²), 33 − 18√3, 227 − 130√3, 1003 − 578√3, 4429 − 2556√3, …; n = 8,
5 − 2√2, 25 − 16√2, 45 − 30√2, 65 − 44√2, 693 − 488√2, …. Most thresholds add only a few points; the
orbit grows in large jumps of a few recurring types. The gaps δ_k = r_c² − t_k at the large jumps,
grouped by type, are:

| n | jump type (size factor) | gaps δ_k | successive ratios | unit |
|---|---|---|---|---|
| 5 | ×3.4–3.7 | 7.5375e-2, 1.80893e-2, 4.28677e-3, 1.01289e-3 | 4.1668, 4.2198, 4.2322 | φ³ = 4.2361 |
| 10 | ×4.4 | 2.11132e-2, 5.01535e-3, 1.18570e-3 | 4.2097, 4.2299 | φ³ = 4.2361 |
| 8 | ×3.5 | 2.71965e-2, 1.13012e-2, 4.68732e-3, 1.94261e-3 | 2.4065, 2.4110, 2.4129 | 1 + √2 = 2.4142 |
| 8 | ×1.5 | 1.27370e-2, 5.35418e-3, 2.23121e-3, 9.26505e-4 | 2.3789, 2.3997, 2.4082 | 1 + √2 |
| 12 | ×3.9 | 2.02490e-2, 5.49830e-3, 1.47848e-3, 3.96531e-4 | 3.6828, 3.7189, 3.7286 | 2 + √3 = 3.7321 |
| 12 | ×2.25 | 1.67464e-2, 4.50663e-3, 1.20894e-3, 3.24036e-4 | 3.7159, 3.7277, 3.7308 | 2 + √3 |

- The ratios converge monotonically to the unit, from below. The unit that appears is φ³ for
  n = 5 and 10, and the fundamental unit itself, 1 + √2 and 2 + √3, for n = 8 and 12.
- For n = 5 the full pattern of jump types repeats with ratio φ³, but within one period the gaps
  between consecutive large jumps of *different* types are close to φ² and φ (for example
  1.809e-2 / 6.931e-3 = 2.61 and 6.818e-3 / 4.287e-3 = 1.59). So φ³ is the period of the whole
  pattern, not the smallest scale present.
- Orbit-size multiplier per period: about 11.6, 13.3, 13.5 (n = 5), 15.3, 15.4 (n = 10), 5.39,
  5.35, 5.38 (n = 8), 8.98, 9.09, 9.06 (n = 12).
- The gaps are **not** exactly self-similar: no gap equals u^e times an earlier gap, for u the
  fundamental unit and e = 1, …, 6 (checked exactly for every pair). The convergence of the ratios is
  asymptotic.

These agree with the preliminary F3 in [`experiments.md`](experiments.md) to the digits quoted
there (4.167, 4.220, 4.233 for n = 5; 2.410, 2.412 for n = 8; 3.690, 3.721 for n = 12), and extend
each sequence by one or two periods.

### (ii) The n ≡ 4 (mod 8) family

For every n ≡ 4 (mod 8) with 12 ≤ n ≤ 100 (12 values), the origin's orbit at r = g has exactly
**n² − 3n + 1** points: 109, 341, 701, 1 189, 1 805, 2 549, 3 421, 4 421, 5 549, 6 805, 8 189, 9 701.
Exactly 4n of the membership decisions in each run are points exactly on a boundary circle, which
is why the exact test matters here. The next threshold above g² is **exactly**
r₁² = 25 − 20cos θ − 16cos 2θ + 16cos 3θ − 4cos 4θ (equality checked in ℤ[ζ_n]⁺ for all 12 values),
so the count holds on the whole interval g ≤ r < r₁. At r = r₁ the orbit becomes 281, 1 101, 2 213,
14 065, 161 405, 62 933, 38 821, 273 485, 546 149, ≥ 2·10⁶ (cap), 158 885, 549 049 points for
n = 12, …, 100: finite in all cases except n = 84, where the cap of 2·10⁶ was reached. The
preliminary F2 count and the r₁ formula are confirmed exactly. The preliminary remark that the orbit
"jumps straight past 6·10⁴" at r₁ for n ≥ 44 does not hold literally: for n = 60 it becomes 38 821
points, and it is finite in every case tested except n = 84.

### (iii) n = 33 and other large n at the touching radius

- **Origin, n = 33.** Exactly 65 089 points at r² = g², and the same 65 089 at r² = g² + ε for
  ε = 10⁻¹², 10⁻⁹, 10⁻⁷, 10⁻⁶, 10⁻⁵, 5·10⁻⁵, 10⁻⁴, 1.1·10⁻⁴. The next threshold is
  r₁(33)² = g² + 1.20014·10⁻⁴ (r − g = 5.795·10⁻⁵), an exact element of ℤ[ζ₃₃]⁺ with coordinates
  `re:3541,-1398,-1726,2362,-780,-1122,1756,-544,-960,858`; four points enter there, and the orbit
  at that radius reaches the cap of 10⁸. This confirms the preliminary 65 089 "up to g + 5·10⁻⁵"
  and locates the end of the plateau exactly.
- **Other points, n = 33.** The lens corners are not in ℚ(ζ₃₃): a corner c = iy at r = g has
  c² = −(g² − 1) = 2ζ⁻¹(1 − ζ)², so c ∈ ℚ(ζ_n) would make 2ζ⁻¹ a square, and for odd n, where ζ⁻¹
  is a square, that needs √2 ∈ ℚ(ζ_n), i.e. 8 | n. Midpoints of orbit points are not integral.
  Instead, short sums of roots of unity inside the lens were used:

  | start (ζ-exponents with signs) | orbit at g² | orbit at g² + 10⁻⁴ |
  |---|---|---|
  | ζ⁴ − ζ⁹ + ζ¹⁴ | 1 537 | 1 537 |
  | 1 − ζ + ζ¹⁶ − ζ¹⁷ | 4 224 | 4 224 |
  | ζ¹¹ − ζ¹³ + ζ²⁷ − ζ²⁹ | 2 112 | 2 112 |
  | ζ²¹ − ζ²² − ζ²³ + ζ²⁴ | 10 560 | 10 560 |
  | ζ⁷ − ζ⁹ + ζ²² − ζ²⁴ | 2 112 | 2 112 |
  | ζ³ + ζ⁴ − ζ⁵ + ζ¹⁸ | 10 560 | 10 560 |
  | ζ²² − ζ²³ − ζ²⁷ + ζ²⁸ | 16 257 | ≥ 2·10⁷ (cap) |

  The last point is the interesting one. Its orbit is finite with 16 257 points at r = g, then
  grows through exact thresholds: 323 777 points at g² + 6.900·10⁻⁵, 7 411 713 at g² + 7.791·10⁻⁵,
  **36 300 353 (finite)** at g² + 7.936·10⁻⁵, and at least 8·10⁷ (cap) from the threshold
  g² + 7.941·10⁻⁵ on (r − g = 3.834·10⁻⁵), 47 thresholds in all. All of this lies below the end of
  the origin's plateau.
- **Other n at r = g (origin).** n = 41: 6 801 points; n = 50: 20 483; n = 49: 573 025;
  n = 64: 619 039; all finite. These match the preliminary F5 (M = 85 for n = 41, 6 801 = 1 + 80·85;
  20 483 = 1 + 98·209 for n = 50) and its statement that N0 exceeds 4·10⁵ for n = 49 and 64.

**What is established.** At r = g exactly, every orbit tested for n = 33, 41, 49, 50, 64 is finite,
with the exact sizes above. For n = 33 the origin's orbit stays at 65 089 points up to
r² = g² + 1.20014·10⁻⁴ and is at least 10⁸ there; one lens point has a finite orbit of 36 300 353 points at
r² = g² + 7.936·10⁻⁵ and an orbit of at least 8·10⁷ at r² = g² + 7.941·10⁻⁵. **What is not established.** No orbit has been shown to be infinite:
"cap reached" is all the engine can say. Whether these large orbits are infinite, and so whether the
table's r_c(33) is a true critical radius, remains open; the exact data now show that very large
orbits appear within about 4·10⁻⁵ of g for n = 33, from points other than the origin.

### Agreement with the preliminary numbers

Every preliminary orbit count that was re-checked agrees exactly: the §3.2 table of
[`arithmetic.md`](arithmetic.md), F2 (n² − 3n + 1 and r₁), the n = 33 plateau of 65 089 points, the
F3 unit ratios, F5 values for n = 41 and 50, and 2n − 1 points just below g (n = 5, 7, 12, 33). The
one statement corrected is the remark in E1c that the orbit at r₁ jumps past 6·10⁴ for n ≥ 44
(see (ii)).

## Possible next steps

1. Deep sweeps for n = 7, 9, 11, 13 to 2–5·10⁸ points (the rank-2 and higher unit lattices).
2. Pack the threshold heap (floats and indices in flat arrays) and store hash bits in the table, to
   reach about 10⁹ points within 32 GB.
3. Search the n = 33 lens systematically (all short sums of roots of unity) at r = g + 10⁻⁵ to
   locate the smallest radius with an orbit beyond 10⁸.
4. Prove the membership argument in Lean against Mathlib's definitions of the disks.
