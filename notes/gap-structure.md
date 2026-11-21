# The group inside the continuation gap

Authors: Eric Vergo and Claude (Anthropic).

**Question.** By [`proofs/analytic-radius.md`](proofs/analytic-radius.md), invariant analytic
functions become constant at r_A(n) = sec(π/n), the group GG_n(r) has order n²(2n − 1)!/2 on
[1, r_A), and the orbit structure changes at r_A. Whether the abstract group changes at r_A was
open. This note computes the group on [r_A, r_c): where it changes, and how large it is in
between.

**Status.** Everything here is **[computed]** with the engine's group mode
([`engine.md`](engine.md), "The group as a permutation group"), with exact disk membership, except
the two statements labelled **[proved]** (the change at r_A itself and the non-isomorphism just
above it). The arguments behind the method are written out, and the sampling step is a computation,
not a proof. This note was independently refereed; the report, with its verdicts, reproductions and
the list of what the referee did not check, is
[`referee-report-engine-campaign.md`](referee-report-engine-campaign.md).

Two groups appear throughout. GG_n(r) is the group of bijections of the plane; G_gen(r) is the
group of the same maps modulo agreement off the discontinuity arcs (a null set; see Definitions).
GG_n(r) maps onto G_gen(r). Every order computed from generic orbits is a certified lower bound for
both; that it equals |G_gen(r)| depends on the sampling being complete.

## Summary

1. **The group changes at r_A.**
   - **At r = r_A itself, GG_n(r_A) already differs from GG_n(1)** **[proved]**, by an exact orbit
     computation in the referee's independent code. At r = r_A the triple point (1 − ζ)/(1 + ζ) lies
     on the boundary circles; its orbit has 8 points for n = 5 (12 for n = 7, 14 for n = 8), and the
     group induces A₈ on it (12!/2 and 14! for n = 7, 8). For n = 5 this orbit together with the
     generic orbits of 5, 5 and 9 points generates a group of order 91 445 760 000 = 4 536 000 · 8!/2,
     a certified lower bound for |GG₅(r_A)|. A₈ is simple and is not a quotient of C₅ × C₅ × A₉, so
     GG₅(r_A) ≇ GG₅(1).
   - **Modulo null sets the change comes only after r_A.** For n = 5, 7, 8, 10, 12 the computation
     reproduces the order n²(2n − 1)!/2 of Proposition 9.1 at r² = r_A² − 10⁻⁶, and gives the same
     order for G_gen(r_A) at r = r_A (generic orbits never meet the boundary circles).
   - **Just above r_A** (r² = r_A² + 10⁻⁹ and r_A² + 10⁻⁶, identical results) the computation
     certifies a group of order at least

     | n | n²(2n − 1)!/2 | lower bound just above r_A | alternating constituents |
     |---|---|---|---|
     | 5 | 4.54·10⁶ | 10^170.30 | A₉, A₁₃², A₂₅², A₃₇² |
     | 7 | 1.53·10¹¹ | 10^583.71 | A₁₃, A₂₅², A₄₃², A₆₁², A₇₉² |
     | 8 | 4.18·10¹³ | 10^221.74 | A₁₅, A₂₉², A₅₀² |
     | 10 | 6.08·10¹⁸ | 10^131.85 | A₁₉, A₃₇² |
     | 12 | 1.86·10²⁴ | 10^766.82 | A₂₃, A₄₅², A₆₇², A₁₂₂² |

     For n = 5 the exact integer is 39 375 000 000 · (9!/2) · (13!/2)² · (25!/2)² · (37!/2)²
     ≈ 1.97287·10¹⁷⁰; the referee reproduced it independently, and also the n = 8 and n = 10 values.
   - **GG_n(r) ≇ GG_n(1) at these radii** **[proved]**, independently of the sampling: at
     r_A² + 10⁻⁹ there is a generic orbit whose size does not divide n²(2n − 1)!/2, which by
     orbit–stabiliser excludes an isomorphism (and an infinite group would not be isomorphic
     either). The orbit sizes are 13 for n = 5 (4 536 000 = 2⁶·3⁴·5³·7), 43 for n = 7
     (152 562 009 600 = 2⁹·3⁵·5²·7³·11·13), and the primes 29, 37, 67 for n = 8, 10, 12, which
     exceed every prime factor of the old order. This holds at the radii computed; extending it to
     a whole interval uses the event argument and the sampling assumptions.
2. **Then it stays constant for long stretches** (at the radii computed, under the sampling and
   centre-completeness assumptions of Method steps 4 and 5). For n = 5 the computed group is the
   same at both radii of every interval between consecutive candidate events from r_A² = 8 − 4φ up
   to 2 + φ = 3.618 (87 intervals, 174 radii); for n = 7 from r_A² = 1.232 up to at least r² = 2.444
   (1 002 intervals; g(7)² = 2.506); for n = 8 up to r² = 2 (34 intervals).
3. **n = 5, the first events** (r² exact):

   | event r² | value | log₁₀ of the order after it | kind |
   |---|---|---|---|
   | (below r_A) | | 6.657 (n²(2n − 1)!/2 = 4 536 000) | |
   | 8 − 4φ = r_A² | 1.5278640 | 170.295 | triple point (−1, 1, a(1)) |
   | 2 + φ | 3.6180340 | 268.742 | tangency (vertex ζ²) |
   | 36 − 20φ | 3.6393202 | 4 910.733 | triple point |
   | 7 − 2φ = g² | 3.7639320 | 5 396.735 | tangency (the touching radius) |

   The computed group is the same at r² = g² − 10⁻⁹ and g² − 10⁻⁶ (10^4910.733), and at g² + 10⁻⁹
   and g² + 10⁻⁶ (10^5396.735). The walk also reaches g² and finds the change there.

   **n = 8**: constant from r_A² = 4 − 2√2 up to r² = 2; changes at 2 (10^364.014) and at
   36 − 24√2 ≈ 2.05887 (10^5332.483), which is still the order at r² = 2.078 (where the walk
   stopped) and at g² − 10⁻⁹.

   **n = 10**: constant from r_A² = (12 − 4φ)/5 up to 8 − 4φ ≈ 1.52786 (7 intervals); then
   10^1276.905 up to g² = 5 − 2φ, 10^1804.970 from g², and 10^3205.287 from (792 − 484φ)/5 ≈ 1.77431;
   the walk stopped at 1.7804. (n = 12 was not walked.)
4. **The computed group changes at the touching radius g** for every n where it was computed (each
   order a certified lower bound; that the two sides differ as groups G_gen rests on the sampling):

   | n | g² | log₁₀ order at g² − 10⁻⁹ | log₁₀ order at g² + 10⁻⁹ |
   |---|---|---|---|
   | 5 | 7 − 2φ | 4 910.733 | 5 396.735 |
   | 8 | 5 − 2√2 | 5 332.483 | 6 031.670 |
   | 10 | 5 − 2φ | 1 276.905 | 1 804.970 |
   | 12 | 5 − 2√3 | 841.463 | 1 667.712 |

   (n = 7 was not computed: one group computation at g² − 10⁻⁹ did not finish within its 30-minute
   limit.) For n = 5 and 8 the first change after r_A is at r² = |1 − ζ²|² (2 + φ and 2).
5. The radii at which lattice points change their orbits (the *lattice thresholds*) are a
   different, larger set: for n = 5, of the 30 lattice thresholds in [1, g²], only r_A², 36 − 20φ
   and g² are changes of the computed group, and the change at 2 + φ is not a lattice threshold.
6. **Not reached**: the accumulation of events toward r_c. The group computation slows down sharply
   once orbits of generic points reach 10⁴–10⁵ points (n = 5 beyond r² ≈ 3.85, compared with
   r_c² = 4.618), so no statement about the ratios of successive gaps r_c² − r_k² comes from this
   note. The unit ratios of the origin's threshold sequence near r_c are in [`engine.md`](engine.md),
   results (i).

## Definitions

- GG_n(r) is generated by a and b on the closed disks D_L, D_R of radius r about −1 and 1
  ([`overview.md`](overview.md)). On (1, r_c) it is finite.
- Each element is a *motion* z ↦ ζ^j z + t (t ∈ ℤ[ζ_n]) on each piece of a finite partition, and is
  discontinuous only on finitely many circle arcs. The **atoms** are the connected components of the
  complement of the union Σ of these arcs over all elements. Every element is a single motion on
  each atom, and the group permutes the atoms.
- G_gen(r) is the group of these maps modulo agreement off Σ (a null set). GG_n(r) maps onto it; its
  order is a lower bound for |GG_n(r)|. Elements that differ only on boundary arcs are not separated,
  and at r = r_A they make GG_n(r_A) strictly larger than G_gen(r_A) (Summary, item 1).
- A **germ** is a motion that some element has on some atom; its **centres** are ζ^{−j}(∓1 − t), the
  centres of the circles m⁻¹(∂D_L), m⁻¹(∂D_R) on which the arcs of Σ lie.
- An **event** is a radius at which the arrangement of arcs changes combinatorially. As r varies
  between events, atoms deform continuously and the action of a, b on atoms, together with the
  motions (which do not depend on r), stays the same, so G_gen is constant between events.
  Every event is a tangency |c₀ − c| = 2r or a triple point (the circumradius of c₀, c, c′), with
  c₀ ∈ {−1, 1} and c, c′ centres: three arcs meeting, or two touching, can be moved by a group
  element so that one of them lies on ∂D_L or ∂D_R. So every event r² lies in ℚ(ζ_n)⁺ and has a
  vertex in ℚ(ζ_n).
- The **lattice thresholds** are the radii at which the orbit of the origin or of a lattice point
  (1 − ζ)x, x with power-basis coefficients in [−B, B], in the lens, changes (`events`). The partition
  of the plane into orbits changes at every event; a lattice threshold is an event only if the
  lattice point is a vertex of the arrangement there.

## Method

1. **Generic points.** Samples are points w/p with p a prime not dividing n (or w/(pD) with
   p ∤ D) and w ∉ pℤ[ζ_n]. Such a point is fixed by no non-trivial motion, nor is any point of its
   orbit. Orbits that meet a boundary circle exactly are discarded.
2. **Lower bound and faithfulness.** Each kept orbit is finite and invariant under a and b, hence
   under the group, so restriction gives a homomorphism from GG_n(r) onto the computed permutation
   group: its order is a lower bound whatever the sampling. If g fixes a generic point x, g is a
   motion near x fixing x, hence the identity on the atom of x. Points in the same atom, or in atoms
   of one orbit of atoms, have the same stabiliser, so their orbits give equivalent permutation
   actions; the engine drops equivalent constituents after checking an explicit bijection. If the
   samples meet every orbit of atoms, the action on the union of their orbits is faithful for
   G_gen(r).
3. **Order** (`structuralOrder` in `TDCSGCompute/Perm.lean`). A constituent of degree d ≥ 9 with an
   element having a cycle of prime length p, d/2 < p ≤ d − 3, is primitive and contains A_d
   (Jordan). If each such constituent also has a *kernel witness*, an element whose power acting
   trivially on all other constituents is non-trivial on it, then, all constituents being pairwise
   inequivalent, the group contains the full product of these alternating groups. Its order is
   |Q| · ∏ d!/2, with Q the image on the other constituents plus the signs, computed by
   deterministic Schreier–Sims. The output is labelled certified only if every witness was found.
   Checks: Schreier–Sims on S₈, A₉, M₁₁, M₁₂ and 24 random groups against brute-force closure; the
   structural order against Schreier–Sims on all constituents for n = 5, 7, 8 just above r_A. The
   referee checked the argument against the code step by step.
4. **Sampling** (a computation, not a proof). Every orbit of atoms contains an atom adjacent to
   ∂D_L or ∂D_R along an arc (follow a boundary arc of an atom back through the first generator
   that is discontinuous there). The samples are a coarse grid, clouds around the triple point
   (1 − ζ)/(1 + ζ) of r_A, and *rim-vertex* samples. Along each boundary circle, on both sides at
   depth 10⁻¹¹, one sample is placed between every pair of consecutive crossing points with circles
   about the centres seen so far; this is iterated until no new crossing point appears (`--fix`).
   At the fixpoint each gap is a single atom on each side. The two assumptions, that the
   crossing points found are all of them and that 10⁻¹¹ is thinner than the atoms at the sampled
   points, are not proved. They are supported by the results being unchanged between r_A² + 10⁻⁹
   and r_A² + 10⁻⁶, under grid refinement (11, 23, 47, 97), by the exact recovery of
   n²(2n − 1)!/2 below r_A, and by the referee's independent random sampling (see the order drop
   below). Without rim-vertex samples, grids miss thin atoms: at r_A² + 10⁻³, grids up to 97 give
   10^15.85 for n = 5, against 10^170.30 with them.
5. **Walk** (`walk`). From an event t: compute the group at t + 10⁻⁹, derive from the centres of
   its germs the next candidate event t′ > t, recompute the group at a rational inside (t, t′), and
   continue from t′. `consistent` means the two computations agree. G_gen can change only at
   candidates, so the walk visits every change once the centres are complete.

## Results

### Below and at r_A

| n | r_A² | at r_A² − 10⁻⁶ | G_gen at r_A | n²(2n − 1)!/2 |
|---|---|---|---|---|
| 5 | 8 − 4φ | 4 536 000 | 4 536 000 | 4 536 000 |
| 7 | 1.2319141 | 152 562 009 600 | 152 562 009 600 | 152 562 009 600 |
| 8 | 4 − 2√2 | 41 845 579 776 000 | 41 845 579 776 000 | 41 845 579 776 000 |
| 10 | 2.4 − 0.8φ | 6 082 255 020 441 600 000 | same | same |
| 12 | 8 − 4√3 | 1 861 345 205 199 718 318 080 000 | same | same |

The constituents are the lens orbit (A_{2n−1} or S_{2n−1}) and two orbits of n points, as in
Proposition 9.1. At r = r_A the generic group is still this one, but GG_n(r_A) itself is larger:
the orbit of the triple point (1 − ζ)/(1 + ζ), which lies on the boundary circles, carries a further
alternating or symmetric group (A₈, 12!/2, 14! for n = 5, 7, 8; Summary, item 1). So the abstract
group changes at r_A, and G_gen changes strictly after it.

### Just above r_A

At r² = r_A² + 10⁻⁹ and r_A² + 10⁻⁶ the computations agree exactly for every n. The order is
|Q| · ∏ d!/2 over the alternating constituents of the summary table, with

| n | Q (exact) | constituents in Q | orders of ab, [a, b] |
|---|---|---|---|
| 5 | 39 375 000 000 = 2⁶·3²·5¹⁰·7 | C₅, C₅, a 40-point action with blocks of 5 and order 1 575 000 000 = 5⁷·8!/2 | 757 575, 5 610 |
| 7 | 2⁹·3⁵·5²·7¹⁴·11 | C₇, C₇, an 84-point action with blocks of 7 and order 7¹¹·12!/2 | 5 185 605 425, 259 350 |
| 8 | 2⁴²·3⁵·5²·7²·11·13 | two 8-point actions, a 56-point action with blocks of 2 and order 2²⁶·14! | 226 200, 2 184 |
| 10 | 2¹⁷·3⁸·5²²·7²·11·13·17 | two 10-point actions, a 90-point action with blocks of 5 | 119 510, 210 |
| 12 | 2⁴³·3³²·5⁴·7³·11²·13·17·19 | two 12-point actions, a 132-point action with blocks of 2 | 118 441 260, 924 |

For n = 5 and 7 the imprimitive constituent has the order of C_n^{m−1} ⋊ A_m with m = 2n − 2 blocks
(the structure itself was not computed); for n = 8 its order 2²⁶·14! is not of that form. The
imprimitive constituent is found by the clouds around the triple point (1 − ζ)/(1 + ζ); the new
alternating constituents are found only by the rim-vertex samples, in thin pieces along the
boundary circles. For n = 5 their degrees 13, 25, 37 include 3n − 2 = 13, the lower bound of
Proposition 9.1(4) for orbits just above r_A.

### n = 5 from r_A to g and beyond

The walk found 142 candidate events in (r_A², r_c²) from the germs just above r_A, and visited them
in order. Under the sampling assumptions, the group:

- is constant, 10^170.295, on (8 − 4φ, 2 + φ): 87 intervals, each checked at two radii;
- is 10^268.742 on (2 + φ, 36 − 20φ);
- just above 36 − 20φ the walk first finds 10^4542.6 and then, inside the interval, 10^4910.7. The
  pieces that open at 36 − 20φ are thinner than the sampling depth at 36 − 20φ + 10⁻⁹. From the next
  candidate (10 633 972 − 6 500 052φ)/32 041 ≈ 3.641176 on, the order is 10^4910.733 at both radii
  of every interval up to at least 3.6965, and at g² − 10⁻⁶ and g² − 10⁻⁹;
- is 10^5396.735 from g² (at g² + 10⁻⁹, g² + 10⁻⁶ and in the walk);
- then changes at (12364 − 5676φ)/841 ≈ 3.781259 (10^5901.613), at (4000 − 2188φ)/121 ≈ 3.799518
  (10^7155.476), at 2659 − 1641φ ≈ 3.806224 (10^8118.788), at (3044 − 1596φ)/121 ≈ 3.815023
  (10^8527.683), at (4224 − 1756φ)/361 ≈ 3.830283 (10^8685.550) and at
  t = (43052 − 24612φ)/841 ≈ 3.839414 (10^8488.718), each consistent at both radii of its
  interval. The walk stopped at its time limit at r² ≈ 3.848 (r_c² = 4.618).

**The order drop at t.** The last change is a decrease, 10^8685.550 → 10^8488.718, and the referee
found its mechanism. Both radii t ∓ 10⁻⁹ use the same 7 018 samples, give 4 809 generic orbits, 64
inequivalent constituents and the identical quotient order Q. The only difference is that four
alternating constituents A₁₂₄ become four A₁₀₀, and 4·log₁₀(124!/100!) = 196.83 is exactly the
difference of the logarithms. Each fixed point's orbit grows, as it must: the 124-point orbits from
below have 143 points above t and are then equivalent to 143-point constituents already present, and
81-point orbits from below become new 100-point ones. Independent random sampling at both radii
(2 000 generic orbits per radius, depths 10⁻¹¹ to 10⁻¹, another prime) found no constituent missing
from the engine's list, so a sampling shortfall is unlikely. No theorem makes |G_gen(r)| monotone
in r: there is no homomorphism between the groups at different radii, only orbits of fixed points
and infiniteness are monotone. A genuine decrease cannot be certified from lower bounds alone; it
would need an upper bound, which nothing here provides.

### The lattice thresholds

`events` merged the thresholds of the origin and of the lattice points (1 − ζ)x in the lens
(coefficients in [−B, B]) with a cap of 10⁵ points per orbit. The lists are complete up to the
value given (the least last threshold of an orbit that reached the cap).

| n | B | points | thresholds | complete up to r² = |
|---|---|---|---|---|
| 5 | 2 | 33 | 103 | 4.5999 |
| 7 | 1 | 54 | 114 | 2.6341 |
| 8 | 2 | 27 | 71 | 2.9162 |
| 10 | 2 | 34 | 102 | 2.3689 |
| 12 | 2 | 26 | 47 | 1.8904 |

For n = 5 the thresholds in [1, g²] are 1, 48 − 29φ, 19 − 11φ, 37 − 22φ, **8 − 4φ**, 55 − 33φ,
26 − 15φ, 73 − 44φ, 167 − 102φ, 91 − 55φ, 15 − 8φ, 62 − 37φ, 33 − 19φ, 80 − 48φ, 4 − φ, 98 − 59φ,
40 − 23φ, 87 − 52φ, 11 − 5φ, 134 − 81φ, 29 − 16φ, 76 − 45φ, 47 − 27φ, 170 − 103φ, 18 − 9φ,
141 − 85φ, 65 − 38φ, **36 − 20φ**, 83 − 49φ, **7 − 2φ**, with the changes of the computed group in
bold. Those below r_A (1.077, 1.202, 1.403) are not changes, by Proposition 9.1. The 22 between r_A²
and 36 − 20φ all lie in (r_A², 2 + φ), where the computed group is the same at all 174 radii the walk
computed.

### Commands

All runs used the engine at commit 4dd9017 (builds of the working tree that differed from it only
in output formatting, line wrapping and the default `--total-cap`, which was given explicitly where
it mattered), with `B=.lake/build/bin/tdcsg-orbit` in the repository. Time limits were imposed with
`gtimeout`.

```sh
# group at one radius (r_A, g and the regression values); g checks: 30 min (n = 5, 7), 15 min (8, 10, 12)
$B group -n N --r2 ra+1e-9 --grid 11 --center necklace --center-p 100000007 --fix --format lines
$B group -n N --r2 touch-1e-9 --grid 11 --center necklace --center-p 100000007 --fix \
   --total-cap 6000000 --orbit-cap 500000 --format lines
# walks: n = 5 with a 90-minute limit (default caps); n = 7, 8, 10 with 40-minute limits
$B walk -n 5 --lo ra --hi closed --grid 11 --center necklace --center-p 100000007 --max-steps 100000
$B walk -n 7 --lo ra --hi touch+1 --grid 11 --center necklace --center-p 100000007 \
   --max-steps 100000 --total-cap 10000000
$B walk -n 8 --lo ra --hi closed --grid 11 --center necklace --center-p 100000007 \
   --max-steps 100000 --total-cap 10000000          # likewise n = 10
# lattice thresholds (B = 1 for n = 7, B = 2 otherwise; upto 2.635992533476 for n = 7)
$B events -n 5 --lens-B 2 --lo 1 --upto closed --cap 100000
```

The `--fix` defaults are depth 10⁻¹¹, scale 10 000 000 000 037 and at most 12 rounds; `--eps` of
`walk` is 10⁻⁹. The referee's reproductions, with their own command lines, are in the report.

## Answers

1. **Does the group change exactly at r_A?** Yes, for n = 5, 7, 8, 10, 12. GG_n(r_A) itself already
   differs from GG_n(1) (proved for n = 5 through the triple-point orbit, with the induced groups
   computed for n = 7, 8), while G_gen(r_A) still has order n²(2n − 1)!/2. Just above r_A the group
   is not isomorphic to GG_n(1) (proved at r_A² + 10⁻⁹ by orbit sizes), and its order is at least
   the values in the summary, which are certified lower bounds. Under the sampling assumptions,
   for n = 5 the group is then constant up to 2 + φ, and for n = 7 up to at least r² = 2.444.
2. **Orders above r_A and at subsequent events**: the tables above; for n = 5 up to r² ≈ 3.848,
   for n = 8, 10 up to where the walks stopped, for n = 7, 12 just above r_A (and at g for 12).
3. **Accumulation toward r_c**: not reached by this computation.
4. **An event at g?** The computed group changes at g for n = 5, 8, 10, 12 (table in the summary);
   not computed for n = 7.

## What is not established

- That the computed orders are the full G_gen(r) (sampling assumptions, Method step 4). All
  statements of constancy and of change between radii, and the change at g, depend on them; the
  lower bounds and the non-isomorphism statements do not.
- How much larger |GG_n(r)| is than |G_gen(r)| because of elements supported on the arcs, except at
  r = r_A, where it is larger.
- The completeness of the event list: the walk visits every candidate obtained from the centres it
  has seen; centres from atoms it never sampled would be missed.
- Whether the order drop at (43052 − 24612φ)/841 is a genuine decrease.
- The structure of the imprimitive constituents beyond their order and block size.
- Everything beyond the radii listed; in particular the behaviour near r_c.
- Not checked by the referee: the full walks (the 142 n = 5 candidates, the n = 7 walk to 2.444,
  the n = 8 and 10 walks), the claim about the 30 lattice thresholds and the `events` table, and
  the orders above r_A for n = 7 and 12 with independent code.
