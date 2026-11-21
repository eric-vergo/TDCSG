# Referee report: gap structure, rank conjecture and large-n table

Referee: Claude (independent of the authoring agent)

Notes refereed: [`gap-structure.md`](gap-structure.md), [`rank-conjecture.md`](rank-conjecture.md),
[`large-n-table.md`](large-n-table.md). Background used: [`engine.md`](engine.md),
`TDCSGCompute/Perm.lean`, `TDCSGCompute/Group.lean`, `TDCSGCompute/Main.lean`,
[`proofs/analytic-radius.md`](proofs/analytic-radius.md) (Proposition 9.1), and the text of arXiv
2302.12950.

## Verdicts

| claim | verdict |
|---|---|
| (G) the group changes at r_A; orders just above r_A; constant stretches; change at g; n = 5 events and the drop at the last one | **confirmed with caveats**. Every reproduced number agrees to all printed digits, and two orders were recomputed with independent code. One plain statement is wrong for the object it names (issue G1): GG_n(r) itself already changes **at** r = r_A. The order drop is reproduced and is not an engine bug (issue G3). |
| (R) for n = 7 one unit u = θ⁻¹(1 + θ)³ governs the threshold sequence; r_c(7) ≈ 1.623578–1.623583 | **confirmed with caveats**. The arithmetic of u and every threshold, ratio, norm and conjugate maximum I could reach are reproduced. The summary reports only the threshold ratio that matches u (issues R1, R2), and "one unit, not two" is weaker evidence than it reads (R3). |
| (T) n = 33: finite orbits up to g² + 10⁻⁵, earliest cap at r − g = 1.37·10⁻⁵; n = 80, 81 blow up within about 10⁻⁷ of g; conclusion "undetermined" | **confirmed**. Every number I re-ran is reproduced. "Undetermined" is the right conclusion and the tone is factual. The point count is overstated (T1). |

## The engine's group mode (claim G, method)

**What is computed.** `group` takes sample points w/p, with p a prime not dividing n and
w ∉ pℤ[ζ_n]. It computes their orbits exactly under a and b and discards any orbit that meets a
boundary circle or reaches a cap. On the union of the remaining orbits it forms the permutations
of a and b, drops constituents that are equivalent through an explicit commuting bijection, and
computes the order of the group they generate (`structuralOrder`, `Perm.lean`).

**Why the result is a lower bound.** Each kept orbit is a finite set closed under a and b. Since
a and b are injective, it is also closed under a⁻¹ and b⁻¹, so it is invariant under GG_n(r).
Restricting to it gives a homomorphism GG_n(r) → Sym(orbits). The image is a quotient of
GG_n(r), and its order is at most |GG_n(r)|, whether GG_n(r) is finite or infinite. This holds
whatever the sampling. Discarding orbits or dropping equivalent constituents does not affect it.
The note's word "quotient" is correct in this sense.

**Is `structuralOrder` right?** I checked the argument step by step against the code
(`Perm.lean`, lines 540–625):

1. **Jordan witness.** The code needs a transitive constituent of degree d ≥ 9 and an element
   with a cycle of prime length p, d/2 < p ≤ d − 3. No other cycle can have length divisible by
   p, so a power of the element is a p-cycle. Since p > d/2, the constituent is primitive, and
   Jordan's theorem then gives Alt(d). Correct.
2. **Kernel witness.** The code needs an element w with a cycle on O_i whose length does not
   divide m, the order of w on the non-big part R. Then w^m is trivial on R and non-trivial on
   O_i. So the kernel K of the action on R projects onto a non-trivial normal subgroup of a group
   containing Alt(O_i), and that projection contains Alt(O_i). Correct.
3. **K′ is the full product.** K′ is a subdirect product of the simple groups Alt(O_i). Suppose a
   diagonal linked two big constituents. G fixes each orbit, so it normalises that diagonal. The
   centraliser of Alt(d) in Sym(d) is trivial, and every automorphism is induced by a bijection
   when d ≠ 6. Together these make the two constituents equivalent, and equivalent ones were
   already dropped. So K′ = ∏ Alt(O_i) ⊆ G. Correct.
4. **The quotient.** The map g ↦ (g|_R, signs on the big orbits) has kernel G ∩ ∏ Alt(O_i), which
   by step 3 is ∏ Alt(O_i). So |G| = |image| · ∏ d!/2. Correct.

Schreier–Sims (`BSGS.build`/`complete`) is the standard deterministic algorithm with explicit
transversals. I read it and found no defect: Schreier generators are u_δ⁻¹ s u_γ, residues go into
levels l+1..j, and levels are re-completed deepest first.

The generic-point lemma is correct. A motion fixing w/p would force (1 − ζ^j)w ∈ pℤ[ζ_n], and
1 − ζ^j is invertible mod p. For the `--center` clouds at scale pD it also needs |α|, |β| < p,
which the defaults (k = 2, p = 1 000 003) satisfy.

The faithfulness argument for the group of maps modulo the arcs, G_gen, is correct as stated:
an element fixing a generic point is the identity on that point's atom.

The rim-vertex argument is also sound modulo its two stated assumptions:

- every orbit of atoms meets an atom bordering ∂D_L or ∂D_R;
- the circles bounding a sampled atom have centres among the germs of that atom's own orbit, so
  at the fixpoint each gap between crossing points is one atom on each side, provided δ is
  thinner than the atoms.

**Independent recomputation** (my own Python with exact arithmetic in ℤ[ζ_n], and sympy's
Schreier–Sims; no engine code). This code computed orbits, permutations and orders, either from
the engine's representative points (`--reps`) or from my own samples.

| case | engine | independent |
|---|---|---|
| n = 3, 4, 6, 5, 7, 8 below r_A (own grid plus 1 500 random rim samples) | n²(2n − 1)!/2 for n = 4, 5, 6, 7, 8 | the same: 40 320; 4 536 000; 718 502 400; 152 562 009 600; 41 845 579 776 000. (For n = 3 the order is 540 at r² ≤ 3 but larger at r² = 3.5 < r_A² = 4; Prop. 9.1 assumes n ≥ 5, so this is no conflict.) |
| disjoint disks, n = 5, 7, 8 | – | n² (25, 49, 64) |
| n = 5, r_A² − 10⁻⁶ and r_A | 4 536 000 | 4 536 000 |
| n = 5, r_A² + 10⁻⁹ | log₁₀ = 170.29510 | exactly the same integer, 1.97287…·10¹⁷⁰; it equals 39 375 000 000 · 9!/2 · (13!/2)² (25!/2)² (37!/2)² |
| n = 10, r_A² + 10⁻⁹ | log₁₀ = 131.84728 | 131.84728 (sympy, 63 s) |
| n = 8, r_A² + 10⁻⁹ | log₁₀ = 221.74292 | 221.74292 (sympy, 601 s) |

**Structure of the orders** (from the engine output, factored by me):

- **n = 5.** Q = 39 375 000 000 = 25 · 1 575 000 000, and 1 575 000 000 = 5⁷ · 8!/2. So the
  40-point constituent has the order of C₅⁷ ⋊ A₈, with 8 = 2n − 2 blocks of 5, and the sign points
  add nothing.
- **n = 7.** The 84-point constituent has order 2⁹·3⁵·5²·7¹²·11 = 7¹¹ · 12!/2, as stated.
- **All factorizations of Q in the note's table are correct** (n = 5, 7, 8, 10, 12).
- **Orders of ab and [a, b]** match for all five n.
- **Even n.** For n = 8 the 56-point imprimitive constituent has order
  5 850 436 087 893 196 800 = 2²⁶ · 14!, with 14 = 2n − 2. This is not of the C_n^{m−1} ⋊ A_m
  form, which the note claims only for n = 5 and 7. Consistent.

Every big degree is the size of a generic orbit, and the order is divisible by each orbit size,
as orbit–stabiliser requires.

**The n = 5 order drop: diagnosis.** I reproduced the drop with the same parameters:

- at r² = t − 10⁻⁹: 10^8685.5498;
- at r² = t + 10⁻⁹: 10^8488.7184;
- at r² = 3.8396, 3.842 and 3.845: 10^8488.7184 again.

Here t = (43052 − 24612φ)/841. Both radii use the same 7 018 samples and give 4 809 generic
orbits, 64 inequivalent constituents, and the identical integer Q (an 83-digit number). The only
difference is that four big constituents of degree 124 become four of degree 100. And indeed
4 · log₁₀(124!/100!) = 196.83, which is exactly the difference.

What happens to the points:

- The four 124-point representatives from below have, at t + 10⁻⁹, generic orbits of **143**
  points. These are equivalent as permutation actions to 143-point constituents that the upper
  run already has (checked with my own canonical-form code).
- The 100-point representatives from above had orbits of 81 points below t.
- So each fixed point's orbit grows, as the threshold monotonicity requires (124 → 143,
  81 → 100). But the set of inequivalent transitive actions loses its 124-point members and
  gains 100-point ones.

Independent random sampling at both radii found **no** constituent missing from the engine's list:
2 000 generic orbits per radius, at random angles on both rim circles, depths 10⁻¹¹ to 10⁻¹, a
different prime (≈ 10¹³). The engine's 64 constituents were reproduced exactly by my code. With sympy, the
124-point action below generates exactly A₁₂₄, and the 100-point action above exactly A₁₀₀.

Conclusion:

- **The drop is possibility (ii), possible.** There is no homomorphism between GG_n(r) and
  GG_n(r′). G_gen(r) is F₂ modulo the kernel of the action on atoms, and those kernels are not
  nested. Monotonicity in r holds for the orbit of a fixed point and, by boundary-contact.md, for
  infiniteness, but not for the order.
- **It is not a bug, and not a shortfall of the obvious kind.** Nothing is capped, the lost
  points are accounted for, and random sampling finds nothing new.
- **It cannot be certified as a decrease.** Both numbers are lower bounds, and the upper one is
  the order of G_gen(t + ε) only under the sampling assumptions. The note's sentence ("it may be
  real … or a sampling shortfall") is accurate. It should add this mechanism (issue G3).

## The unit for n = 7 (claim R)

- **u is a unit and a Pisot number.** θ = 2cos(2π/7), and u = θ⁻¹(1 + θ)³ has minimal polynomial
  x³ − 9x² − x + 1. Its real embeddings (θ ↦ θ₁, θ₂, θ₃) are σ₁(u) = 9.0978347,
  σ₂(u) = −0.3840429 and σ₃(u) = 0.2862083. So N(u) = −1, and u is a Pisot unit: one conjugate
  outside the unit disk, two inside.
- **The predicted rates and their pairing are right.** 1/|σ₂| = 2.6038755 and
  1/|σ₃| = 3.4939592. Take a self-similarity z ↦ c + u⁻¹(z − c), which contracts the physical
  plane by 9.098. It multiplies the σ_k-coordinate by σ_k(u)⁻¹. So the k = 2 spread should grow
  by 2.604 and the k = 3 spread by 3.494. The engine's conjugate k is ζ ↦ ζ^k (engine.md), which
  sends θ₁ to θ_k.
- **The units table is correct and complete.** The logarithmic embeddings of θ and 1 + θ, the
  regulator 0.5255, and the list of Pisot units θ^a(1 + θ)^b with σ₁ < 12 all check out. I
  enumerated |a|, |b| ≤ 12 and found exactly the six listed.
- **9.098 = 2.604 × 3.494 is the norm relation |N(u)| = 1.** In the Minkowski embedding, u
  preserves the covolume of ℤ[ζ₇]: the physical contraction (area factor σ₁²) is exactly offset by
  the internal expansion. Every unit satisfies this. So once the physical ratio is matched to a
  unit, the product of the two internal rates carries no independent information; only their
  split does. The observed products, 2.62 × 3.59 = 9.41 and 2.73 × 3.52 = 9.61, exceed 9.098 by
  3–6%. That is a measure of how noisy max|σ_k| is as a statistic.
- **Every reproduced number matches** (to a 5.4·10⁷ cap): the thresholds t₀…t₁₅₃ (k = 4, 6, 9,
  10, 24, 35, 46, 102, 153 compared in full), the plateau sizes up to 52 264 937, the ratios
  9.09425, 7.37915 and 8.25447, the norms 17 192, 131 768, 76 888 and 947 128, and the conjugate
  maxima at two plateaus (37.278 and 116.739; 97.743 and 418.855).
- **r_c(7).** Recomputing gives 1.623578 / 1.623580 / 1.623583 with ratio u. With each type's own
  observed ratio it gives 1.623578 / 1.623582 / 1.623591.
  - If the ratios approach u from below, as they do for n = 5, 8, 10 and 12, the u-based values
    are lower estimates.
  - The paper says its table is "good to about 5 decimal places". It also says estimates "may be
    too low because the points searched had very large but finite images".
  - So 1.623578–1.623591 against 1.623574 is consistent with the paper at its stated accuracy.
    The note's "spread of about 5·10⁻⁶" understates the model uncertainty (issue R2).

**Is "one unit, not two" justified?** Only in a weak sense:

1. **A single renormalisation always has a single scale.** Self-similarity at one point under one
   map always involves exactly one unit, even when the unit group has rank 2. So "the dynamics
   selects one Pisot unit at the origin's critical point" is what the data can support. They
   cannot distinguish that from "the scaling group has rank 1". A rank-2 effect would show as
   different units at different seeds or depths, or as quasi-periodic rather than periodic
   ordering of jump types (the paper's pattern change). The note says it does not reach that.
2. **The depth is one ratio per jump type.** Only one of the three ratios matches u closely
   (0.04%). The others are 19% and 9% low. For n = 5 the comparable first ratios were within 1.6%
   of φ³. Slow convergence is possible, but a 19% deviation at this depth is also what a
   competing scale would look like. The data do not decide.
3. **A finite-index sublattice is excluded within the tested set.** u is not a proper power of a
   smaller Pisot unit, since none has σ₁ = 9.098^{1/k} for k ≥ 2. So "u generates the observed
   scaling" is meaningful. u is also primitive in the unit group (θ⁻¹(1+θ)³ has coprime
   exponents).

## Issues

Severity: fatal / gap / minor / cosmetic.

### gap-structure.md

**G1 (gap). "At r_A it is still of order n²(2n − 1)!/2" is false for GG_n(r_A); it is true only
for G_gen.**

At r = r_A exactly (closed disks), the triple point (1 − ζ)/(1 + ζ) lies on boundary circles, and
its orbit is not generic. I computed it exactly:

| n | orbit | group induced on it |
|---|---|---|
| 5 | 8 points | order 20 160 = 8!/2 |
| 7 | 12 points | order 12!/2 |
| 8 | 14 points | order 14! |

For n = 5, this orbit together with the three generic orbits (5, 5, 9) generates a group of order
91 445 760 000 = 4 536 000 · 20 160. That is a certified lower bound for |GG₅(r_A)|. A₈ is simple
and not a quotient of C₅ × C₅ × A₉, so GG₅(r_A) ≇ GG₅(1). **The abstract group GG_n(r) changes at
r_A, not strictly after it.** What stays the same at r_A is the group modulo null sets.

The note does define G_gen, and it lists "elements supported on boundary arcs" as not
established. But the Summary item 1 ("at r = r_A itself"), Results ("the change is strictly after
r_A") and Answers item 1 state it for "the group".

*Repair:* say G_gen(r_A) in those three places, and add the triple-point computation as a proved
statement about GG_n(r_A).

**G2 (minor). The non-isomorphism just above r_A is proved, not only computed. Say so, and say at
which radii.**

The 13-point generic orbit for n = 5 at r_A² + 10⁻⁹ already proves GG₅(r) ≇ GG₅(1) there, since
13 ∤ 4 536 000; orbit–stabiliser suffices, and GG infinite would also be non-isomorphic. Likewise
for n = 7: there is a 43-point orbit, and 152 562 009 600 = 2⁹·3⁵·5²·7³·11·13, so 43 does not
divide it. For n = 8, 10 and 12 there are orbits of 29, 37 and 67 points, primes that do not divide
the old order.

This is the route analytic-radius.md suggests ("exhibit an orbit whose size does not divide that
order"). It is cleaner than the structural order, and it does not depend on sampling. But it holds
at the computed radii. Extending it to all of (r_A, 2 + φ) uses the event argument and sampling
completeness.

*Repair:* state the divisibility proof and the radii.

**G3 (minor). The order drop at (43052 − 24612φ)/841: record the mechanism and drop the hint of a
sampling shortfall.**

The diagnosis is in the section above: the 124-point constituents become 143-point orbits
equivalent to existing ones, 81-point ones become new 100-point ones, Q is unchanged, and
independent random sampling finds nothing missing. This makes a sampling shortfall unlikely.
A certified decrease would need an upper bound, which nothing provides.

*Repair:* add two sentences, and state that a decrease of G_gen is not excluded by any theorem.

**G4 (minor). Sampling-dependent statements are worded as facts in places.**

- "The group is constant on (8 − 4φ, 2 + φ)" holds at the 174 radii computed, under the sampling
  and centre-completeness assumptions.
- "Changes at g for every n where computed", and similar.

The body says this; the Summary should repeat it once.

**G5 (minor). Reproducibility.**

- The `walk` command is given for n = 5 only. The n = 7, 8 and 10 walks (1 002 intervals for
  n = 7, the 30-minute limit, the stopping radii 2.078 and 1.7804) cannot be rerun from the note.
- The time limits that stopped the walks are not stated as parameters.
- The binary was rebuilt during this review (11:50). Results should name the engine commit.

*Repair:* give the full command lines and the commit.

**G6 (cosmetic).** "Order exactly n²(2n − 1)!/2 at r_A² − 10⁻⁶" is the proved value
(Prop. 9.1). Say "reproduces" rather than "computes".

### rank-conjecture.md

**R1 (gap). The Summary row reports "threshold differences shrink by 9.094 per period" without
saying that the other two jump types give 7.379 and 8.254.**

Those are 19% and 9% below σ₁(u). That is the main counter-indication in the data, and it
appears only in the body.

*Repair:* give all three ratios in the Summary and the status paragraph. State that the depth is
one ratio per type.

**R2 (minor). The r_c(7) uncertainty is understated.**

Using u for the ×1.8 and ×3.2 types, whose observed ratios differ from u, is a modelling choice.
With the observed ratios the estimates are 1.623582 and 1.623591. If convergence is from below,
the u-based numbers are lower estimates.

*Repair:* quote the range 1.623578–1.623591. Note that this is still consistent with the paper's
"about 5 decimal places" and with its remark that its estimates may be too low.

**R3 (minor). Rank of the scaling group.**

- "No second independent scale is visible" should be "the self-similarity at the origin's critical
  point is by one Pisot unit". A single renormalisation is rank 1 regardless of the rank of the
  unit group.
- The triple match is less than three tests: given σ₁, the product of the internal rates is fixed
  by |N(u)| = 1.
- Add N(u) = −1 and the minimal polynomial x³ − 9x² − x + 1.

**R4 (minor). The deepest data were not reproducible within this review's memory limit.**

These are t₁₆₀, the sizes 94 359 561 and 94 367 065, and the cap at 10⁸ (about 7–11 GB). The
note should give the exact command (`thresholds -n 7 --cap 100000000 --format lines`) and the
memory used.

**R5 (cosmetic).** "2.7 periods" is ambiguous; it counts from the first ×3.2 jump to t₁₆₀. Say
"two complete periods of each jump type".

### large-n-table.md

**T1 (minor). "About 8 000 starting points … at r² = g², g² + 10⁻⁷, g² + 10⁻⁶ and g² + 10⁻⁵"
overstates.**

The table lists 279 + 1 943 + 288 + 4 032 = 6 542 starts. The 279 four-root sums are among the
1 943 five-root sums, so about 6 260 are distinct. The five-root and axis-grid sets were run only
at g² and g² + 10⁻⁵ (the table has dashes).

*Repair:* correct the count and the radii.

**T2 (minor).** "Every orbit is finite" should read "every tested orbit, at the tested radii".

**T3 (minor). Reproducibility.** The command parameters are missing for three runs:

- the clouds near a(0), b(0) and the corners (`--near`, `--scale`, `--spread`);
- the axis grid with spacing 1/1009;
- the "largest orbit tested at the table radius" for n = 31–81.

**T4 (cosmetic).** The table has 1 943 five-root sums at g. At g² + 10⁻⁵ I count 1 944 lens
candidates and 1 796 orbits; the note says "1 720 orbits" without giving the radius.

**Tone and conclusion.** "Undetermined" is right. The note does not claim the table entry is
wrong; it records what the exact engine does and does not see, and names what would settle it.
The comparison with n = 31, 35, 40 and 41 is the strongest argument for "undetermined", and it is
presented fairly. I found no overclaim beyond T1 and T2, and no underclaim.

## What I reproduced, with commands

Engine binary `TDCSG/.lake/build/bin/tdcsg-orbit`. The 10:30 build was used for the first runs;
later runs used a copy of the 11:50 build at
`/private/tmp/claude-501/-Users-eric-Github-riemann-hypothesis/8e07d302-d180-4cc0-ac7d-117a36aae2f9/scratchpad/refcamp/tdcsg-orbit-snap`.
Both builds agree on every overlapping run. Independent code and outputs are in that same
directory (`tdcsg.py`, `check_reps.py`, `indep.py`, `atra.py`, `drop*.py`, `randsample.py`,
`norms.py`).

**Group orders** (`group -n N --r2 R --grid 11 --center necklace --fix --reps`), log₁₀|G|:

| n | r_A² − 10⁻⁶ | r_A | r_A² + 10⁻⁹ | r_A² + 10⁻⁶ |
|---|---|---|---|---|
| 5 | 4 536 000 | 4 536 000 | 170.29510 | 170.29510 |
| 7 | 152 562 009 600 | same | 583.70846 | 583.70846 |
| 8 | 41 845 579 776 000 | same | 221.74292 | 221.74292 |
| 10 | 6 082 255 020 441 600 000 | same | 131.84728 | 131.84728 |
| 12 | 1 861 345 205 199 718 318 080 000 | same | 766.82316 | 766.82316 |

The alternating degrees and the Q factorizations match the note's tables.

**Later events**, same options:

| n | r² | log₁₀|G| |
|---|---|---|
| 5 | (2 + φ) ∓ 10⁻⁹ | 170.29510 / 268.74190 |
| 5 | g² ∓ 10⁻⁹ | 4 910.7330 / 5 396.7353 |
| 8 | g² − 10⁻⁹ | 5 332.4832 |
| 10 | g² ∓ 10⁻⁹ | 1 276.9049 / 1 804.9698 |
| 12 | g² ∓ 10⁻⁹ | 841.46294 / 1 667.7121 |
| 7 | 2.4 | 583.70846 (supports "constant up to 2.444") |
| 5 | t ∓ 10⁻⁹, t = (43052 − 24612φ)/841 | 8 685.5498 / 8 488.7184 |
| 5 | 3.8396, 3.842, 3.845 | 8 488.7184 |

The last two rows were run as
`--r2 're:18439999999159/841000000000,-24612/841'` and `'re:18440000000841/841000000000,-24612/841'`.

**n = 7 thresholds.** `thresholds -n 7 --cap 10000000 --format lines` (16 s, 0.7 GB) and
`--cap 54000000` (101 s, 4.9 GB peak). They give thresholds 0–153 with the stated values and
sizes through k = 102 (52 264 937). `orbit -n 7 --r2 re:299,-172,184` and
`--r2 re:4389,-2514,2812 --cap 3000000` give the conjugate maxima.

**n = 33.**

- `orbit -n 33 --r2 touch` gives 65 089 (finite).
- `scan -n 33 --r2 touch --terms 4` and `--r2 touch+1e-5` give 279 candidates, 265 orbits, maximum
  65 089 at both.
- `scan -n 33 --r2 touch+1e-5 --terms 5 --cap 3000000 --total-cap 5000000` gives 1 944
  candidates, all finite, maximum 78 529.
- `thresholds -n 33 --start pow:0,0,-1,0,0,0,1,0,0,0,0,-1,1,-1,0,0,0,1,0,-1 --from touch --rc touch --cap 20000000`
  gives 53 313, 101 697, 110 529 and 18 057 213 (finite), then the cap at r² − g² = 2.843·10⁻⁵
  (r − g = 1.37·10⁻⁵). That is the same threshold as the note's cap of 6·10⁷.

**n = 80, 81.**

- `orbit --r2 touch` gives 1 269 847 and 478 881 (finite).
- `thresholds --from touch --rc touch --cap 20000000` reaches the cap at r − g = 9.5·10⁻⁸ (n = 80)
  and 1.34·10⁻⁷ (n = 81). The n = 81 run peaked at 6.9 GB.

**Independent code.** `indep.py` (own samples, n = 3–8 below r_A and disjoint disks),
`check_reps.py`/`n8.py` (n = 5, 8, 10 above r_A from engine representatives), `atra.py` (the
triple point at r_A), `drop*.py`/`randsample.py` (the order drop), `norms.py` (exact norms and
ratios). Disk membership is decided by 50–120-digit evaluation together with the Liouville bound
|D| ≥ B^{−(m−1)}, checked at every decision.

## What I did not check

- The n = 7 data beyond 5.4·10⁷ points (t₁₅₄–t₁₆₀, the 10⁸ cap): memory limit.
- The n = 9, 11 and 13 sections of rank-conjecture.md.
- The full walks: the 142 n = 5 candidates, the n = 7 walk to 2.444, the n = 8 and 10 walks. I did
  not check the claim "only r_A², 36 − 20φ and g² among the 30 lattice thresholds are changes", or
  the `events` table.
- Group orders above r_A for n = 7 and 12 with independent code (sympy is too slow at degree
  about 500).
- Large-n rows other than those listed: n = 31, 35, 40 and 41, the near-point clouds, the axis
  grid, and the odd-n r₁ table.
- Whether elements supported on arcs make |GG_n(r)| larger than |G_gen(r)| on open intervals
  (r_A, r_c). G1 shows they do at the event r_A itself.
- A literature pointer I did not verify: work by Lowenstein, Kouptsov and Vivaldi on piecewise
  rotations with 7-fold symmetry (Nonlinearity, about 2004) may already describe the cubic
  renormalisation unit. Worth checking before claiming novelty.
