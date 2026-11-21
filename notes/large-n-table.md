# The large-n entries of the critical-radius table

Authors: Eric Vergo and Claude (Anthropic).

**Question.** The paper's Appendix A gives r_c(33) = 1.035512, which equals the touching radius
g(33) = |2 − ζ₃₃| = 1.035512053 to six decimals, and for n ≥ 79 every entry equals g(n) to rounding
([`experiments.md`](experiments.md), E1b). The exact engine finds that at r = g(33) the orbits it has
tested are finite and moderate in size, and that the first orbits reaching its cap appear only some
4·10⁻⁵ above g ([`engine.md`](engine.md), results (iii)). This note looks for orbits that are large at
or just above g(33), and compares with other n. The table is the work of the repository owner and
coauthors; the aim is to record what the exact computation does and does not see.

**Status.** All numbers are **[computed]** with exact membership (commands at the end). "Finite"
means an exhausted search; "cap" means the cap was reached and nothing is claimed about finiteness.
The paper imaged points with at least 10¹⁰ images; the caps here are 2·10⁶ to 10⁸. The conclusion
is "undetermined". This note was independently refereed; the report, with its verdicts,
reproductions and the list of what the referee did not check, is
[`referee-report-engine-campaign.md`](referee-report-engine-campaign.md). The referee reproduced the
n = 33 origin, the four- and five-root scans, the sweep of the earliest-capping point and the
n = 80, 81 rows; it did not check the n = 31, 35, 40, 41 rows, the near-point clouds, the axis grid
or the odd-n table of r₁.

## Summary

1. **n = 33, at g and just above.** About 6 260 distinct starting points were tested, not all at
   every radius (see the table below): every signed sum of up to five 33rd roots of unity in the lens
   (one per symmetry class; at r² = g² and g² + 10⁻⁵, the four-root sums also at g² + 10⁻⁷ and
   g² + 10⁻⁶), generic points near the touching points a(0), b(0) and near the lens corners (at all
   four radii), and a grid of generic points along the lens axis (at g² and g² + 10⁻⁵); r − g is at
   most 4.8·10⁻⁶. **Every tested orbit, at the tested radii, is finite.** The largest has 65 089
   points at g (the origin's) and 78 529 at g² + 10⁻⁵.
2. **The first caps for n = 33.** Sweeping the seven largest lens orbits upward from g, the
   earliest reaches the cap of 6·10⁷ at r² − g² = 2.843·10⁻⁵ (r − g = 1.37·10⁻⁵), right after a finite
   orbit of 18 057 213 points; the others reach it between 4.0·10⁻⁵ and 1.5·10⁻⁴. All of this is far
   above the table's resolution of about 5·10⁻⁷. The earliest cap comes closer to g the more points
   are searched (r − g = 3.8·10⁻⁵ for the best four-root point, 1.37·10⁻⁵ for the best five-root
   point), so points blowing up still closer to g may well exist.
3. **The same picture for n = 31, 35, 40, 41**, where the table is above g by 3·10⁻⁶ to 2.5·10⁻⁵:
   at the table radius every orbit tested is finite and small (at most 16 400 points), and the
   origin's orbit reaches the cap only 7·10⁻⁵ to 3.7·10⁻⁴ above the table value (in r). So small finite
   orbits at the table radius are not special to n = 33.
4. **n = 80, 81 are different**: the origin's orbit is already large at g (1 269 847 and 478 881
   points, finite) and reaches the cap of 2·10⁷ within r − g ≈ 1·10⁻⁷, below the table's rounding.
   There the data agree with the table.
5. **Conclusion: undetermined.** For 31 ≤ n ≤ 41 the orbits that blow up near the table values are
   not among those tested, so failing to find them at g(33) does not show that the n = 33 entry is
   wrong. Neither do the data support it: no tested orbit is larger than 78 529 points within
   4.8·10⁻⁶ of g(33), and none reaches a cap within 1.37·10⁻⁵ of it. If the seeds used here were the
   relevant ones, the true r_c(33) would be about 1·10⁻⁵ or more above the table value; nothing here
   shows that they are.

## n = 33 at r = g and just above

`scan` at each radius; points already in a computed orbit are skipped.

| starting points | count | r² = g² | g² + 10⁻⁷ | g² + 10⁻⁶ | g² + 10⁻⁵ |
|---|---|---|---|---|---|
| signed sums of ≤ 4 roots of unity in the lens | 279 (265 orbits) | max 65 089 | 65 089 | 65 089 | 65 089 |
| signed sums of ≤ 5 roots of unity in the lens | 1 943 at g² (1 720 orbits), 1 944 at g² + 10⁻⁵ (1 721 orbits) | max 65 089 | – | – | 78 529 |
| generic points within 3·10⁻⁷ of a(0), b(0), the lens corners | 288 | max 32 577 | 65 089 | 65 089 | 65 089 |
| generic grid along the lens axis (spacing 1/1009) | 4 032 | max 46 465 | – | – | 77 889 |

The four-root sums are among the five-root sums, so the rows contain about 6 260 distinct starts.
The number of orbits depends on `--total-cap`, which limits how many computed points are recorded
for skipping later starts: with `--total-cap 5000000` the referee obtained 1 796 orbits from the
same 1 944 candidates at g² + 10⁻⁵, with the same maximum.

All are finite. At g the five-root sums give orbits of 129 to 65 089 points, with the sizes 2 112,
4 224, 8 448 and 10 560 the most frequent; the next largest after the origin's are 46 465, 34 241 and
26 881. The lens corners are not in ℚ(ζ₃₃) ([`engine.md`](engine.md)); generic points within
3·10⁻⁷ of them have orbits of at most 769 points.

## The thresholds above g

For the origin and the largest lens orbits, the sweep from r² = g² upward (`thresholds --from touch
--rc touch`) gives the exact radii at which the orbit grows, up to the cap:

| start (power-basis coefficients) | orbit at g | thresholds to the cap | last finite size | cap reached at r² − g² |
|---|---|---|---|---|
| origin | 65 089 | 1 | 65 089 | 1.20014·10⁻⁴ (cap 10⁸) |
| ζ²² − ζ²³ − ζ²⁷ + ζ²⁸ | 16 257 | 47 | 36 300 353 | 7.941·10⁻⁵ (cap 8·10⁷) |
| 0,0,−1,0,0,0,1,0,0,0,0,−1,1,−1,0,0,0,1,0,−1 | 46 465 | 5 | 18 057 213 | 2.843·10⁻⁵ (cap 6·10⁷) |
| −1,−1,0,1,−1,0,1,−1,−1,2,−1,0,0,−1,1,0,−1,1,0,−2 | 8 385 | 12 | 192 193 | 4.011·10⁻⁵ |
| −1,0,1,−1,0,1,−1,−1,2,0,0,0,−1,1,0,−2,1,0,−1,1 | 26 881 | 3 | 77 889 | 5.456·10⁻⁵ |
| 0,0,−1,0,0,0,0,1,0,0,0,0,0,−1,0,−1,1,0,1,−1 | 34 241 | 12 | 1 976 321 | 9.274·10⁻⁵ |
| −1,0,0,0,0,0,0,−1,0,1,0,−1,0,0,0,1,0,0,−1,−1 | 3 521 | 207 | 20 560 640 | 1.249·10⁻⁴ |
| −1,0,1,−1,1,1,−1,0,1,−1,0,0,−2,2,0,0,0,0,−1,1 | 24 065 | 4 | 39 745 | 1.495·10⁻⁴ |

The last six rows are the largest orbits of the five-root scan at g² + 10⁻⁵ (cap 6·10⁷; peak memory
9 GB). The orbit of the third row grows 46 465 → 53 313 → 101 697 → 110 529 → 18 057 213 → cap, at
r² − g² = 1.195, 2.412, 2.708, 2.836 and 2.843 (all ·10⁻⁵). The last two thresholds are only 7·10⁻⁸
apart while the orbit grows by more than a factor of 3. That looks like an accumulation of
thresholds just above g² + 2.84·10⁻⁵, but a finite sweep cannot show it.

The values are exact elements of ℤ[ζ₃₃]⁺; for the origin the next threshold is
`re:3541,-1398,-1726,2362,-780,-1122,1756,-544,-960,858`.

**No formula of the n ≡ 4 (mod 8) type.** For n ≡ 4 (mod 8) the origin's next threshold is one
trigonometric expression, r₁² = 1 + 8s² + 512s⁶(1 − s²), s = sin(π/n), for all n. For odd n the
corresponding values r₁² − g² of the origin are irregular:

| n | 25 | 27 | 29 | 31 | 33 | 35 | 37 | 39 | 41 | 43 | 45 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| orbit at g | 2 353 | 2 549 | 2 745 | 14 221 | 65 089 | 9 589 | 29 737 | 9 805 | 6 801 | 7 141 | 22 969 |
| r₁² − g² (10⁻⁵) | 72.8 | 111.8 | 31.4 | 17.9 | 12.0 | 26.3 | 18.9 | 10.8 | 2.81 | 6.74 | 5.87 |
| orbit at r₁ | 73 393 | ≥ 3·10⁶ | 9 913 | 77 101 | ≥ 3·10⁶ | 9 857 | 54 793 | 28 957 | 13 521 | ≥ 3·10⁶ | 38 809 |

They do not follow a smooth function of n, and the n ≡ 4 (mod 8) formula would give 3.8·10⁻⁴ for
n = 33. For these n the origin's orbit is not organised by a single second threshold.

## Other n

| n | g(n) | table − g | origin's orbit at g | origin reaches the cap at r − g | largest orbit tested at the table radius |
|---|---|---|---|---|---|
| 31 | 1.040134720 | 2.33·10⁻⁵ | 14 221 | 9.0·10⁻⁵ (2·10⁷) | 14 221 |
| 33 | 1.035512053 | −5·10⁻⁸ | 65 089 | 5.8·10⁻⁵ (10⁸) | 8 448 (r < g there) |
| 35 | 1.031640269 | 6.7·10⁻⁶ | 9 589 | 3.7·10⁻⁴ (2·10⁷) | 9 589 |
| 40 | 1.024327407 | 2.46·10⁻⁵ | 10 063 | 1.5·10⁻⁴ (2·10⁷) | 10 063 |
| 41 | 1.023170712 | 3.3·10⁻⁶ | 6 801 | 7.9·10⁻⁵ (2·10⁷) | 16 400 |
| 80 | 1.006146443 | −4·10⁻⁷ | 1 269 847 | 9.5·10⁻⁸ (2·10⁷) | 18 960 (r < g there) |
| 81 | 1.005996141 | −1·10⁻⁷ | 478 881 | 1.3·10⁻⁷ (2·10⁷) | 103 680 (r < g there) |

"Largest orbit tested" is over the signed sums of at most three roots of unity in the lens (4 to 23
orbits per n) at the table's radius. For n = 33, 80, 81 the table value is just below g, where the
origin's orbit still has 2n − 1 points.

For n = 31, 35, 40, 41 the table value lies strictly between g and the radius at which the origin's
orbit reaches the cap, and at the table value no tested orbit is large. The paper's computation must
therefore have used other seeds, or another criterion, for these n as well. For n = 80 and 81 the
origin's orbit itself reaches the cap within 1.3·10⁻⁷ of g, which is the table's value to rounding.

## Commands

All runs used the engine at commit 4dd9017, `B=.lake/build/bin/tdcsg-orbit`, one heavy run at a
time with `gtimeout` limits of 30 to 50 minutes (none was reached).

```sh
# lens sums at g² and above (OFF = "", +1e-7, +1e-6, +1e-5)
$B scan -n 33 --r2 touch$OFF --terms 4 --cap 3000000 --total-cap 25000000 --top 40
$B scan -n 33 --r2 touch$OFF --terms 5 --cap 3000000 --total-cap 20000000 --top 30   # OFF = "", +1e-5
# clouds near a(0), b(0) and the lens corners
$B scan -n 33 --r2 touch$OFF --near "b0;a0;xy:0,0.268859091;xy:0,-0.268859091;xy:0,0.2688;xy:0,0.268" \
   --scale 10000019 --spread 3 --cap 3000000 --total-cap 20000000 --top 30
# lens axis: 14 centres xy:0,y for y = ±0.02, ±0.06, …, ±0.26
$B scan -n 33 --r2 touch$OFF --near "xy:0,-0.26;xy:0,-0.22;…;xy:0,0.26" --scale 1009 --spread 8 \
   --cap 3000000 --total-cap 20000000 --top 30
# sweeps upward from g (the seven largest five-root orbits at g² + 10⁻⁵), peak 9 GB
$B thresholds -n 33 --start pow:… --from touch --cap 60000000 --rc touch --format lines
# other n: origin through g, and three-root lens sums at g and at the table value t²
$B thresholds -n N --from touch-1e-12 --cap 20000000 --rc touch --format lines
$B scan -n N --r2 touch --terms 3 --cap 3000000 --total-cap 15000000 --top 10
$B scan -n N --r2 t² --terms 3 --cap 3000000 --total-cap 15000000 --top 10
# first threshold above g for odd n = 25, …, 45
$B thresholds -n N --from touch-1e-12 --max-steps 2 --cap 3000000 --rc touch --format lines
```

## What would settle it

- **The paper's seeds and criterion.** Which starting point (or set of points) was followed, and
  whether the radius was found by bisection on the size of one orbit. With that, the exact engine
  can recompute the orbit at the table radius directly.
- **A seed search at the table radius for n = 31, 35, 40, 41**, where the table is known to be
  above g: finding the orbits that blow up there, and then the same family at g(33), would test the
  n = 33 entry on equal terms. The generic-point search that located seeds for n = 9
  ([`rank-conjecture.md`](rank-conjecture.md)) is the obvious tool; for n ≥ 30 it needs a finer grid
  in the thin lens and more memory than was used here.
- **A deeper engine.** Orbits of 10⁹–10¹⁰ points (the paper's scale) need the packed storage
  sketched in [`engine.md`](engine.md), "Possible next steps".
