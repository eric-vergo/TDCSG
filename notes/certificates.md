# Finiteness certificates from the exact engine

Authors: Eric Vergo, Claude

This note records the cut-set certificates of finiteness computed by the Lean engine
(`tdcsg-orbit certify` and `tdcsg-orbit check-certificate`, see [`engine.md`](engine.md)), their
agreement with the earlier Python computations, how far toward r_c each n was pushed, and what
exactly is established.

## 1. The statement being certified

Fix n and r > 1, and let D_L, D_R be the closed disks of radius r about −1 and 1. The certificate
theorem (Theorem 4.2 of [`proofs/critical-radius-n5.md`](proofs/critical-radius-n5.md), restated as
Theorem 3.1 of [`proofs/critical-radius-n8.md`](proofs/critical-radius-n8.md); refereed) says: if a
finite union K of non-degenerate closed arcs of circles of radius r satisfies

- **(C1)** ∂D_L ∪ ∂D_R ⊆ K;
- **(C2)** A^{±1}(K ∩ D_L) ⊆ K and B^{±1}(K ∩ D_R) ⊆ K;
- **(C3)** no circle carrying an arc of K, other than ∂D_p, is tangent to ∂D_p;
- **(C4)** every endpoint of a maximal arc of K lying on ∂D_p belongs to an arc entering int D_p
  there,

then GG_n(r) is finite, and by the refereed group monotonicity so is GG_n(r') for every r' ≤ r.
In Lean, `TDCSG/CriticalRadius/Certificate.lean` defines `TDCSG.Arc` (a centre and two angles
θ₁ < θ₂ ≤ θ₁ + 2π), `TDCSG.Certificate n r arcs` (non-degeneracy and (C1)–(C4) for the union of
`arcs`, with (C4) in a local form), the theorem as the proposition `TDCSG.CutSetCertificate n`
(stated, **not proved** in Lean), and proves the reduction `TDCSG.finite_GG_of_certificate`:
the theorem plus `TDCSG.ExistsCertificate n r₀` give finiteness for all r ≤ r₀.

The natural candidate for K is the cut set K(r), the closure of ∂D_L ∪ ∂D_R under a^{±1}, b^{±1}.
`certify` computes it; when the closure terminates, no carrying circle is tangent to a boundary
circle, and (C4) holds, it writes K(r) as a certificate file.

## 2. The programs

**Generator** (`TDCSGCompute/Closure.lean`). Circles are their centres c ∈ ℤ[ζ_n]; an arc is a pair
of endpoint symbols (e, ±), "the intersection point of the circle about c with the circle about e
on side ±", run counterclockwise. Starting from the two full boundary circles, every new piece is
clipped to the windows C(c) ∩ D_p (from (p, −) to (p, +)), rotated by ζ^{±1} about p, and the parts
of the images not yet covered are added and merged with the arcs they touch. The run stops when
nothing new appears (*closed*) or at a cap (*nothing claimed*). Tangency of a new circle to ∂D_p is
decided exactly and stops the run (*not certified*).

**Exact order of endpoints.** This is the one geometric decision, and it is exact:

1. The point (e, s) on the circle about c, with d = e − c, N = |d|², r² = R/q, has the direction
   U = d(qN + is√H), H = qN(4R − qN) > 0 (U is a positive multiple of the point minus c).
2. With ω = ζ − ζ⁻¹ and S₄ = −ω² = 4sin²(2π/n), the real numbers X = 2√S₄ Re U and Y = 2√S₄ Im U
   are X = √S₄·qN·A(d) − sT(d)√H and Y = qN·T(d) + sA(d)√S₄√H, where A(d) = d + d̄ and
   T(d) = −(d − d̄)ω lie in ℤ[ζ_n]⁺. So X, Y lie in the tower ℚ(ζ_n)⁺(√S₄, √H).
3. The half of a point (angle in [0, π) or [π, 2π)) is the sign of Y, or of X when Y = 0. Two points
   in the same half are ordered by the sign of X₁Y₂ − Y₁X₂ ∈ ℚ(ζ_n)⁺(√S₄, √H₁, √H₂), and are equal
   exactly when it is 0. Points in different halves are distinct.
4. A sign in a tower is decided by recursive squaring: for x = P + Q√r with r > 0, the sign is that
   of P or Q when the other is 0 or they agree, and otherwise sign(P)·sign(P² − rQ²). This descends
   to signs in ℚ(ζ_n)⁺. For n = 5, 8, 10, 12 those are integer comparisons
   (4x = u + v√D with u, v ∈ ℤ); in general they are exact zero tests followed by certified ball
   evaluation, which terminates for a nonzero algebraic integer.
5. Before the exact sign, two cheaper certified tests are tried: an enclosure of X, Y and the cross
   product in fixed-point integer ball arithmetic (no floating point), and, in the generator only, a
   double-precision evaluation with running error bounds (IEEE 754 correct rounding of +, −, ×, /
   and √ assumed). Either decides only when its enclosure excludes 0, and then gives the exact sign.

Consequently equality of endpoints is decided exactly, also between different symbols (three
circles through one point), and so is their cyclic order. The arguments are written out in the
module docstrings of `CirclePoint.lean`, `Tower.lean` and `CircleFilter.lean`.

**Checker** (`TDCSGCompute/CertCheck.lean`). It reads only the certificate file and verifies:
the radius is real with r > 1; every symbol names a point of its circle (the two circles cross);
each circle is listed either as full or by arcs; on each circle the arcs are non-degenerate,
pairwise disjoint and do not touch (so they are the maximal arcs); (C1) both boundary circles are
full; (C2) for every arc α, every p = ±1 whose disk meets the circle, and k = ±1, each part of α ∩ D_p
rotated by ζ^k about p lies inside one listed arc of the image circle (or that circle is full);
(C3) 4r² − |c − p|² ≠ 0 for every centre c ≠ p; (C4) every endpoint equal to (p, −) starts its arc
and every endpoint equal to (p, +) ends it; and the summary counts. It shares with the generator
only the exact layer (`Field`, `Ball`, `Tower`, `CirclePoint`: arithmetic in ℤ[ζ_n], signs, the
order of points, tangency signs, the rotations). Parsing, clipping, containment, maximality and the
(C1)–(C4) logic are separate code, and the checker uses no floating point at all.

**Relation to `TDCSG.Certificate`.** An `arc` record on centre c is the `TDCSG.Arc` with centre the
complex value of c, θ₁ the angle of its initial point and θ₂ = θ₁ + (counterclockwise angle to the
final point); a `full` record has θ₂ = θ₁ + 2π. With r = √(r²) the checks above are the conjuncts of
`TDCSG.Certificate n r arcs`: non-degeneracy, (C1), (C2) for `permA`, `permA⁻¹`, `permB`, `permB⁻¹`
(the rotations by ζ^{∓1} on the closed disks, the identity elsewhere), (C3) as `dist c p ≠ 2r`, and
(C4) in the local form of the Lean statement (an arc that starts at (p, −) or ends at (p, +) runs
into D_p, and an interior point of an arc on ∂D_p is a crossing). This correspondence is by
inspection of the definitions.

## 3. The certificate format

A line-oriented UTF-8 text file. Blank lines and lines starting with `#` are ignored.

```
tdcsg-certificate 1
n 5
r2 2,0,-5,-5 / 5
full -1,0,0,0
arc -5,-2,-2,-2 -1,0,0,0 - -3,-2,-2,-2 +
…
summary circles 54 arcs 64 c4-endpoints 60
end
```

- Vectors are integer coefficients in the power basis 1, ζ, …, ζ^{φ(n)−1} of ℤ[ζ_n], ζ = e^{2πi/n},
  separated by commas (for n = 5: x₀ + x₁ζ + x₂ζ² + x₃ζ³, reduced by ζ⁴ = −1 − ζ − ζ² − ζ³).
- `r2 v / q`: r² = v/q with v real (here 3 + φ − 13/5 = (2 − 5ζ² − 5ζ³)/5).
- `full c`: the whole circle of radius r about c.
- `arc c e₁ s₁ e₂ s₂`: the arc of the circle about c from the point (e₁, s₁) counterclockwise to the
  point (e₂, s₂). The point (e, s), s ∈ {+, −}, is c + (d/2)(1 + i s h) with d = e − c and
  h = √(4r²/|d|² − 1): the intersection with the circle about e on side s.
- `summary`: the number of circles, of maximal arcs (full circles included) and of arc endpoints
  lying on a boundary circle.
- `end`: required, so that a truncated file is rejected.

The generator writes circles in lexicographic order of their centres and arcs by the angle of their
initial point, so the file is a deterministic function of (n, r²).

## 4. Reproduction of the Python results

Every run below closed, had no tangency and no (C4) failure, and its certificate was accepted by the
checker with the same counts. In none of them was the exact tower sign needed: every comparison was
decided by the float filter, and no two different symbols named the same point. "Pieces" is the
number of stored arcs before merging; it depends on the processing order, but the generator, like
the Python programs, processes its work list last in, first out, and the piece counts agree exactly
with the referee's n = 5 program and the author's n = 8, 12 program.

### n = 5, r² = 3 + φ − δ (Table 5.1 of `critical-radius-n5.md`)

| δ | r | circles | maximal arcs | pieces | (C4) endpoints | max\|σ(c)\| | Python | file | generator / checker time |
|---|---|---|---|---|---|---|---|---|---|
| 13/5 | 1.42058 | 54 | 64 | 112 | 60 | 7.3 | identical arcs | 2.6 kB | < 0.01 s / 0.02 s |
| 1/2 | 2.02929 | 1 398 | 3 074 | 8 749 | 704 | 31.8 | identical arcs | 118 kB | 0.05 s / 0.9 s |
| 9/10 | 1.92822 | 466 | 952 | 2 040 | 316 | 18.2 | identical arcs | 35 kB | 0.01 s / 0.3 s |
| 9/20 | 2.04158 | 1 722 | 4 222 | 10 301 | 864 | 37.6 | identical arcs | 164 kB | 0.06 s / 1.3 s |
| 3/10 | 2.07799 | 5 044 | 13 138 | 35 665 | 1 696 | 57.6 | identical arcs | 546 kB | 0.2 s / 4 s |
| 1/5 | 2.10191 | 11 606 | 35 194 | 185 539 | 2 964 | 89.1 | identical arcs | 1.5 MB | 1.1 s / 11 s |
| 3/20 | 2.11377 | 30 776 | 87 922 | 496 587 | 4 420 | 156.4 | identical arcs | 4.0 MB | 3.4 s / 29 s |
| 1/10 | 2.12557 | **50 714** | **198 470** | **1 437 580** | 7 172 | 188.3 | identical arcs | 9.3 MB | 11 s / 64 s |

"Identical arcs" means: the set of (centre, initial symbol, final symbol) triples of our certificate
equals the referee's merged output (`ref4/mine_*.json`) exactly, and at δ = 1/10 also the author's
merged output; compared in a scratch script, not part of the repository. All counts agree with
Table 5.1 and the referee report (circles, maximal arcs, (C4) endpoints, max|σ(c)|), and the piece
counts with the referee's (the author's are 2 higher from δ = 9/20 on, as the note explains). The
row δ = 1/2, absent from Table 5.1, agrees with the referee's 1 398 circles and 3 074 arcs.

### n = 8, r² = 10 − 5√2 − δ (Table 3.1 of `critical-radius-n8.md`)

| δ | r | circles | maximal arcs | pieces | (C4) endpoints | max\|σ(c)\| | Python | file | times |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1.38886 | 52 | 84 | 140 | 80 | 6.2 | agrees | 3.3 kB | < 0.01 s / 0.02 s |
| 1/2 | 1.55850 | 726 | 1 920 | 8 563 | 676 | 20.6 | agrees | 71 kB | 0.04 s / 0.5 s |
| 1/3 | 1.61109 | 3 648 | 10 824 | 49 425 | 1 420 | 46.1 | agrees | 427 kB | 0.3 s / 3 s |
| 1/5 | 1.65195 | 4 222 | 18 780 | 143 703 | 2 920 | 47.6 | agrees | 738 kB | 0.9 s / 5 s |
| 1/6 | 1.66201 | 5 024 | 22 258 | 184 459 | 3 176 | 51.1 | agrees | 884 kB | 1.2 s / 6 s |
| 1/7 | 1.66915 | **24 150** | **122 762** | 824 763 | 5 692 | 110.4 | agrees | 5.4 MB | 7 s / 36 s |
| 1/10 | 1.68194 | 30 490 | 213 418 | 2 004 896 | 10 328 | 122.8 | agrees | 9.5 MB | 22 s / 63 s |
| 1/12 | 1.68689 | 31 366 | 229 058 | 2 357 437 | 11 252 | 124.6 | agrees | 10.3 MB | 29 s / 67 s |

"Agrees" means: circles, maximal arcs and (C4) endpoints equal Table 3.1 of the note and the
referee's table, and the pieces equal those of the note's first version (the current table no
longer lists pieces). In that first version the author's run at δ = 1/10 stopped at its cap of
2·10⁶ pieces with 30 490 circles; the closure needs 2 004 896 pieces, just over that cap. The rows
1/10 and 1/12 were then closed by the referee in floating point and later by the author exactly,
with the same counts as here. The note's "(C2) image
arcs checked" column counts 4 more than our checker at every δ (for example 4 548 against 4 544 at
1/2): the four images of the two boundary circles about their own centres, which the checker skips
because they lie on those circles.

### n = 12, r² = 40 − 22√3 − δ (Table 3.1 of `critical-radius-n12.md`)

| δ | r | circles | maximal arcs | pieces | (C4) endpoints | max\|σ(c)\| | Python | file | times |
|---|---|---|---|---|---|---|---|---|---|
| 1/3 | 1.24962 | 282 | 556 | 2 003 | 368 | 13.5 | agrees | 20 kB | 0.01 s / 0.14 s |
| 1/5 | 1.30188 | 2 324 | 6 016 | 30 709 | 1 000 | 37.1 | agrees | 238 kB | 0.14 s / 1.6 s |
| 1/10 | 1.33973 | 2 360 | 6 192 | 38 579 | 1 032 | 37.5 | agrees | 246 kB | 0.2 s / 1.6 s |
| 1/20 | 1.35826 | **37 180** | **114 380** | 926 755 | 3 928 | 137.5 | agrees | 5.3 MB | 6 s / 32 s |
| 1/30 | 1.36439 | 37 840 | 157 924 | 1 237 209 | 4 804 | 137.5 | agrees | 7.3 MB | 9 s / 45 s |

The row δ = 1/30 was closed by the referee in floating point and later by the author exactly, with
the same circles, maximal arcs and (C4) endpoints. Pieces are compared with the note's first version
(δ ≥ 1/20).

**Disagreements.** None in any count that is an invariant of K(r). The only differences are in
implementation-dependent counts, explained above (two degenerate pieces of the n = 5 author's
program; four boundary self-images in the n = 8, 12 "(C2) image arcs" column), and one rounding:
for n = 8, δ = 1/2, max|σ(c)| is 20.647, which Table 3.1 of the n = 8 note gives as 20.7 and the
referee as 20.6.

## 5. Toward r_c

All runs below closed with no tangency and no (C4) failure, and every certificate listed was
accepted by the checker with the generator's counts. Again the exact tower sign was never needed and
no two different symbols named the same point. Times are wall-clock on the development machine
(Apple M2 Ultra), one core per run, with up to seven runs in parallel; memory is peak resident size.
"Gen." is `certify`, "check" is `check-certificate`. The runs used the engine at commits `c7075c4`
and `a4e4d05`, which differ only in the speed and memory of the exact layer and of the checker's
parser; certificates produced by both are byte-identical. The checker figures for n = 5, δ = 1/30
are those of `c7075c4`, which keeps more data per point.

### n = 5, r² = 3 + φ − δ (r_c ≈ 2.148961)

| δ | r | r_c − r | circles | maximal arcs | pieces | (C4) endpoints | max\|σ(c)\| | gen. | check | file |
|---|---|---|---|---|---|---|---|---|---|---|
| 1/10 | 2.125567 | 0.023394 | 50 714 | 198 470 | 1 437 580 | 7 172 | 188.3 | 11 s, 0.13 GB | 64 s, 0.35 GB | 9.3 MB |
| 3/40 | 2.131439 | 0.017522 | 105 406 | 352 790 | 2 828 298 | 9 836 | 309.6 | 26 s, 0.23 GB | 126 s, 0.67 GB | 17 MB |
| 1/20 | 2.137296 | 0.011665 | 190 436 | 833 366 | 7 795 006 | 15 376 | 363.7 | 80 s, 0.54 GB | 287 s, 1.6 GB | 41 MB |
| 1/30 | 2.141191 | 0.007770 | 722 196 | 3 372 640 | 31 153 889 | 26 200 | 738.8 | 334 s, 2.0 GB | 1 246 s, 6.8 GB | 181 MB |
| 1/40 | 2.143136 | 0.005825 | 996 924 | 6 351 150 | 74 922 890 | 42 776 | 844.7 | 922 s, 4.0 GB | 2 383 s, 5.1 GB | 346 MB |
| 1/50 | 2.144303 | 0.004658 | 1 052 720 | 7 632 516 | 103 776 163 | 53 316 | 844.7 | 1 362 s, 4.5 GB | 2 819 s, 6.1 GB | 417 MB |
| 1/55 | 2.144727 | 0.004235 | 2 190 188 | 11 861 876 | 128 337 348 | 59 668 | 1 407.2 | 1 850 s, 7.6 GB | 4 626 s, 9.6 GB | 662 MB |

The Python programs stopped at δ = 3/40 and 1/20 at their cap of 10⁶ pieces; the exact closure
needs 2.8·10⁶ and 7.8·10⁶.

### n = 8, r² = 10 − 5√2 − δ (r_c ≈ 1.711412)

| δ | r | r_c − r | circles | maximal arcs | pieces | (C4) endpoints | max\|σ(c)\| | gen. | check | file |
|---|---|---|---|---|---|---|---|---|---|---|
| 1/13 | 1.688789 | 0.022623 | 33 690 | 259 266 | 2 491 574 | 11 824 | 138.1 | 32 s, 0.17 GB | 77 s, 0.45 GB | 12 MB |
| 1/14 | 1.690415 | 0.020997 | 36 024 | 291 418 | 3 089 741 | 13 320 | 138.1 | 42 s, 0.19 GB | 87 s, 0.51 GB | 13 MB |
| 1/16 | 1.693054 | 0.018358 | 129 380 | 882 710 | 6 750 066 | 17 012 | 262.5 | 102 s, 0.56 GB | 278 s, 1.6 GB | 41 MB |
| 1/20 | 1.696742 | 0.014671 | 174 540 | 1 921 458 | 31 764 931 | 35 216 | 288.5 | 548 s, 1.2 GB | 607 s, 1.5 GB | 92 MB |
| 1/25 | 1.699686 | 0.011726 | 175 126 | 2 350 150 | 45 926 270 | 46 512 | 288.5 | 939 s, 1.4 GB | 776 s, 1.9 GB | 112 MB |
| 1/30 | 1.701646 | 0.009766 | 240 482 | 3 431 610 | 62 674 340 | 62 548 | 354.2 | 1 458 s, 2.1 GB | 1 129 s, 2.6 GB | 165 MB |
| 1/36 | 1.703278 | 0.008135 | 582 886 | 6 474 082 | 96 611 862 | 82 624 | 567.6 | 2 526 s, 4.2 GB | 2 065 s, 5.1 GB | 324 MB |

The rows δ = 1/13, 1/14 agree with the newer rows of Table 3.1 of `critical-radius-n8.md`
(circles, maximal arcs, (C4) endpoints); there the author's run at 1/16 stopped at its cap with
124 752 circles.

### n = 12, r² = 40 − 22√3 − δ (r_c ≈ 1.376547)

| δ | r | r_c − r | circles | maximal arcs | pieces | (C4) endpoints | max\|σ(c)\| | gen. | check | file |
|---|---|---|---|---|---|---|---|---|---|---|
| 1/40 | 1.367436 | 0.009111 | 38 016 | 162 960 | 1 714 619 | 6 420 | 137.5 | 15 s, 0.12 GB | 47 s, 0.31 GB | 7.5 MB |
| 1/50 | 1.369263 | 0.007284 | 83 674 | 335 412 | 3 301 520 | 9 444 | 266.8 | 33 s, 0.22 GB | 102 s, 0.64 GB | 16 MB |
| 1/60 | 1.370480 | 0.006067 | 470 284 | 1 354 760 | 9 242 698 | 14 120 | 539.1 | 87 s, 0.91 GB | 431 s, 1.2 GB | 70 MB |
| 1/80 | 1.371999 | 0.004548 | 527 982 | 2 167 972 | 24 753 329 | 20 340 | 539.1 | 256 s, 1.5 GB | 689 s, 1.8 GB | 115 MB |
| 1/100 | 1.372910 | 0.003637 | 533 886 | 2 582 028 | 41 534 986 | 25 224 | 539.1 | 462 s, 1.7 GB | 823 s, 2.1 GB | 137 MB |
| 1/150 | 1.374124 | 0.002424 | 570 008 | 3 528 064 | 89 610 412 | 38 140 | 539.1 | 1 165 s, 2.6 GB | 1 158 s, 2.9 GB | 189 MB |
| 1/180 | 1.374528 | 0.002019 | 1 076 158 | 5 937 136 | 103 993 897 | 42 136 | 915.6 | 1 435 s, 4.1 GB | 1 908 s, 4.8 GB | 324 MB |

The rows δ = 1/40, 1/50 agree with the newer rows of Table 3.1 of `critical-radius-n12.md`; there
the author's run at 1/60 was stopped at more than 3.2·10⁵ circles.

### n = 10, r² = 4 − φ − δ (r_c ≈ 1.543362)

Table 4.1 of [`proofs/critical-radius-n10.md`](proofs/critical-radius-n10.md) (exact Python
closure, reproduced by its referee) lists δ = 1/2, 1/3, 1/5, 1/7, 1/10, 1/14, 1/16; every one of its
circle, piece, maximal-arc and (C4) counts agrees with ours, and its (C2) image counts are again 4
higher (598 244 against 598 240 at 1/16).

| δ | r | r_c − r | circles | maximal arcs | pieces | (C4) endpoints | max\|σ(c)\| | gen. | check | file |
|---|---|---|---|---|---|---|---|---|---|---|
| 1/2 | 1.371848 | 0.171514 | 318 | 678 | 4 056 | 432 | 12.7 | 0.02 s | 0.2 s | 25 kB |
| 1/3 | 1.431305 | 0.112057 | 988 | 2 322 | 9 895 | 632 | 23.5 | 0.06 s | 0.7 s | 87 kB |
| 1/5 | 1.477148 | 0.066214 | 5 986 | 19 388 | 176 617 | 1 816 | 51.0 | 1.1 s | 5.5 s | 0.8 MB |
| 1/7 | 1.496365 | 0.046997 | 6 058 | 24 000 | 290 916 | 2 252 | 51.0 | 2.1 s | 6.8 s | 1.0 MB |
| 1/10 | 1.510618 | 0.032744 | 11 722 | 47 128 | 530 151 | 3 112 | 79.9 | 4.5 s | 14 s | 2.0 MB |
| 1/14 | 1.520045 | 0.023317 | 33 040 | 205 320 | 2 718 214 | 9 448 | 117.2 | 33 s, 0.14 GB | 61 s, 0.16 GB | 9.2 MB |
| 1/16 | 1.522979 | 0.020383 | 33 364 | 260 176 | 3 901 930 | 11 792 | 117.2 | 43 s, 0.18 GB | 72 s, 0.21 GB | 12 MB |
| 1/20 | 1.527078 | 0.016284 | 114 888 | 689 072 | 12 789 337 | 16 884 | 217.0 | 168 s, 0.45 GB | 221 s, 1.3 GB | 33 MB |
| 3/100 | 1.533612 | 0.009750 | 144 882 | 1 453 954 | 54 835 671 | 31 572 | 245.0 | 1 058 s, 0.94 GB | 486 s, 1.1 GB | 70 MB |
| 1/40 | 1.535241 | 0.008121 | 203 874 | 2 169 434 | 79 890 589 | 38 596 | 328.4 | 1 737 s, 1.4 GB | 716 s, 1.7 GB | 106 MB |
| 1/47 | 1.536454 | 0.006908 | 418 510 | 3 936 494 | 105 364 502 | 43 768 | 449.7 | 2 564 s, 2.5 GB | 1 313 s, 3.1 GB | 197 MB |

One count disagrees with that note, and it is not an exact count there: at δ = 1/20 the note
reports a floating-point closure (arcs stored as float angle intervals and merged numerically) with
114 888 circles, as here, and 689 665 merged arcs, against 689 072 exact maximal arcs here. The
exact count is the one the checker verifies (disjoint, non-touching arcs); the excess of 593 is
consistent with touching arcs left unmerged by a numerical merge, but that explanation was not
checked.

### Size growth and the best certified radius

The size of K(r) grows in steps as δ decreases, not smoothly: for n = 12 the circle count is almost
unchanged from 1/20 to 1/40 (37 180, 37 840, 38 016) and from 1/60 to 1/100 (470 284 to 533 886),
with large jumps in between, and similarly for n = 8 between 1/20 and 1/25. The steps are consistent
with one per renormalization level (a factor of the unit in δ). Both programs scale about linearly
with the size of the certificate: the generator processes 0.4–1.3·10⁵ pieces per second and needs
about 0.65 kB per maximal arc; the checker needs 0.3–0.4 ms and about 0.8 kB per maximal arc. The
limit is memory. For n = 5 the orbit data of [`engine.md`](engine.md) show the next large jump just
below δ = 0.0181; if the cut set jumps there too, the next level would need several times the
7.6 GB of δ = 1/55, beyond the 24 GB allowed for these runs, so it was not attempted.

**Best certified radius per n.** r_*² = r_c² − δ_* is the deepest radius certified by both
programs; by group monotonicity GG_n(r) is then finite for every r ≤ r_* (subject to §7).

| n | r_c² | r_c | δ_* | r_* | r_c − r_* | best in the notes (Python, exact) |
|---|---|---|---|---|---|---|
| 5 | 3 + φ | 2.148961 | 1/55 | 2.144727 | 0.004235 | δ = 1/10, r_c − r = 0.023394 |
| 8 | 10 − 5√2 | 1.711412 | 1/36 | 1.703278 | 0.008135 | δ = 1/14, r_c − r = 0.020997 |
| 10 | 4 − φ | 1.543362 | 1/47 | 1.536454 | 0.006908 | δ = 1/16, r_c − r = 0.020383 |
| 12 | 40 − 22√3 | 1.376547 | 1/180 | 1.374528 | 0.002019 | δ = 1/50, r_c − r = 0.007284 |

The remaining gap is open in every case: no single computation reaches r_c, and the window
(r_*, r_c) needs the renormalization argument of the notes. A symmetry-reduced window-free closure
(`certify-relative --window 0 --symmetric`, checked with (C1)–(C4) by
`check-relative-certificate`) certifies n = 8 at δ = 547/25000 ≈ 0.02188
(r_c − r_* ≈ 0.006404), and exact intervals of validity extend the n = 10 and n = 12 rows slightly;
see [`relative-certificates.md`](relative-certificates.md) §§7, 8, 10.

## 6. Committed certificates and checksums

The small certificates are in [`../certificates/`](../certificates/); the others were written to a
scratch directory and are recorded by SHA-256 (of the file exactly as written by `certify`). Each is
reproduced exactly (the output is deterministic) by

```sh
tdcsg-orbit certify -n N --r2 closed-δ --max-pieces 400000000 --max-circles 20000000 --out FILE
tdcsg-orbit check-certificate FILE
```

with `δ` as in the tables (for example `closed-1/55`). The default caps (10⁷ pieces, 5·10⁶
circles) suffice only for the rows with fewer than 10⁷ pieces; a run that reaches a cap says so
and names the flags to raise.

Committed (checked by `shasum -a 256 -c certificates/SHA256SUMS`): n = 5 at δ = 13/5, 9/10, 1/2;
n = 8 at δ = 1, 1/2; n = 12 at δ = 1/3; n = 6 at r² = 3.7 (18 circles); and two relative
certificates at r_c in symmetric storage (format of
[`relative-certificates.md`](relative-certificates.md) §4, checked by
`check-relative-certificate`): `n5-rc-w0_2_-1_0.rcert` (n = 5, window shape 0,2,-1,0) and
`n12-rc-w-6_5_1_-4.rcert` (n = 12, window shape -6,5,1,-4).

All certificates of §§4–5 (n, δ, maximal arcs, size in bytes, SHA-256):

| n | δ | maximal arcs | bytes | SHA-256 |
|---|---|---|---|---|
| 5 | 13/5 | 64 | 2591 | `07e25af9e313197deb750e676ca8aa3d38d2691f56b3929c38465ab575f3c003` |
| 5 | 9/10 | 952 | 35473 | `20570d4a84face48ce0c538fae07ee19b1079d28637a435462875d47a8d96bcc` |
| 5 | 1/2 | 3074 | 118470 | `ac2ebab3f119a1c3ce94d8719d5171d1abe64fd63e320a898f7ed4a2af1e2988` |
| 5 | 9/20 | 4222 | 163682 | `4c492c0887c9be29330a604deb6a8de7102e29c4cef26f482540f544a922583b` |
| 5 | 3/10 | 13138 | 545817 | `f83bf848ec12d0457861614b1cc56cf1f4e6fa826218382c5eeaa497b07a3744` |
| 5 | 1/5 | 35194 | 1541639 | `10e47668fa07ec8cbc3d0fbf572daeaf26eb02eb8d5a89ae2974af7c9c3ee4e8` |
| 5 | 3/20 | 87922 | 4035171 | `8fe83ca10d673cb0145ba068f3e5f84d25d2b9cd61e57aa60a41e4ef5f7c7a58` |
| 5 | 1/10 | 198470 | 9253704 | `72c31089e32d8c1cd99ce02058bac15a8512b1f6879f9bbcb765882a22538340` |
| 5 | 3/40 | 352790 | 16921905 | `aa0c358a9f544b596817f4cdf8251469d1546fb533df64c4b2c087ed5fe3fefd` |
| 5 | 1/20 | 833366 | 41394081 | `299483c81fe3a5b744bbe8b2d3d91d3b859a89c69ca3b77efadba06e2e96524e` |
| 5 | 1/30 | 3372640 | 181183000 | `bffc3d48766ec938007883c9d35daac2015dc35a2a05b9c28f391d2f1b59e11d` |
| 5 | 1/40 | 6351150 | 345738870 | `a8ece3456d5c91fdef1934c13b0e7f4670b16da4ff940378a00811aad79c1065` |
| 5 | 1/50 | 7632516 | 416890412 | `dc9ce2da1af8cee6fb21f6498bb3ec869f42e6a09ae386eba6744e64529fbb0a` |
| 5 | 1/55 | 11861876 | 661622894 | `3682098ae898f2e50c8274d0025ece474e8542a118e5ce78218eebf04ac60082` |
| 8 | 1 | 84 | 3253 | `6cd36cf516d755e8a2cfc244a0830294072026135a3c9ba5f063d52ce123e188` |
| 8 | 1/2 | 1920 | 70818 | `e9588705f1561fc6505a38f2ddb18e4fc09e160bb2f3aeac88295cebc6974587` |
| 8 | 1/3 | 10824 | 426847 | `99e64e079d8500efca160e1d93ac23555a306b79448bad4a7370329f3766134e` |
| 8 | 1/5 | 18780 | 738157 | `2f6aa56ba73f360acedf4a5868f104c4899339eccf91121abca62c3d873104ba` |
| 8 | 1/6 | 22258 | 884188 | `c52d0869cd73bbe6e1897b4a607099f7c6ea068e8875394e26ff0fd08708092d` |
| 8 | 1/7 | 122762 | 5438382 | `e177b1ba175b94ca2e754e8416487cb1b29f2fd68f61e7d03c9ea5a543288fe1` |
| 8 | 1/10 | 213418 | 9537245 | `253e3b3410ac35ac22c9f49d8514c397aa96030f032896f695a1fc1eaee01030` |
| 8 | 1/12 | 229058 | 10291174 | `76e09ab1615a826e33447044a2c44f825880cfaa6f2cf7474a989809d039bf9c` |
| 8 | 1/13 | 259266 | 11682354 | `0108c73c0cc3e7d10a3d67e171edf2799d996156b5f65e4cf145f8773de79672` |
| 8 | 1/14 | 291418 | 13175176 | `c6384edbf40cd235a0a17695f8ebddac9dc0cfe6a4670dfea94f13318b0cab7a` |
| 8 | 1/16 | 882710 | 41461381 | `72ee52fb7cd3210164badfa2008b4f79dceb1bb7f1be993b38070f2d0d1b5fb4` |
| 8 | 1/20 | 1921458 | 91593796 | `7e0e16eef7d3c7019b33be417bbefb096520a2c5fa5778011ba945aa8aa0f728` |
| 8 | 1/25 | 2350150 | 112044358 | `91572706996f1be40b0d5a7f1b8930d8cd7c6157f120af65b2121fb99c63f8bf` |
| 8 | 1/30 | 3431610 | 165154874 | `154715187211e7ade6592fc257e431969447dc206a7e57920b9432184288ab3f` |
| 8 | 1/36 | 6474082 | 323722644 | `7d21caacb2399a8dab246c4f7888526a31497015165ccda43efe44300e523352` |
| 10 | 1/2 | 678 | 24728 | `57e006df089d9c9720670fa40903030d37671d245ea929017c4a101cc9e14f99` |
| 10 | 1/3 | 2322 | 86588 | `258a26bfa49064333720b5e53206f8a0bab1ae697dd3e5d12786ee429db2e48c` |
| 10 | 1/5 | 19388 | 819154 | `988085b85a612900b80d8d547f0d567cbc1b337e38b0327e7c196d7bd90c9fdc` |
| 10 | 1/7 | 24000 | 1012489 | `a3ac01be07ea46b4d27774a7dcf0be960bb21896b69d557b619f0e29de67d1b3` |
| 10 | 1/10 | 47128 | 2032164 | `1862bd39d72d52d5f25c45166c240d5dd40e221e73a8feeff910eacc12b857fe` |
| 10 | 1/14 | 205320 | 9222916 | `91681b4e4fdb8f76968ffd88fd5a4d586a8bcfe01c07cf2bbf2c52198f38aebc` |
| 10 | 1/16 | 260176 | 11739330 | `a1571a4b136f5d5a59699839b74af12eec71339ddfa62f0b7b51f7acacb7fdb1` |
| 10 | 1/20 | 689072 | 32591803 | `074358575f58c4f3c66edfaa79dc8b15d515c1f30658fbe3e44f8152a31bb1b4` |
| 10 | 3/100 | 1453954 | 69775831 | `4a7063345f10a8cccbfce3525dee6562c6d5c1fe49ad000b2f7f0fe7eb351c7a` |
| 10 | 1/40 | 2169434 | 105619656 | `c63a069880b20bdf14838ca33d31ab35046936f4a783477057695305822c9398` |
| 10 | 1/47 | 3936494 | 196650832 | `cbc0cceb3aab719424a7266df8cb7989fb95c43fc33b3eeabf29110c5b8cd0cc` |
| 12 | 1/3 | 556 | 20376 | `ffa3743aac348a3d4392e32c911b8f161f52988bc90a4c7c5a5cb7fd67f986fb` |
| 12 | 1/5 | 6016 | 238179 | `a228093b3b136a684780ed41e9929e22b2510ca6eca74d87b79b51a99701a8aa` |
| 12 | 1/10 | 6192 | 245551 | `1652fab3ee629d8fc78dd1b082a36f16f3e30b04c108a2ef99cc38b4bdf7b3e2` |
| 12 | 1/20 | 114380 | 5288590 | `acbe47f00c6517087b45ceaf2b7b34f67a17ef007129d6c9810f735a201e339b` |
| 12 | 1/30 | 157924 | 7343657 | `a25827b46109c1f1c03b3486c14a46de04c6c99aabca7c54bf402a5e7165175b` |
| 12 | 1/40 | 162960 | 7545683 | `e2194f7649eb1ef633c203dfecb1932bdb91e2f9b724e6f5301ee7ee2be37a26` |
| 12 | 1/50 | 335412 | 15781939 | `acf8c62596b8f09a8308eeec5f4a9ef5c619ae315e9cee0f1d9d42380d144584` |
| 12 | 1/60 | 1354760 | 70481652 | `d8e31c821301f7574ff4b7dbcc0bfb5ab4bc21c94a6d5f9110955948ad3700a1` |
| 12 | 1/80 | 2167972 | 114722246 | `fa32d3a4b98fd7fb0a25a22bcaedb4dc6b66c4c025605883ba37cc99a74a7863` |
| 12 | 1/100 | 2582028 | 136682118 | `3b3613c8ece9edb8f76fc517b73abe60a8f39670ee5829dbf9a619c6a66ab6de` |
| 12 | 1/150 | 3528064 | 188565409 | `712cd146d81c16b464c2772ad93229a475449587ef450476a784883cbb96acd6` |
| 12 | 1/180 | 5937136 | 323794654 | `014d04ac8d566244bb13b2f6fbe1187dfac29efcf3e78adab47ca831e209617f` |

## 7. What is and is not established

- **Established, as computations.** For each (n, δ) listed as certified, `certify` computed K(r)
  exactly, and `check-certificate`, a separate compiled Lean program sharing only the exact
  arithmetic, verified (C1)–(C4) for it. Both are tested by `lake test` (known finite cases,
  rows of the tables above, tangency and cap cases, a triple point, eleven tampered certificates).
- **Not established by a proof.** The checker is a program, not a kernel-checked proof: its
  correctness rests on the arguments in its docstrings, on the tests, and on the Lean compiler and
  runtime (and for the generator's float filter, on IEEE 754 arithmetic; the checker does not use
  floats). The link between "the checker accepts" and the Lean proposition
  `TDCSG.ExistsCertificate n r` is by correspondence of definitions (§2), not by a formal proof.
  The certificate theorem itself, `TDCSG.CutSetCertificate n`, is proved on paper and refereed, but
  not in Lean; so `TDCSG.finite_GG_of_certificate` cannot yet be applied formally.
- **What closing the gap would take.** (1) A checker written as a Lean function on a certificate
  data type (symbols as elements of a verified model of ℤ[ζ_n], e.g. `ℤ[X]/Φ_n` with a ring
  isomorphism to `ℤ[ζ_n] ⊂ ℂ`), with a theorem `check cert = true → TDCSG.Certificate n r (arcs cert)`.
  Its ingredients are the exact sign algorithm in quadratic towers (soundness of recursive squaring),
  the order of intersection points by cross products, clipping and containment of arcs, and the
  correspondence of symbols with `TDCSG.Arc` angles. (2) Running it on a certificate of 10⁵–10⁶
  arcs: kernel reduction (`decide`) is far out of reach at this size; `native_decide` would trust
  the compiler (as the present program does), so the gain would be the verified algorithm, not a
  smaller trusted base. (3) A Lean proof of `TDCSG.CutSetCertificate` (the cell-decomposition
  argument of Theorem 4.2).
