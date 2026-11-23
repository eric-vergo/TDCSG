# Relative certificates at the critical radius, and float-free certified ranges

Authors: Eric Vergo, Claude

This note records the *relative* (window-clipped) certificates computed by the Lean engine
(`tdcsg-orbit certify-relative` and `tdcsg-orbit check-relative-certificate`), the theorem they
are certificates for, what was reproduced from
[`proofs/sharp-lower-bound-combined.md`](proofs/sharp-lower-bound-combined.md) (cited below as
*the combined note*), the window-free symmetric closures that extend the certified finiteness
ranges, the interval-of-validity computation, and the hybrid certificate. Ordinary cut-set
certificates and their checker are in [`certificates.md`](certificates.md).

The note has been independently refereed; the report is
[`proofs/referee-report-relative-certificates.md`](proofs/referee-report-relative-certificates.md),
and §11 records its verdicts.

## 1. Summary

1. **Built.** `certify-relative` computes the smallest restricted closure (Definition 4.1 of the
   combined note) at an exact radius, in particular at `r_c` where tangencies and triple points
   occur, with every decision certified and every coincidence identified and located exactly;
   `--symmetric` stores one circle per orbit of `±z, ±z̄`. `check-relative-certificate` verifies
   the hypotheses of the relative-certificate theorem from the file alone, sharing only the exact
   layer, with no floating-point decision, including the critical points and the exact
   disjointness of the windows. `validity-interval` computes the exact radius at which an
   ordinary certificate's symbolic arcs stop being valid. All are tested by `lake test`.
2. **The theorem** (Theorem 4.2 of the combined note, re-read in §3): no gap affects the checker;
   the bound is `1 + 20nF` for general `n`; coincidences are not confined to the windows.
3. **Float-free certified at `r_c`**: windows 1–8 of the note's Table 5.1 for `n = 5` (counts and
   check counts agree exactly with the note, `chk.py` and `rcut.c`); window 9 not run (memory);
   one window for `n = 8` (a second did not close), two for `n = 10`, four for `n = 12`.
4. **Hybrid**: Theorem H (proved here; refereed correct after minor fixes) makes a windowed storage of a cut set a valid
   certificate; it saves at most about 2.5× in memory, so level 2 for `n = 5` is not certified.
5. **New best radius**: `n = 8` at level 5, `δ = 0.02188` (`r_c − r_* = 0.006404`, from
   0.008135); tiny exact extensions for `n = 10, 12` by the interval of validity.

## 2. Definitions and the theorem the checker verifies

Throughout, `ζ = e^{2πi/n}`, `Λ = ℤ[ζ]`, `D_1, D_2` are the closed disks of radius `r` about `∓1`,
`A^{±1}` and `B^{±1}` are the rotations by `ζ^{∓1}` about `-1` and `1`, and
`GG_n(r) = ⟨a, b⟩` with `a = A` on `D_1`, the identity elsewhere (likewise `b`).

**Critical points.** At a radius with `r² ∈ ℚ(ζ)⁺`, the critical points are the lattice points on
`∂D_1 ∪ ∂D_2`: `P = p + w`, `p = ±1`, `w ∈ Λ`, `|w|² = r²`. The engine finds all such `w` from an
exact bound: the trace form `Tr(w w̄) = Σ_σ |σ(w)|²` is the positive definite quadratic form
`xᵀ G x` in the coefficient vector `x` (`G_ij = Tr ζ^{i−j}`), and `Tr(w w̄) = Tr(r²)`, so
`x_i² ≤ Tr(r²) (G⁻¹)_ii`; every vector of that box is tested. Generator and checker do this with
separate code (Gauss–Jordan and Cramer's rule respectively). At `r = r_c`:

| n | `r_c²` | lattice elements of norm `r_c²` | critical points | classes under `±z, ±z̄` | combined/n = 8 notes |
|---|---|---|---|---|---|
| 5 | `3 + φ` | 20 | 38 | 10 | 38 in 10 classes (Lemma 2.1): agrees |
| 8 | `10 − 5√2` | 16 | 32 | 8 | 32 in 8 classes (`sharp-lower-bound-n8.md` Table 2.1): agrees |
| 10 | `4 − φ` | 20 | 38 | 10 | not stated |
| 12 | `40 − 22√3` | 24 | 48 | 12 | not stated |

(`tdcsg-orbit critical-points -n N --r2 closed` lists them with their classes.)

**Windows** (§3 of the combined note, for every `n`). A *window shape* is `w ∈ Λ`, `w ≠ 0`,
`|w| < r`. With `V = {w, −w, w̄, −w̄}`,

`W₀ = ⋂_{v ∈ V} D(v, r)`,  `W_P = P + W₀` for every critical point `P`,  `W = ⋃_P W_P`,

closed disks of the same radius `r`. `W₀` is compact and convex with `0` in its interior,
invariant under `z ↦ −z` and `z ↦ z̄`, and bounded by arcs of the circles `C(v)`. The windows must
be pairwise disjoint; the engine proves this exactly. A *corner* of `W₀` is a point of two of the
circles `C(v)` lying in every disk `D(v')`. The farthest point of `W₀` from `0` is a corner: a
boundary arc of `W₀` on `C(v)` cannot contain the point of `C(v)` farthest from `0`, which lies
outside `D(−v)`, and `|x|` is unimodal along `C(v)`. So `W_P ∩ W_Q = ∅` whenever
`|P − Q|² > 4|x|²` for every corner `x`. This is one exact sign in `ℚ(ζ)⁺(√S₄, √H)` per corner and
pair (`CircleCtx.diskSign`; the combined note checked disjointness in floating point,
`wingeo.py`). With `w = 0` there are no windows (`W = ∅`).

**Strict chains, restricted closures.** A *strict chain* at radius `r` takes each step
`S ∈ {A^{±1}, B^{±1}}` only at a point of the *open* disk of `S`. A *restricted closure* for `W`
is a finite union `K'` of closed arcs of circles of radius `r` with

- **(R1)** `∂D_1 ∪ ∂D_2 ∪ ∂W ⊆ K'`;
- **(R2)** for every arc `α` of `K'` and every `S`, with `D_S` the closed disk of `S`, every
  non-degenerate component of `α ∩ D_S ∖ int W` is mapped by `S` into `K'`.

**Theorem (relative certificate; Theorem 4.2 of the combined note, general `n`).** If a
restricted closure `K'` exists for `W` at radius `r`, then every strict chain at `r` whose
intermediate points avoid `W` has at most `1 + 20 n F` distinct endpoints from a given start,
`F` the number of bounded faces of `ℂ ∖ K'` not contained in `W`. Every chain at a radius
`r' < r` is a strict chain at `r` once its trivial steps are deleted, so the same bound holds for
`GG_n(r')`, uniformly in `r' < r`.

For `n = 5` the bound is the note's `1 + 100F`: the rotation part of an isometry
`x ↦ ζ^j x + t` mapping a bounded face onto a given face takes `n` values, so the count is
`1 + 4(nF + 4nF)`.

**Consequences** (Corollary 4.3 and Proposition 4.4 of the combined note, unchanged): with
`β_W = 1 + 20nF`, `|O_r(z)| ≤ β_W max(1, sup_x |O_r(x) ∩ W|)` for every `r < r_c`, so `GG_n(r)` is
finite if and only if orbits meet `W` in boundedly many points, and the dynamics induced on `W` is
generated by the finitely many words of length at most `β_W + 1`.

**With `W = ∅`** the theorem is a *strict cut-set theorem* at any radius: a finite union `M` of
closed arcs with `∂D_1 ∪ ∂D_2 ⊆ M` and (R2) (no window) bounds every strict orbit at `r`, so
`GG_n(r')` is finite for every `r' < r`, with no tangency or endpoint conditions. If in addition
(C3) and (C4) of [`certificates.md`](certificates.md) hold, `M` is an ordinary certificate and
`GG_n(r)` itself is finite by the refereed certificate theorem.

### What the checker verifies

`check-relative-certificate FILE [--threads T]` reads only the file and verifies, with no
floating-point decision:

1. the listed critical points are exactly the lattice points on `∂D_1 ∪ ∂D_2` at the file's `r`
   (recomputed);
2. the shape: `w = 0` (no windows), or `w ≠ 0`, `|w| < r`, the corners of `W₀`, and pairwise
   disjointness of the windows by the corner bound;
3. every symbol names a point of its circle; on each circle the arcs are non-degenerate, pairwise
   disjoint and do not touch; in the symmetric mode every listed circle is the canonical
   (lexicographically least) one of its orbit under `±z, ±z̄`, and the arcs on a circle are
   invariant under its stabiliser;
4. **(K1)** both boundary circles are full (in the symmetric mode `∂D_1`, which stands for both);
5. **(K2)** every boundary arc of every window, the part of `C(P + v)` inside the other disks
   `D(P + v')`, lies in one listed arc (moved to its canonical circle in the symmetric mode);
6. **(K3)** for every listed arc `α` on `C(c)`, `p = ±1` with `c ≠ p` and `C(c)` crossing `∂D_p`,
   and `k = ±1`: `α ∩ D_p` minus the open arcs `C(c) ∩ int W_P` falls into closed arcs, and each
   non-degenerate one, rotated by `ζ^k` about `p`, lies in one listed arc. `C(c) ∩ int W_P` is the
   intersection of the open arcs of `C(c)` inside the four disks `D(P + v)`, each shorter than
   `π`, hence one arc; it is empty if `C(c)` does not cross every `C(P + v)`. A circle tangent to
   `∂D_p` meets `D_p` in one point and contributes nothing; for `c = p` the images lie on `∂D_p`;
7. the summary line; and it reports the tangent circles and the (C4) endpoint counts.

(K1)–(K2) are (R1) and (K3) is (R2): a component of `α ∩ D_S ∖ int W` is a union of the closed
arcs of item 6. In the symmetric mode `K'` is the union of the images of the listed arcs under the
four symmetries; the conditions for `g(α)` follow from those for `α` because `g` maps
`D_1, D_2, W` and `K'` to themselves and conjugates `{A^{±1}, B^{±1}}` to itself (`z ↦ −z`
exchanges `A` and `B`, `z ↦ z̄` exchanges `A` and `A⁻¹`).

Windows near a circle are found with a certified prefilter: a circle can meet `int W_P` only if
`| |c − P| − r | < ρ̄`, where `ρ̄ = m/2¹⁶` exceeds the circumradius of `W₀` (verified exactly
against every corner). The generator decides "certainly farther" with the float filter of
`CircleFilter`, the checker with integer ball arithmetic; an undecided case keeps the window.

The checker shares with the generator only the exact layer: `Ball`, `Field`, `Tower`, `Disk` and
`CirclePoint`, including `CircleCtx.diskSign` (the exact sign of `t − |x − z|²` for a symbol point
`x`), `gapSign`, `rot`, `rotSym` and `validSym`. It shares with the ordinary checker `parseVec`,
`parseSym`, `mkPt`, `cmp`, `clip`, `covered`, `posCmp`, `inside` and `msort`. The generator
(`RelClosure` → `Closure` → `CircleFilter`) does not import `CertCheck`. A defect in `diskSign`
would be common to generator and checker, so the window geometry is not checked independently
inside the repository; the `lake test` comparison of `diskSign` against floating point covers the
tested cases.

## 3. Reading Theorem 4.2 critically

The proof of Theorem 4.2 was re-derived while implementing the checker. No gap affects what the
checker must verify; the points below fix readings.

1. **Numbering.** In the combined note the relative-certificate theorem is Theorem 4.2;
   Theorem 5.2 is its application to Table 5.1.
2. **General `n`.** The constant `1 + 100F` is for `n = 5`; for general `n` it is `1 + 20nF`
   (§2). Only finiteness is used downstream.
3. **"Every arc of `K'`".** Condition 2 of Definition 4.1 quantifies over arcs of `K'`. The proof
   of Step 1 works for any finite list of arcs whose union is `K'`: if `y ∈ K' ∖ int W` lies in
   the interior of `D_S` and every listed arc through `y` enters `int W` on each side, then `y` is
   on `∂W`, and the listed arc through `y` on the window circle `C(P + v)` contains a
   non-degenerate piece of `C(P + v) ∖ int W` at `y` (one side is on `∂W_P`, the other outside
   `W_P`, and no other window is near since the windows are disjoint). The checker uses the maximal
   arcs.
4. **Images inside the windows.** Condition 2 asks that `S(κ) ⊆ K'`, including the part of
   `S(κ)` inside `int W`; the proof uses only `S(κ) ∖ int W ⊆ K'`. The checker verifies the
   literal (stronger) condition, which the smallest restricted closure satisfies.
5. **Disjointness and convexity of the windows** are used in Step 1 (boundary arcs of `W_P` avoid
   `int W`). The combined note verified disjointness numerically; the checker proves it exactly
   (§2).
6. **Where tangencies and coincidences occur.** Tangency of a carrying circle to `∂D_p` happens
   only at critical points (Lemma 2.1(4)); this was confirmed in every run (every tangency has its
   point of contact `(c + p)/2` at a critical point). Coincidences (three circles of `K'` through
   one point) are **not** confined to the critical points or to the windows: every coincidence
   found lies at a lattice point (`r_c²` is a norm, so every lattice point lies on the 20, 16, 20
   or 24 lattice circles of radius `r_c` about it), almost none at a critical point, and for the
   window `(−3, 4, −4, 0)` 248 of 579 coincidence records lie in the bulk. Theorem 4.2 has no
   hypothesis on coincidences; the engine identifies coinciding points exactly. So nothing is
   wrong in the note (which says only that triple points occur), but the expectation that they
   occur only inside the windows is false.
7. **Lemma 3.4 (generic points)** needs the chain points of a generic start to avoid the circles
   of `K'` and `∂D_S`; these are countably many circles and the chain points are images
   `ζ^j x + t`, `t ∈ Λ`, so generic points (dense by Baire) exist. Correct as written.

## 4. The programs

`certify-relative -n N --r2 SPEC --window w0,w1,… [--symmetric] [--out FILE]` computes the
smallest restricted closure as a work-list closure: the boundary circles and the window boundary
arcs are inserted first; every new piece is clipped to `D_p`, has the open window arcs removed,
and is rotated by `ζ^{±1}` about `p`; uncovered parts of images are inserted and merged. Every
order and equality decision is the certified one of the ordinary generator (float filter with a
proven error bound, exact tower sign otherwise). Tangent circles contribute nothing and are
recorded; coincidences are logged and afterwards located exactly (lattice point or not, critical
or not, inside a window, on its boundary, or in the bulk). With `--symmetric` only the canonical
circle of each orbit of `±z, ±z̄` is stored, with its stabiliser-invariant arc set, as in
`rcut.c`; this is exact because the system, the windows and hence the smallest restricted closure
are invariant, and it divides time and memory by about four.

**Format.** Like [`certificates.md`](certificates.md) §3, with header
`tdcsg-relative-certificate 1`, the lines `window w` (`0`: no windows), `symmetric` (optional),
one `critical P` per critical point, `full c` and `arc c e₁ s₁ e₂ s₂` records, and
`summary circles C arcs A windows K` (listed circles and arcs), then `end`.

**Tests** (`lake test`): critical points and classes for `n = 5, 8, 10, 12` (generator and checker
enumerations agree; `latticeOfNorm` against a brute-force search for five norms); `diskSign`
against floating point at 300 random points for `n = 5, 8, 12`; the window geometry of `(0,2,−1,0)`
(8 corners, 703 disjoint pairs, `ρ̄` within `2⁻¹⁶` of `0.2924`), an overlapping shape detected, a
zero shape and `|w| ≥ r` refused; the `n = 5` closure at `r_c` with the window `(0,2,−1,0)` in both
modes (the counts of Table 5.1, 8 tangencies all at critical points, coincidences all at lattice
points and none in the bulk; the checker accepts); a small case (`n = 6`, `r² = 13`, `w = (2, 2)`:
22 windows, 536 arcs) in both modes; and rejected tamperings: a deleted arc, a deleted arc on a
window circle, a deleted boundary circle, an endpoint with its side flipped, moved to the other
intersection point or replaced by another arc's, a dropped critical point, a non-critical point
listed, a critical point listed twice, an overlapping window, the windows removed, a smaller
window (`(5,−1,4,0)` in place of `(0,2,−1,0)` for `n = 5`), a changed radius, a wrong summary, a
truncated file, the `symmetric` line removed, an arc moved to a non-canonical circle; the
window-free symmetric closure at `n = 5`, `δ = 1/10` (the ordinary engine's counts, (C3), (C4));
and the interval of validity of the `n = 5`, `δ = 9/10` certificate (below).

## 5. Reproduction of Table 5.1 of the combined note (`n = 5`, `r = r_c`)

All runs at `r² = 3 + φ` exactly (`--r2 closed`), windows about all 38 critical points. Counts
are of circles and maximal arcs modulo `±z, ±z̄` (one circle per orbit; arcs exclude the full
boundary circle, as in the note's table), then in all. "Images" is the number of (K3) image arcs
the checker verified. Rows 1–4 were run in both modes (full storage and `--symmetric`), with
identical counts; rows 5–8 symmetric only. Times are wall-clock on the development machine (Apple
M2 Ultra) with several runs in parallel, generator single-threaded, checker with 3–6 threads;
memory is peak resident size.

| # | `w` | `ρ_W` | circles | maximal arcs | in all (circles / arcs) | tangencies (at critical points) | combined note | generator | checker | file (bytes) |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `0,2,−1,0` | 0.2924 | 3 442 | 5 614 | 13 692 / 22 230 | 8 (8) | equal; `chk.py` 51 828 images | 1 s | **VALID**, 51 828 images, 19 s | 857 326 |
| 2 | `5,−1,4,0` | 0.1815 | 113 208 | 202 879 | 452 153 / 808 444 | 12 (12) | equal; `chk.py` 2 023 476 | 84 s, 0.60 GB | **VALID**, 2 023 476 images, 346 s, 0.75 GB | 37 446 323 |
| 3 | `−3,4,−4,0` | 0.1124 | 196 900 | 312 969 | 786 925 / 1 249 286 | 8 (8) | equal; `chk.py` 3 192 528 | 119 s, 0.97 GB | **VALID**, 3 192 528 images, 510 s, 1.20 GB | 58 977 952 |
| 4 | `−3,−1,−1,−5` | 0.0935 | 152 506 | 286 472 | 609 320 / 1 142 778 | 8 (8) | equal (not checked there) | 126 s, 0.85 GB | **VALID**, 2 940 288 images, 406 s, 1.04 GB | 53 756 051 |
| 5 | `−3,2,−3,−2` | 0.0466 | 1 179 129 | 2 840 004 | 4 715 312 / 11 351 370 | 8 (8) | equal (not checked there) | 327 s, 1.63 GB | **VALID**, 7 336 946 images, 715 s, 2.51 GB | 167 707 349 |
| 6 | `2,−5,5,−6` | 0.0371 | 1 939 012 | 6 509 586 | 7 754 030 / 26 020 150 | 16 (16) | equal (not checked there) | 1 242 s, 3.51 GB | **VALID**, 16 822 522 images, 1 716 s, 5.55 GB | 393 462 687 |
| 7 | `2,3,0,2` | 0.0340 | 2 437 445 | 6 595 363 | 9 747 711 / 26 365 194 | 8 (8) | equal (not checked there) | 1 173 s, 3.69 GB | **VALID**, 17 046 316 images, 2 141 s, 5.72 GB | 399 843 442 |
| 8 | `2,−2,3,−3` | 0.0247 | 1 982 707 | 6 244 141 | 7 927 775 / 24 955 002 | 16 (16) | equal (not checked there) | 1 294 s, 3.39 GB | **VALID**, 16 144 754 images, 2 957 s, 2.45 GB | 379 708 887 |
| 9 | `2,6,−2,5` | 0.0166 | — | — | — | — | 10 960 690 / 36 177 413 (`rcut.c`) | not run (needs about 20 GB for the generator and 14 GB for the checker, not available alongside the other runs) | — | — |

Rows 1–4 report the full-storage files (the symmetric file of row 1 was also accepted, with
13 104 image arcs on canonical circles); rows 5–8 the symmetric files, whose image counts
are those of the canonical circles and equal `rcut.c`'s own re-check counts (`images_checked`
7 336 946, 16 822 522, 17 046 316, 16 144 754 in the logs of `sharp2/`). Tangencies are counted over all
circles (the symmetric runs count canonical circles: 2 or 4).

**Agreement.** Every circle and maximal-arc count agrees with Table 5.1 of the combined note, and
so does `max|σ(c)|` (52.5, 178.3, 249.0, 254.6, 735.2, 1105.4, 1091.6, 1091.6). The image counts
agree exactly with `chk.py` for rows 1–3 (its numbers in the note's table) and with `rcut.c`'s
self-check for rows 5–8. There is no disagreement. Pieces differ (they depend on the processing
order): for example 22 789 387 against 26 373 994 canonical pieces in row 5.

**Coincidences.** Located exactly in every run (full-storage rows): row 1, 58 records at 34
lattice points, 32 inside windows and 26 on window boundaries; row 2, 186 records at 91 lattice
points, 4 at critical points, 58 inside windows, 128 on boundaries; row 3, 579 records at 146
lattice points, none at critical points, 34 inside windows, 297 on boundaries and **248 in the
bulk**; row 4 and the symmetric rows 5–8, none met. No coincidence at a non-lattice point was met.
Every tangency of a carrying circle to `∂D_p` has its point of contact at a critical point.

**Status of Theorem 5.2 of the combined note.** For windows 1–8 the restricted closure
is certified float-free: generated with certified decisions and verified by the separate
checker. So for those windows the uniform bound on window-avoiding chains for every `r < r_c`
holds through Theorem 4.2 alone, with no floating-point ordering in the computation.

**Reproduction.** For row `k` with shape `w`:

```sh
tdcsg-orbit certify-relative -n 5 --r2 closed --window w --symmetric --out n5-wk.rcert
tdcsg-orbit check-relative-certificate n5-wk.rcert --threads 4
```

(without `--symmetric` for the full-storage files of rows 1–4). The tables print shapes with the
Unicode minus sign `−`; the command line needs ASCII hyphen-minus signs, for example
`--window 0,2,-1,0`. The default caps (2·10⁹ pieces,
2·10⁸ circles) suffice for every row. SHA-256 of the files as written:

| file | SHA-256 |
|---|---|
| row 1, full | `7a60f7c673a9bf64e7fba36839f7f6be0ae9a9b8be9b4da8ba57ee8f123dd752` |
| row 1, symmetric | `db3a946434f2e389c4ff590736b89634b2b154aa4c434d76900ebb67ddf9f2ec` |
| row 2, full | `8a5aef025b0e2a5c4f35b9a4a663c73b14da644a58ab04dd20b40174fff283f3` |
| row 3, full | `690c8dcb743f7bdc578b926dff7d67172e18ffd4cbc7d29ce4543d85368e6005` |
| row 4, full | `425727562d0a65c5d4a462c256bf87071db81ca6e4a177ad775d92428dff38b0` |
| row 5, symmetric | `71fde7b749bccdb9cfceba9af1f5b70f171e5529f6e0245a77618a5d1300d17c` |
| row 6, symmetric | `2bfc4aa15bc47c3f4c98abfa9a3d3a84672d3176a83f6286bba2e84b6934b1ae` |
| row 7, symmetric | `5165f81dce2dcb2645bf2328f64b6b24563f5cc638c98013a920368d429cea31` |
| row 8, symmetric | `c8b1fdb982ae4843700896758e83d8085a212bf5517496fcf1710e171f758f83` |

The row-1 symmetric certificate is committed as
[`../certificates/n5-rc-w0_2_-1_0.rcert`](../certificates/n5-rc-w0_2_-1_0.rcert).

## 6. `n = 8, 10, 12` at `r_c`

Windows about all critical points at `r = r_c` (`--r2 closed`), symmetric mode. The shapes were
chosen with `tdcsg-orbit critical-points -n N --r2 closed --search 6`, which lists every shape
with coefficients in `[−6, 6]` (one per symmetry orbit) whose windows are disjoint, with the
circumradius bound `ρ̄`. Counts as in §5 (modulo `±z, ±z̄`, arcs without the full boundary circle;
then in all); tangencies are of canonical circles, every one with its point of contact at a
critical point. No coincidence was met except for `n = 12`, `(−4, 4, 2, −5)`: 398 records at 59
lattice points, all on window boundaries.

| n | `w` | `ρ̄` | circles | maximal arcs | in all (circles / arcs) | tangencies | generator | checker | SHA-256 |
|---|---|---|---|---|---|---|---|---|---|
| 8 | `−4,0,4,−4` | 0.0760 | 416 172 | 2 136 732 | 1 663 814 / 8 531 662 | 3 | 786 s, 1.13 GB | **VALID**, 5 039 308 images, 1 079 s, 0.65 GB | `2ff770a7a1b5aad72d7696a18dac1b2c6c0370231b4bb2a39400645f3273a3d6` |
| 8 | `−3,0,2,−2` | 0.0578 | — | — | not closed: stopped at 3.0·10⁸ pieces, 1.74·10⁶ circles, when the session's runs ended | — | 8 700 s | — | — |
| 10 | `−6,2,4,−6` | 0.1180 | 36 744 | 131 741 | 146 550 / 523 730 | 4 | 12 s, 0.07 GB | **VALID**, 300 340 images, 46 s, 0.12 GB | `f152856472eef725f8438b17206d9442551d3daf20c142c8e55b59ac5c37aca8` |
| 10 | `−5,3,1,−4` | 0.0650 | 301 499 | 1 162 605 | 1 204 775 / 4 635 860 | 4 | 113 s, 0.60 GB | **VALID**, 2 661 826 images, 359 s, 0.98 GB | `401bada7f9b454883f2d104d2124b746a7ef83e366e11e40f30fdf7a271343b5` |
| 10 | `−4,4,0,−4` | 0.0480 | — | — | not closed: stopped by the memory watchdog at 3.0·10⁸ pieces, 2.66·10⁶ circles, 6.7 GB | — | 8 100 s | — | — |
| 12 | `−6,5,1,−4` | 0.0915 | 7 888 | 13 124 | 31 391 / 51 812 | 3 | 1 s | **VALID**, 29 290 images, 7 s | `ac2a76677d01655d4a370736544a12f0a9e2357e4b6ce3f827d17d226fe15f95` |
| 12 | `−4,4,2,−5` | 0.0718 | 235 285 | 425 436 | 940 301 / 1 697 684 | 5 | 39 s, 0.27 GB | **VALID**, 948 942 images, 204 s, 0.40 GB | `33edc61d471aa18a778fed8438982b8acf8b4a05bd9b809824f0bf1aca955e11` |
| 12 | `−5,4,1,−2` | 0.0405 | 308 130 | 563 445 | 1 231 620 / 2 249 388 | 5 | 72 s, 0.39 GB | **VALID**, 1 262 576 images, 469 s, 0.24 GB | `e011a3334ddd6b4510dc3c3d70bef56458823a149c1e1bc1afd4ef96b9992cea` |
| 12 | `−3,1,2,−3` | 0.0124 | 4 618 187 | 9 368 319 | 18 469 410 / 37 451 840 | 5 | 1 238 s, 5.66 GB | **VALID**, 21 066 738 images, 4 872 s, 3.68 GB | `d7ee3be42a1c92fd44c1e50278729b8fd6b40f414ddce48b91b8275c9cc1a766` |

The `n = 12` shape `(−6, 5, 1, −4)` closure (565 kB) is committed as
[`../certificates/n12-rc-w-6_5_1_-4.rcert`](../certificates/n12-rc-w-6_5_1_-4.rcert). Reproduction:
`tdcsg-orbit certify-relative -n N --r2 closed --window w --symmetric --out FILE`, then
`tdcsg-orbit check-relative-certificate FILE --threads 4`, with the shape typed in ASCII
hyphen-minus signs (§5).

So Theorem 5.2 of the combined note (the uniform bound on window-avoiding chains below `r_c`)
holds float-free for these windows for `n = 8, 10, 12` as well. Unlike `n = 5`, where the
closure size grows slowly between `ρ_W = 0.29` and `0.025`, these closures grow fast already at
moderate windows (`n = 10`, `ρ̄ = 0.048`, did not close within the memory available alongside the
other runs).

## 7. Deeper certified ranges

Without windows (`--window 0`) the symmetric closure is the cut set `K(r)` itself, stored one
circle per orbit; the relative checker then also reports (C3) and (C4), and when they hold the
union of the listed arcs and their symmetric images is an ordinary certificate (the conditions for
`g(α)` follow from those for `α`, as in §2), so the refereed certificate theorem gives `GG_n(r)`
finite. Symmetric storage divides memory by about four, which reaches the next level for `n = 8`.

| n | `δ` | circles | maximal arcs | in all (circles / arcs) | pieces | (C3), (C4) | generator | checker | SHA-256 |
|---|---|---|---|---|---|---|---|---|---|
| 5 | `1/10` (test) | 12 715 | 49 838 | 50 714 / 198 470 | 263 140 | hold | 2.5 s | **VALID** | — |
| 8 | `547/25000 = 0.02188` | 270 142 | 4 578 953 | 1 079 562 / 18 284 974 | 1.41·10⁸ | hold (35 543 endpoints) | 5 332 s, 2.36 GB | **VALID**, 10 869 666 images, 2 216 s, 1.16 GB | `4a7c18de0d857da0adcf24a6fca2690eaa177666bad67bf5bb264c1787894b6a` |
| 12 | `1/250` | 1 714 547 | 6 481 980 | 6 855 494 / 25 907 016 | 1.03·10⁸ | hold (15 868 endpoints) | 1 637 s, 3.65 GB | **not checked** (the check was stopped unfinished) | `64f4261f2a677dd9baf9ce91120a34d8b4b8a3b39302e513d13dc388863a4c52` |
| 8 | `57/5000 = 0.0114` | — | — | not closed: stopped at 2.0·10⁸ pieces, 8.3·10⁵ circles | — | — | 5 330 s | — | — |
| 12 | `1/600` | — | — | not closed: stopped at 1.0·10⁸ pieces, 1.45·10⁶ circles | — | — | 1 061 s | — | — |

`δ = 0.02188` is the level-5 radius of `sharp-lower-bound-n8.md` §5.5 (`m = 5`) rounded to five
decimals, past the jump at `δ₅ ≈ 0.0272` that no earlier certificate crossed. The exact value
`λε⁵` for `θ* = 4/5` is `0.0218762 < 0.02188`, so this certificate is at a radius just below that
`r_5`; it covers `r_5` for every `θ* ≥ 0.80014` (for example `θ* = 4001/5000`), for which `r_4`
is also inside the certified range. Reproduction:
`tdcsg-orbit certify-relative -n 8 --r2 closed-547/25000 --window 0 --symmetric --out FILE`, then
`tdcsg-orbit check-relative-certificate FILE --threads 4`. The `n = 12`, `δ = 1/250` closure is a
computation only until it is checked (`certify-relative -n 12 --r2 closed-1/250 --window 0
--symmetric`, then the checker; about 1.5 hours). For `n = 5` no window-free run beyond `1/55` was
made: level 2 needs about 6.9·10⁷ canonical arcs, some 39 GB in this generator.

## 8. The interval of validity

A certificate names its arcs by symbols, which make sense at every radius at which the named
circles cross. `tdcsg-orbit validity-interval FILE` computes, for an ordinary certificate accepted
at `ρ₀ = r₀²`, an exact `ρ₁ > ρ₀` such that the same symbolic arc set is accepted by
`check-certificate` at every `ρ ∈ [ρ₀, ρ₁)`; with the certificate theorem and group monotonicity,
`GG_n(r)` is then finite for every `r² < ρ₁`.

**Argument** (`TDCSGCompute/Validity.lean`). Every decision of the checker is either the sign of
`4ρ − |x − y|²` for two centres (symbol validity, whether a circle meets `int D_p`, (C3)), or a
cyclic order or equality of named points on one circle: arc endpoints, clip points `(p, ±)`, and
endpoints of images of clipped pieces of the circles mapped onto it. As `ρ` grows the first kind
changes only at a *disk event* `ρ = |c − p|²/4` of a circle missing `D_p` at `ρ₀` (crossing pairs
stay crossing). Named points move continuously, so the cyclic order changes only when two points
coincide, i.e. three circles `c, e₁, e₂` pass through one point: the circumcentre of the three
centres, at `ρ = R² = |a|²|b|²|a − b|² / (4 (Im ā b)²)` (`a = e₁ − c`, `b = e₂ − c`), and only if
the sides match (`s₁ = sign(|b|² − Re ā b)·sign(Im ā b)`, `s₂ = sign(Re ā b − |a|²)·sign(Im ā b)`)
(*triple event*). At the first coincidence above `ρ₀` some coinciding pair is adjacent in the
cyclic order valid just before it, so only adjacent pairs of the order at `ρ₀` need examining.
`ρ₁` is the least disk or matching triple event above `ρ₀`. If two adjacent named points already
coincide at `ρ₀`, the tool reports that there is no extension (exit code 3). Otherwise it also writes the same arcs
with the radius replaced by the largest `m/2¹⁰⁰ < ρ₁` (verified exactly to exceed `ρ₀`), and the
ordinary checker is run on that file as an independent confirmation.

The test suite checks the method on `n = 5`, `δ = 9/10`: the least event is the tangency of the
circle about `−3 + 2ζ` to `∂D_R` at `ρ₁ = 7 − 2φ` (`r_c² − ρ₁ = 0.854`), and the arcs are
accepted at `r² = 3.7639` and rejected at `3.764`.

Results for the deepest ordinary certificates of [`certificates.md`](certificates.md)
(regenerated with `tdcsg-orbit certify -n N --r2 closed-δ --max-pieces 400000000 --max-circles
20000000 --out FILE`, SHA-256 equal to the recorded one, so the files are the checked
certificates; then `tdcsg-orbit validity-interval FILE --no-check --threads 4 --out MOVED` and
`tdcsg-orbit check-certificate MOVED`):

| n | `δ₀` | adjacent pairs, disk events | least event | `r_c² − ρ₁` | same arcs at `m/2¹⁰⁰` just below `ρ₁` | time (interval, re-check) |
|---|---|---|---|---|---|---|
| 12 | `1/180 = 0.0055556` | 14 148 366, 629 542 | triple point on the circle about `(−323, 376, −8, −182)` | 0.0055543 | **VALID** (SHA-256 `84ac764d…f8da5d6`) | 994 s, 2 787 s |
| 10 | `1/47 = 0.0212766` | 8 775 676, 226 286 | triple point on the circle about `(73, −16, −90, 102)` | 0.0212735 | **VALID** (SHA-256 `a4cb12fa…01162e29`) | 605 s, 1 994 s |
| 8, 5 | `1/36`, `1/55` | not run (stopped when the session's runs ended) | | | | |

The extensions are real but tiny (the relative gain in `δ` is 2·10⁻⁴ and 1.4·10⁻⁴): the deepest
cut sets have millions of arcs, and some adjacent pair of named points meets at a triple point
just above `ρ₀`. The method is more useful for small certificates (`δ = 9/10` extends to `0.854`).
The `n = 8` extension is superseded by the level-5 certificate of §7.

## 9. The hybrid certificate

The combined note's "next" item asks for a certificate that combines the fixed relative
certificate at `r_c` (for the bulk) with a closure of the induced system inside the windows at a
radius `r < r_c`. This section states the theorem that makes such a combination valid, proves it,
and reports what it buys.

**Theorem H (strict cut-set theorem).** Let `r > 0` and let `M` be the union of a finite family
of non-degenerate closed circular arcs, with `∂D_1(r) ∪ ∂D_2(r) ⊆ M`, such that for every arc `α`
of the family, every `S ∈ {A^{±1}, B^{±1}}` and every non-degenerate component `κ` of
`α ∩ D_S(r)`, `S(κ) ⊆ M`. Then every strict orbit at `r` has at most `n F` points (`F` the number
of bounded faces of `ℂ ∖ M`), and `GG_n(r')` is finite for every `r' < r`.

*Proof.* This is Theorem 4.2 of the combined note with `W = ∅` and `r_c` replaced by `r`; its
proof does not use that `r_c` is critical. Faces lie inside `int D_S` or outside `D_S`: a face is
connected, open and disjoint from `∂D_S ⊆ M`. If `X` is a face in `int D_S` and
`y ∈ S(X) ∩ M`, then `y ∈ int D_S`, so `y` lies in a non-degenerate component of `α ∩ D_S` for an
arc `α ∋ y` of the family, and the hypothesis for `S⁻¹` (same disk) gives
`S⁻¹(y) ∈ M ∩ X = ∅`. So `S(X)` is contained in one face `Y`. Conversely, `Y` meets `int D_S`,
so `Y ⊆ int D_S`, and the same argument for `S⁻¹` on `Y` puts `S⁻¹(Y)` in one face, which
contains `X`; hence `S⁻¹(Y) ⊆ X`, and `S(X) = Y` is a face. A generic start `x` (dense,
Lemma 3.4) has all strict-chain points in faces, each reached by an isometry `z ↦ ζ^j z + t`
(`t ∈ Λ`, since `±1 ∈ Λ`) carrying the face of `x` onto the face of the point. If `x` lies in the
unbounded face, which lies outside both disks, no strict step applies and the strict orbit of `x`
is `{x}`, with `1 ≤ nF` because `F ≥ 1`. Otherwise the face of `x` is bounded, so such an
isometry is fixed by `j` and the target face (a bounded set is not invariant under a non-zero
translation), the strict orbit of `x` has at most `nF` points, and by Lemma 3.4 so does every
strict orbit. A chain at `r' < r` is a strict chain at `r` after deleting trivial
steps, so the orbits of `GG_n(r')` are uniformly bounded, and the group is finite
(`theorem1-converse.md`, Proposition 4.2). `□`

**The hybrid certificate.** Fix windows `W` about the critical points of `r_c` (disks of radius
`r`, so that one radius serves the exact layer) and a radius `r < r_c`. Store only
`L = M ∩ W`, a finite union of closed arcs inside `W`, and verify the hypotheses of Theorem H for
`M` *without storing the rest of `M`*: process `L` in batches; for a batch, map the batch's arcs
(arcs of `L`, and `∂D_1 ∪ ∂D_2` for the first batch) in full, with no clipping by `int W`, and
form the relative closure `B` of these images, in which only the transported pieces are clipped
by `int W`, as in §2; check that `B` is closed relative to `W`, that every part of an arc of `B`
inside `W` lies in `L`, and discard `B`. Then the family of the arcs of `L` and of every `B`, with
union `M = L ∪ ⋃ B`, satisfies Theorem H:

- for an arc `α` of some `B` and a non-degenerate component `κ` of `α ∩ D_S`, the components of
  `κ ∖ int W` are mapped into `B`, because `B` is closed relative to `W`;
- the parts of `κ` in `W` lie in arcs of `L`, including isolated points on `∂W` (an isolated point of
  `κ ∖ int W` cannot be interior to `κ`, because `C(c) ∩ W_P` is connected and the windows are
  disjoint);
- every component of `λ ∩ D_S` for an arc `λ` of `L` has its full image in the batch that
  processed `λ`, which is part of `M`;
- `∂D_1 ∪ ∂D_2` is seeded.

So `GG_n(r')` is finite for every `r' < r`. The verification is proved by Theorem H alone; the
relative certificate is not needed for *validity*.

**Where the relative certificate would enter (motivation only).** No result here depends on this
paragraph. Proposition 4.4 of the combined note says that when a restricted closure exists for the
windows `W(r_c)` built from disks of radius `r_c`, the germs of all chains at any `r < r_c` whose
intermediate points avoid `W(r_c)` lie in one finite set `G_W` (words of length at most
`β_W + 1`). The hybrid windows above are built from disks of radius `r`, and `W(r) ⊆ W(r_c)`, so a
chain that avoids `W(r)` need not avoid `W(r_c)`, and the proposition says nothing about the
batches as constructed. The hope is that a hybrid built with the windows `W(r_c)` (Theorem H does
not depend on the window shape, and Definition 4.1 does not use the window radius) has every
batch inside the images under `G_W` of its seeds, hence finite uniformly in `r`; this would also
need Proposition 4.4 for strict chains, which is not proved here. The *induced-system*
formulation (an arc set `L` closed under the first-return maps to the windows `W(r_c)`, giving
`|O_r(x) ∩ W| ≤ nF_L` and then, by Corollary 4.3, `|O_r(x)| ≤ β_W n F_L`) leads to the same
computation: the first-return maps are bulk chains whose domains are cut by
pullbacks of `∂D_p(r)` and `∂W`, so verifying that `L` is closed under them means transporting
the arcs of `L` and of `∂D_p(r)` through the bulk exactly as above, plus the pullbacks of `∂W`.
Theorem H is the simpler of the two and needs neither `β_W` nor `F`.

**What it buys (measured).** A prototype of the windowed generator was run against the ordinary
symmetric closure at `n = 5`, `δ = 1/20` (`K(r)`: 47 671 circles and 208 875 arcs modulo
`±z, ±z̄`; 1.38·10⁶ pieces, 19 s). The prototype is not in the repository, so the measurements
below cannot be reproduced from it.

| window shape (at `r_c`) | batch size | stored `L` (arcs) | largest batch (arcs) | pieces processed | time |
|---|---|---|---|---|---|
| `(−3, 4, −4, 0)` | 100 000 | 6 892 | 79 360 | 3.42·10⁶ | 59 s |
| `(−3, 4, −4, 0)` | 1 000 | 6 892 | 59 994 | 3.97·10⁶ | 67 s |
| `(5, −1, 4, 0)` | 100 000 | 20 281 | 88 328 | 3.83·10⁶ | 86 s |
| `(−3, 2, −3, −2)` | 100 000 | 653 | 178 084 | 4.02·10⁶ | 67 s |

(A float measurement on the full certificate gives the same picture: 27%, 4.3% and 0.7% of the
833 366 arcs of `K(r)` touch the windows of circumradius 0.29, 0.11 and 0.047.) The stored part is
small, but the peak memory is set by the largest batch, which is always a large fraction of the
bulk: the largest batch is 29–85% of `K(r)`, and the
transports of a batch of seeds spread over the whole bulk. The saving is at most a factor of about
2.5 in memory, for a factor 3 in time. That does not reach level 2 for `n = 5`, whose cut set has
6.9·10⁷ maximal arcs modulo symmetry (1.4·10⁹ pieces in `kcut4.c`): about 39 GB in the symmetric
generator, against the 24 GB allowed. The prototype was therefore not developed into a
certificate format and checker. **Level 2 for `n = 5` remains
uncertified.** What would change this is a coarser invariant partition than the arc arrangement,
for instance the partition of `W` by the *set of available germs* of the first-return maps (many
arcs of `K(r) ∩ W` separate regions with the same germs); computing it needs orbit and germ data,
not arc closures.

## 10. Best certified radius per `n`

`r_*² = r_c² − δ_*`: `GG_n(r)` is finite for every `r ≤ r_*` (and, for `n = 10, 12`, for every
`r² < ρ₁`, by §8).

| n | `r_c` | `δ_*` | `r_*` | `r_c − r_*` | how | previous best (`certificates.md`) |
|---|---|---|---|---|---|---|
| 5 | 2.148961 | `1/55` | 2.144727 | 0.004235 | ordinary certificate (unchanged) | same |
| 8 | 1.711412 | **`547/25000 = 0.02188`** | **1.705008** | **0.006404** | symmetric window-free certificate, (C1)–(C4) checked | `1/36`, 0.008135 |
| 10 | 1.543362 | `1/47` (`ρ₁`: `δ ≈ 0.0212735`) | 1.536454 (1.536455) | 0.006908 | ordinary certificate; interval of validity | `1/47` |
| 12 | 1.376547 | `1/180` (`ρ₁`: `δ ≈ 0.0055543`) | 1.374528 (1.374528) | 0.002019 | ordinary certificate; interval of validity | `1/180` |

For `n = 8, 10, 12` the remaining windows `(r_*, r_c)` are open. For `n = 5` finiteness on the
whole window is proved by a different argument
([`proofs/sharp-lower-bound-n5-pentagrid.md`](proofs/sharp-lower-bound-n5-pentagrid.md)), which
uses no certificate; as a certificate, level 2 for `n = 5` is only the floating-point computation
of `sharp-lower-bound-n5.md`.

## 11. What is established and what is not

- **Certified, as computations.** For every row marked VALID, the generator computed the closure
  with every decision certified, and the separate checker, which makes no floating-point decision,
  verified the hypotheses of the theorem used from the file alone. Generator and checker are tested
  by `lake test` (§4).
- **Relative certificates at `r_c`** establish, through Theorem 4.2 of the combined note (refereed
  for `n = 5` in
  [`proofs/referee-report-sharp-lower-bound-combined.md`](proofs/referee-report-sharp-lower-bound-combined.md),
  correct after minor fixes; the general-`n` form replaces 5 by `n` in Step 2, giving `1 + 20nF`,
  and is refereed correct in
  [`proofs/referee-report-relative-certificates.md`](proofs/referee-report-relative-certificates.md)),
  the uniform bound on window-avoiding chains (Theorem 5.2 there) for the windows marked VALID:
  for those windows the note's Theorem 5.2 does not depend on floating-point ordering. (R-bulk) and (R-core) remain open; a relative certificate says
  nothing about finiteness at any particular `r < r_c` by itself.
- **Finiteness ranges** in §10 rest on the refereed certificate theorem where (C1)–(C4) were
  checked, and on Theorem H (§9; proved here, refereed correct after minor fixes; it is
  Theorem 4.2 with `W = ∅`) for the ranges ending in an open interval; §8 on the
  interval-of-validity argument (proved here, refereed correct), with the arcs also re-checked
  just below the event. The `n = 8` row rests on the symmetric unfolding of §§2, 7 (refereed
  correct); during refereeing its file was regenerated byte for byte and accepted again by the
  relative checker, which is the only checker that has read it.
- **Not established by a proof.** The generator and the checkers are tested programs, not
  kernel-checked proofs; their correctness rests on the arguments in their docstrings, on the
  tests, and on the Lean compiler and runtime (and, for the generator's float filter, on IEEE 754
  arithmetic). The link between the checker's acceptance and the theorems' hypotheses is by
  inspection of the definitions. Theorem 4.2, Theorem H and the §8 argument are proved and refereed
  on paper only; none has a Lean counterpart, so the certified ranges are proved modulo the
  computation. The face count `F`, and hence the constant
  `β_W = 1 + 20nF`, was not computed: it
  needs every crossing of two arcs of `K'` (a quadratic enumeration with exact identification of
  points on three or more circles), and no conclusion here uses its value, only its finiteness.
- **Large files.** Only the small certificates are in the repository; the others were written to
  a scratch directory and are recorded by SHA-256 of the file exactly as written. Every command is
  deterministic, so each file is reproduced by the command given with its table.

**Referee verdicts** (from
[`proofs/referee-report-relative-certificates.md`](proofs/referee-report-relative-certificates.md),
whose fixes are applied in this note):

| claim | verdict |
|---|---|
| §2 critical points, window disjointness by the corner bound, items 1–7 of "What the checker verifies" | correct; critical-point counts reproduced |
| §2 symmetric mode (canonical circles, stabiliser invariance, conjugation argument) | correct |
| §2 general constant `1 + 20nF` | correct |
| §2 no floating-point decision in the checker; shared code | correct (shared code listed precisely in §2) |
| §3 readings of Theorem 4.2 | correct |
| §5 Table 5.1 | rows 1–3 reproduced; rows 4–8 not re-run |
| §6 `n = 8, 10, 12` relative certificates | `n = 8` `(−4,0,4,−4)`, `n = 10` `(−6,2,4,−6)`, `n = 12` `(−6,5,1,−4)` and `(−4,4,2,−5)` reproduced; the others not re-run |
| §7 `n = 8`, `δ = 547/25000` | reproduced: regenerated byte for byte, accepted by the checker, (C3) and (C4) hold |
| §8 interval-of-validity argument | correct; the `n = 12` and `n = 10` results reproduced |
| §9 Theorem H | correct after minor fixes |
| §9 hybrid certificate: validity via Theorem H | correct after a wording fix |
| §9 where the relative certificate would enter | heuristic; motivation only |
| §9 prototype measurements | not checkable: the prototype is not in the repository |
| §10 best certified radius per `n` | consistent with what was reproduced |

Not checked by the referee: Table 5.1 rows 4–9, `n = 10` `(−5,3,1,−4)`, `n = 12` `(−5,4,1,−2)` and
`(−3,1,2,−3)`, and the `n = 12`, `δ = 1/250` closure.
