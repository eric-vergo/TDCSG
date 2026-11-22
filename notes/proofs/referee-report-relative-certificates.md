# Referee report: `relative-certificates.md`

Referee: Claude (independent of the authoring agent)

Subject: the note "Relative certificates at the critical radius, and float-free certified
ranges" (`../relative-certificates.md`, commit `0a43d31`), together with the engine modules
it describes (`TDCSGCompute/RelCheck.lean`, `RelClosure.lean`, `Validity.lean`, the new
`CircleCtx.diskSign` in `CirclePoint.lean`, and the commands `critical-points`,
`certify-relative`, `check-relative-certificate` and `validity-interval` in `Main.lean`).
Companions consulted: `sharp-lower-bound-combined.md` §§3–5 (Lemmas 3.3, 3.4,
Definition 4.1, Theorem 4.2, Corollary 4.3, Proposition 4.4) and its referee report
`referee-report-sharp-lower-bound-combined.md`; `../certificates.md`.

## Summary

The note does what it says. The relative checker verifies the hypotheses of Theorem 4.2 of the
combined note, in the literal (stronger) form of Definition 4.1. It proves the windows disjoint
with an exact argument, recomputes the critical points, and makes no floating-point decision.
The general constant `1 + 20nF` is derived correctly. Theorem H, the strict cut-set theorem, is
**correct after minor fixes**: its proof is complete in substance, and the fixes are about
wording and two implicit steps. The validity argument for the hybrid certificate in §9 is
correct. The paragraph on where the relative certificate "enters" is heuristic: the window radii
it combines do not match (issue 4). No conclusion depends on that paragraph.

I reproduced, with the engine built from the commit, every count and checksum I tried. A separate
exact closure program of my own reproduced the window `(0,2,−1,0)` closure arc for arc. The
issues I found are about status labelling and wording. One is a documentation inconsistency
about whether Theorem 4.2 was refereed (issue 1).

## 1. Verdicts

| claim | verdict |
|---|---|
| §2 critical points (counts 38/10, 32/8, 38/10, 48/12; trace-form box) | **correct**; reproduced |
| §2 window disjointness by the corner bound (farthest point of `W₀` is a corner) | **correct** |
| §2 "What the checker verifies", items 1–7, and (K1)–(K3) ⇒ (R1), (R2) | **correct** (checked against `RelCheck.lean`) |
| §2 symmetric mode (canonical circles, stabiliser invariance, conjugation argument) | **correct** |
| §2 general constant `1 + 20nF` | **correct**: `1 + 4(nF + 4nF)`; for `n = 5` it is `1 + 100F`, with `100 = 4 × 25` |
| §2 "no floating-point decision" in the checker; prefilter | **correct**: the checker's prefilter `farFrom` uses integer ball arithmetic and keeps the window when undecided |
| §2 "shares only the exact layer" | **correct, with a precise list** (issue 6) |
| §3 readings of Theorem 4.2 (items 1–7) | **correct**; item 3 is the reading the checker needs, and it holds because listed arcs on a circle are disjoint and non-touching |
| §5 Table 5.1 reproduction (rows 1–8) | rows 1–3 **reproduced** (counts, image counts, SHA-256); rows 4–8 not re-run |
| §6 `n = 8, 10, 12` relative certificates | `n = 8` `(−4,0,4,−4)`, `n = 10` `(−6,2,4,−6)`, `n = 12` `(−6,5,1,−4)` and `(−4,4,2,−5)` **reproduced** (counts, image counts, SHA-256); others not re-run |
| §7 `n = 8`, `δ = 547/25000`, window-free symmetric certificate | **reproduced**: regenerated (SHA-256 `4a7c18de…894b6a` equal), checker VALID with 10 869 666 images, (C3), (C4) hold with 35 543 endpoints |
| §8 interval-of-validity argument | **correct**; the "coincident at start ⇒ no extension" rule is implemented (exit code 3) |
| §8 results for `n = 12`, `1/180` and `n = 10`, `1/47` | **reproduced**: same pair and disk-event counts, same least events (`r_c² − ρ₁ ≈ 0.0055543`, `0.0212735`), moved files with the recorded SHA-256 prefixes and accepted by `check-certificate` |
| §9 Theorem H | **correct after minor fixes** (issues 2, 3) |
| §9 hybrid certificate: validity via Theorem H | **correct after a wording fix** (issue 3) |
| §9 "where the relative certificate enters" | **heuristic; window mismatch** (issue 4) |
| §9 measured savings of the prototype | **not checkable**: the prototype is not in the repository (issue 7) |
| §10 best certified radius per `n` | **consistent** with what was reproduced; labels correct |
| §11 status statements | **one inconsistency** (issue 1) |

## 2. The checker against Theorem 4.2

I read `checkRelative` and `RelChecker.*` line by line.

- **Critical points.** `critPoints` bounds each coefficient by `x_k² ≤ Tr(r²)·(G⁻¹)_kk`. This is
  Cauchy–Schwarz for the positive definite trace form. `(G⁻¹)_kk` is computed as
  `det(minor_kk)/det G` with exact rationals, and `b = ⌊√b2⌋` exactly. Every box vector is tested
  by the exact norm identity `q·|x|² = R`. Both `±1` translates are collected, and the listed set
  must equal the recomputed one, with no duplicates. This is more than Theorem 4.2 needs (the
  theorem holds for any finite family of disjoint compact convex windows), but it is what
  Corollary 4.3's use requires.
- **Windows.** `|w| < r` is checked by an exact sign. Corners are the intersection points of two
  shape circles that lie in every other shape disk; every pair of shape circles must cross. The
  claim that the farthest point of `W₀` from `0` is a corner holds. The farthest point of `C(v)`
  from `0`, at distance `|v| + r`, lies at distance `2|v| + r > r` from `−v`, so it is not on
  `∂W₀`. Along `C(v)` the distance to `0` has one maximum and one minimum, so on a boundary arc
  avoiding the maximum it peaks at an endpoint, which is a corner. Disjointness of `W_P`, `W_Q`
  then follows from `|P − Q|² > 4|x|²` for every corner, which is one exact `diskSign` per corner
  and pair.
- **(K2)** covers `∂W`. For each window circle `C(P+v)`, the boundary piece is the intersection
  of its closed arcs inside the other three disks. Each of these arcs is shorter than `π`, so the
  intersection is connected, and the checker throws otherwise.
- **(K3)** for each listed maximal arc `α` on `C(c)`, `p = ±1` with `c ≠ p` crossing, and
  `k = ±1`:
  - `α ∩ D_p` is computed by `clip`.
  - The holes are `C(c) ∩ W_P` for each window not excluded by the certified prefilter. A hole is
    the intersection of four closed arcs. It is empty if `c` is a window centre, if some window
    circle does not cross `C(c)`, or if the intersection has no interior.
  - `minusHoles` returns the closed, non-degenerate pieces between holes.
  - Each image must lie in one listed arc, moved to its canonical circle in symmetric mode.

  This is Definition 4.1(2) for the maximal arcs, in the literal form (the whole image must lie
  in `K'`, including any part of it inside `int W`). By §3 item 3 the maximal arcs suffice: a
  non-degenerate arc contained in `K'` lies in one maximal arc, because the maximal arcs on a
  circle are separated by gaps of positive length, which finitely many points of other circles
  cannot fill.
- **Tangent circles and `c = p`** are handled as the note says.
- **Prefilter.** `farFrom` decides `| |c − P| − r | > ρ̄` with integer balls. `ρ̄ = m/2¹⁶` is
  verified exactly to exceed `|x|` for every corner, and an undecided case keeps the window. If
  the prefilter skips a window, `C(c)` misses `D̄(P, ρ̄) ⊇ W_P`.
- **Symmetric mode.**
  - Every listed circle must be canonical.
  - The arcs on a circle must be invariant under its stabiliser. Without this, `K' ∩ C(c)` could
    be strictly larger than the listed arcs, and the extra arcs would go unchecked.
  - Queries are moved to the canonical circle by the symmetry that achieves the minimum. The
    reflections exchange endpoints and flip sides, which is correct for orientation-reversing
    maps.
  - The deduction for the non-canonical images `g(α)` is the conjugation argument of §2, which
    is valid because `W`, `D_1 ∪ D_2` and the set of critical points are invariant.

I found no hypothesis of Theorem 4.2 that the checker omits, and no decision taken in floating
point.

## 3. Theorem H, line by line

*Statement.* Let `M` be a finite union of non-degenerate closed arcs with `∂D_1 ∪ ∂D_2 ⊆ M`, such
that for every arc `α` of `M`, every `S` and every non-degenerate component `κ` of `α ∩ D_S`,
`S(κ) ⊆ M`. Then every strict orbit at `r` has at most `nF` points, and `GG_n(r')` is finite for
`r' < r`.

1. "Faces lie inside `int D_S` or outside `D_S`": a face is connected, open and disjoint from
   `∂D_S ⊆ M`. **Correct.**
2. "If `X` is a face in `int D_S` and `y ∈ S(X) ∩ M`, then `y ∈ int D_S`": `S` preserves
   `int D_S`. **Correct.** "So `y` lies in a non-degenerate component of `α ∩ D_S` for an arc
   `α ∋ y`": any arc of `M` through `y` meets the open disk in a neighbourhood of `y`.
   **Correct.** The hypothesis for `S⁻¹`, which acts on the same disk, gives
   `S⁻¹(y) ∈ M ∩ X = ∅`. **Correct.**
3. "So `S(X)` is a face": the argument shows only that `S(X)` is contained in one face `Y`. The
   reverse inclusion needs the same argument for `S⁻¹` on `Y`: `Y` meets `int D_S`, so
   `Y ⊆ int D_S`, so `S⁻¹(Y)` lies in a face, which contains `X`, hence `S⁻¹(Y) ⊆ X`. This step
   is implicit. **Minor fix** (issue 2).
4. Counting.
   - A generic start (Lemma 3.4 with `W = ∅`, `K' = M`) has all its chain points in faces.
   - The chain maps are `z ↦ ζ^j z + t` with `t ∈ Λ`, because `±1 ∈ Λ`.
   - Each strict step is taken at a point of a face inside the open disk, so by item 3 the
     composite maps the face `X₀` of `x` onto the face of the endpoint.
   - The isometry is determined by `j` and the target face, since a bounded set is not invariant
     under a non-zero translation. This needs `X₀` bounded. If `x` is in the unbounded face, no
     strict step applies and the orbit is `{x}`, with `1 ≤ nF` because `F ≥ 1`.

   **Correct**, with the unbounded case to be stated (issue 2).
5. "By Lemma 3.4 so does every strict orbit": openness of strict-chain conditions and of the
   distinctness of finitely many endpoints. **Correct.**
6. "A chain at `r' < r` is a strict chain at `r` after deleting trivial steps": this is
   Lemma 3.3 of the combined note with `r_c` replaced by `r`, and its proof does not use
   criticality. Uniformly bounded orbits give a finite group (`theorem1-converse.md`,
   Proposition 4.2). **Correct.**
7. The quantifier "every arc `α` of `M`" should be read, as in §3 item 3, as "every arc of a
   given finite family whose union is `M`". The proof uses only that each `y ∈ M ∩ int D_S` lies
   on a family arc. This reading is the one the hybrid argument needs, because there
   `M = L ∪ ⋃B` is given as a family (issue 3).

**Verdict: correct after minor fixes.** The bound `nF` is sharper than `1 + 20nF` at `W = ∅`.
The two bounds are consistent: Theorem 4.2's extra factors come from endpoints entering the
windows.

**Hybrid validity.** With `M = L ∪ ⋃B` as a family:

- An arc of some `B` has the components of `κ ∖ int W` mapped into `B`, because `B` is closed
  relative to `W`.
- Its part in `W` lies in arcs of `L`. The closed parts are covered, including isolated points
  on `∂W`. An isolated point of `κ ∖ int W` cannot be interior to `κ`, because `C(c) ∩ W_P` is
  connected and the windows are disjoint.
- Every `L` arc's components of `λ ∩ D_S` have their full images in the batch that processed
  them, which is part of `M`.
- `∂D_1 ∪ ∂D_2` is seeded.

So Theorem H applies. The proof is correct, provided the images of the batch's `L` arcs are
computed **without** clipping by `int W`, while only the transported closure is clipped. The text
says "sources clipped by int W" and then "whose full images", which reads as if both were
clipped (issue 3).

## 4. Issues

1. **Status of Theorem 4.2: inconsistent labelling (minor).** §11 says Theorem 4.2 is "a
   written, unrefereed proof", and that "Theorem 4.2 and Theorem H … neither is refereed".
   Theorem 4.2 (for `n = 5`) was refereed in `referee-report-sharp-lower-bound-combined.md`,
   verdict "correct after minor fixes", and the README cites that report.
   *Repair:* say "Theorem 4.2 (refereed for `n = 5`; the general-`n` form replaces 5 by `n` in
   Step 2, checked in this report)". Keep "not refereed" only for Theorem H and the §8 argument
   until this report is committed.
2. **Theorem H proof: two implicit steps (minor).** The step "`S(X)` is a face" should give the
   reverse inclusion, and the unbounded-face start should be stated (§3 items 3, 4).
   *Repair:* add one sentence each.
3. **Theorem H quantifier and hybrid wording (minor).** Read "every arc of `M`" as "every arc of
   a finite family with union `M`". In the hybrid paragraph, say that the batch's `L` arcs are
   mapped in full and that only the transported pieces are clipped by `int W`.
4. **"Where the relative certificate enters": window mismatch (minor; heuristic only).** The
   hybrid windows are built from disks of radius `r` (`W(r)`), but Proposition 4.4 concerns
   chains avoiding the windows `W(r_c)` of the relative certificate. Since
   `W(r) ⊆ W(r_c)`, a chain that avoids `W(r)` need not avoid `W(r_c)`, so "a batch is contained
   in the images under `G_W` of its seeds" does not follow as written. The claim that
   Proposition 4.4 "applies verbatim to strict chains" is also asserted without proof.
   *Repair:* use the `r_c`-windows in the hybrid. Theorem H does not care about the window
   shape, and Definition 4.1 does not use the window radius. Otherwise, label the paragraph as
   motivation.
5. **Validity interval: one point to state (cosmetic).** The module docstring says the interval
   "is reported empty" if two adjacent points coincide at `ρ₀`. The code reports "no extension"
   with exit code 3, which is right. The note's §8 omits this case. *Repair:* one sentence in §8.
6. **"Shares only the exact layer" (cosmetic, precision).** The checker shares with the generator
   `Ball`, `Field`, `Tower`, `Disk` and `CirclePoint`, including `diskSign`, `gapSign`, `rot`,
   `rotSym` and `validSym`. It shares with the ordinary checker `parseVec`, `parseSym`, `mkPt`,
   `cmp`, `clip`, `covered`, `posCmp`, `inside` and `msort`. The generator (`RelClosure` →
   `Closure` → `CircleFilter`) does not import `CertCheck`. A defect in `diskSign` would be
   common to both, so the window geometry is not independently checked inside the repository.
   The `lake test` comparison against floating point, and my separate closure (§5), cover it
   for the tested cases.
7. **§9 measurements are not reproducible (minor).** The prototype is not in the repository, so
   the table of batch sizes cannot be checked. *Repair:* say so next to the table, or commit the
   prototype.
8. **Unicode minus signs in shapes (cosmetic).** The tables write shapes with U+2212
   (`5,−1,4,0`), and `--window 5,−1,4,0` copied from them fails with "cannot parse the integer
   −1". The failure is safe. *Repair:* use ASCII hyphens in the shape columns, or give literal
   commands.
9. **The generator's `missesBall` (informational).** It compares `t.v − t.e > ρ` in floating
   point without bounding the rounding of that last subtraction. This affects only the
   generator: a wrongly skipped window would make the closure larger, and the checker would
   still decide exactly. No change is needed for soundness.

## 5. What was reproduced

With the engine built from `0a43d31` (fresh clone, Mathlib provisioned locally, `lake build`
2352 jobs, no warnings; `lake test` 4642 passed, 0 failed):

- `critical-points` for `n = 5, 8, 10, 12`: 38/10, 32/8, 38/10, 48/12 critical points/classes;
  20, 16, 20, 24 lattice elements.
- Committed relative certificates: regenerated byte for byte (SHA-256 equal to `SHA256SUMS`) and
  accepted. Row 1 full storage was also regenerated (SHA-256 equal to the note's).
- Table 5.1 rows 1–3, full storage: counts, image counts (51 828, 2 023 476, 3 192 528), coincidence locations and SHA-256 all as in the note.
- `n = 8` `(−4,0,4,−4)`, `n = 10` `(−6,2,4,−6)`, `n = 12` `(−6,5,1,−4)` and `(−4,4,2,−5)`:
  counts, images and SHA-256 as in the note.
- `n = 8`, `δ = 547/25000` window-free symmetric closure: regenerated (4 996 s, 2.36 GB),
  SHA-256 equal to the note's, and **VALID** with (C1)–(C4).
- `n = 12`, `δ = 1/180` and `n = 10`, `δ = 1/47` ordinary certificates: regenerated (SHA-256 as
  in `../certificates.md`); `validity-interval` reproduced the events; the moved files had the
  recorded SHA-256 prefixes and were accepted. The `n = 10` file at `ρ₀` was also re-checked.
- An independent exact closure also reproduced window `(5,−1,4,0)` (row 2) arc for arc:
  452 153 circles and 808 444 maximal arcs.
- Tampering:
  - Rejected: a deleted arc (two variants), a flipped or replaced endpoint, a smaller window, a
    dropped critical point, a dropped boundary circle, and five of six endpoint moves on lone
    arcs in each storage mode.
  - Accepted, correctly: two endpoint flips. Each **enlarged** an arc by a piece that lies
    outside both disks or inside `int W`, so the enlarged set is still a restricted closure. I
    confirmed this numerically by sampling.
- Independent exact closure (my own Python, integers in `ℤ[ζ₅]`, exact concurrency test for
  every coincidence, mpmath positions with a 10⁻³⁵ tie threshold) for `w = (0,2,−1,0)`:
  13 692 circles and 22 230 maximal arcs, identical **arc for arc** to the certificate on all
  13 690 non-boundary circles. 217 exact equalities were met, and no unresolved near-tie.

## 6. What was not checked

- Table 5.1 rows 4–9, `n = 10` `(−5,3,1,−4)`, `n = 12` `(−5,4,1,−2)` and `(−3,1,2,−3)`, and
  the unchecked `n = 12`, `δ = 1/250` closure.
- The prototype measurements of §9.
- Theorem H and the §8 argument are refereed here on paper only. The correctness of the checker
  rests on inspection, tests and the Lean compiler and runtime, not on a kernel proof.
