# Two-Disk Compound Symmetry Groups

Research on the two-disk systems GG_n(r) of the paper

> R. A. Hearn, W. Kretschmer, T. Rokicki, B. Streeter, E. Vergo,
> *Two-Disk Compound Symmetry Groups*, arXiv:2302.12950 ([`2302.12950v1.pdf`](2302.12950v1.pdf)).

Two closed disks of radius r are centred at −1 and 1 in the plane. One generator rotates the left
disk by 2π/n and fixes everything outside it; the other does the same for the right disk. GG_n(r) is
the group they generate. The paper shows that it is infinite for some r exactly when n ∉ {2, 3, 4, 6},
and computes the critical radius r_c(n) at which it first becomes infinite.

This repository has two parts: a Lean 4 / Mathlib formalization, and research notes.

## Research questions

1. Prove, and formalize, the half of Theorem 1 that the paper omits (finiteness for n ∈ {2, 3, 4, 6})
   and a boundary-contact theorem at the critical radius.
2. Explain the closed forms of r_c(n) for n = 5, 8, 10, 12 through the units of ℚ(ζ_n)⁺, and test
   whether unit rank 2 explains the broken self-similarity seen for n = 7.
3. Decide whether the large-n entries of the paper's critical-radius table are true critical radii or
   the onset of very large finite orbits.
4. Build an exact orbit engine (disk membership decided exactly in ℤ[ζ_n]) to confirm the numerical
   findings.
5. Compare compound symmetry with analytic continuation: the analytic threshold r_A against r_c.

[`notes/overview.md`](notes/overview.md) sets these out in full.

## Layout

| Path | Contents |
|---|---|
| `TDCSG/` | Lean sources (`TDCSG.lean` is the root module) |
| `notes/` | Research notes in Markdown: [`overview.md`](notes/overview.md), [`arithmetic.md`](notes/arithmetic.md), [`analytic-continuation.md`](notes/analytic-continuation.md), [`experiments.md`](notes/experiments.md) |
| `notes/proofs/` | Written proofs of results intended for formalization |
| `2302.12950v1.pdf` | The paper |

## Building

The project uses Lean `v4.35.0` (see `lean-toolchain`) and Mathlib at revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` (see `lakefile.toml`). With
[elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get   # download the prebuilt Mathlib (large; skip if .lake/packages is already populated)
lake build
```

## Status of results

The notes label every claim [proved], [computed], [classical], [conjecture] or [analogy].

- **Proved in Lean**, in `TDCSG/Basic.lean`, with no `sorry` and only the standard axioms: the
  definitions of the two disks and the two generators, and that each generator maps its disk to
  itself, has order dividing n (for n ≠ 0), and is a bijection of ℂ. Nothing from the paper's
  theorems is formalized yet.
- **Written proofs** (not refereed): the omitted half of Theorem 1 and the boundary-contact theorem.
  Sketches are in [`notes/analytic-continuation.md`](notes/analytic-continuation.md) and
  [`notes/arithmetic.md`](notes/arithmetic.md); full write-ups go in `notes/proofs/`.
- **Computed**: the baseline r_c(n) ≥ |2 − ζ_n| against the paper's table, the units governing orbit
  growth for n = 5, 8, 10, 12, the n ≡ 4 (mod 8) second threshold, and the absence of class-number or
  L-value correlations. See [`notes/experiments.md`](notes/experiments.md).
- **Conjectures**: the rank conjecture (self-similarity group = cyclotomic units), r_c(n)² ∈ ℚ(ζ_n)⁺
  for all n, complex dimensions of the critical fractal, and r_A < r_c.

**The computed numbers are preliminary.** They come from exploratory Python scripts, not part of this
repository, that stored orbit points exactly in ℤ[ζ_n] but tested membership in the closed disks in
floating point (tolerance 1e-12). Results at exact thresholds depend on that test. They are to be
re-checked with an exact engine.

## Licence and authors

Apache License 2.0; see [`LICENSE`](LICENSE). Authors: Eric Vergo and Claude (Anthropic).
