/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import TDCSG.CriticalRadius.Basic

/-!
# The cut-set certificate for finiteness

This file states the cut-set finiteness certificate, Theorem 4.2 of
`notes/proofs/critical-radius-n5.md` (restated as Theorem 3.1 of `critical-radius-n8.md` and
used for `n = 12`), as a proposition `TDCSG.CutSetCertificate n`. It is **not proved** here.
The finiteness results on an initial range of radii (Theorem B of those notes) combine it with
large external computations, which are also not formalized; they are recorded as propositions
`TDCSG.ExistsCertificate n r`.

What is proved is the reduction: the certificate theorem and a certificate at a radius `r₀ > 1`
give finiteness for every `r ≤ r₀` (by group monotonicity) and hence the lower bound
`r₀ ≤ criticalRadius n`.

## Main definitions

* `TDCSG.Arc`: a closed arc of a circle, by its centre and two angles.
* `TDCSG.Certificate n r arcs`: conditions (C1)–(C4) for the union `K` of the arcs `arcs` of
  circles of radius `r`.
* `TDCSG.CutSetCertificate n`: the certificate theorem, as a proposition.
* `TDCSG.ExistsCertificate n r`: a certificate exists at radius `r`, as a proposition.

## Main statements

* `TDCSG.finite_GG_of_certificate`: the certificate theorem and a certificate at `r₀` give
  finiteness for all `r ≤ r₀`.
* `TDCSG.le_criticalRadius_of_certificate`: they give `r₀ ≤ criticalRadius n`.

## Implementation notes

Condition (C4) of the written statement speaks of maximal arcs of `K`. It is formalized in the
form that the certificate checkers verify and the proof uses: wherever a carrying circle `C` of
`K`, other than the boundary circle `∂D_p`, meets `∂D_p` at a point `x` of `K`, the part of `C`
inside `D_p` near `x` lies in `K`. Condition (C3), non-tangency of a circle of radius `r` about
`c ≠ p` to the circle of radius `r` about `p`, is `dist c p ≠ 2 r`. The hypotheses `1 < r` and
non-degenerate arcs are those of `critical-radius-n8.md`, Theorem 3.1.
-/

@[expose] public section

open Complex Metric Equiv
open scoped Real

namespace TDCSG

/-- A closed arc of a circle, given by its centre and the angles `θ₁ ≤ θ₂` of its end points,
run through counterclockwise. -/
structure Arc where
  /-- The centre of the carrying circle. -/
  center : ℂ
  /-- The angle of the initial end point. -/
  θ₁ : ℝ
  /-- The angle of the final end point. -/
  θ₂ : ℝ

namespace Arc

/-- The points of the arc on the circle of radius `r`. -/
def carrier (r : ℝ) (α : Arc) : Set ℂ :=
  {z | ∃ θ ∈ Set.Icc α.θ₁ α.θ₂, z = α.center + r * exp (θ * I)}

/-- The arc is non-degenerate and at most a full circle. -/
def NonDegenerate (α : Arc) : Prop := α.θ₁ < α.θ₂ ∧ α.θ₂ ≤ α.θ₁ + 2 * π

end Arc

/-- The union of the arcs in a list, on circles of radius `r`. -/
def arcUnion (r : ℝ) (arcs : List Arc) : Set ℂ := ⋃ α ∈ arcs, α.carrier r

/-- Conditions (C1)–(C4) of the cut-set certificate for the union `K` of the arcs `arcs`, all on
circles of radius `r`:
* (C1) both boundary circles lie in `K`;
* (C2) `K` is mapped into itself by `a`, `a⁻¹`, `b` and `b⁻¹`;
* (C3) no carrying circle other than a boundary circle is tangent to that boundary circle;
* (C4) where a carrying circle `C ≠ ∂D_p` meets `∂D_p` in a point of the arc, the part of `C`
  inside `D_p` near that point lies in `K`. -/
def Certificate (n : ℕ) (r : ℝ) (arcs : List Arc) : Prop :=
  (∀ α ∈ arcs, α.NonDegenerate) ∧
  sphere leftCenter r ∪ sphere rightCenter r ⊆ arcUnion r arcs ∧
  (permA n r '' arcUnion r arcs ⊆ arcUnion r arcs ∧
    (permA n r)⁻¹ '' arcUnion r arcs ⊆ arcUnion r arcs ∧
    permB n r '' arcUnion r arcs ⊆ arcUnion r arcs ∧
    (permB n r)⁻¹ '' arcUnion r arcs ⊆ arcUnion r arcs) ∧
  (∀ α ∈ arcs, ∀ p ∈ ({leftCenter, rightCenter} : Set ℂ), α.center ≠ p →
    dist α.center p ≠ 2 * r) ∧
  (∀ α ∈ arcs, ∀ p ∈ ({leftCenter, rightCenter} : Set ℂ), α.center ≠ p →
    ∀ x ∈ α.carrier r, dist x p = r →
      ∃ ε > 0, ∀ y ∈ sphere α.center r, dist y x < ε → y ∈ closedBall p r →
        y ∈ arcUnion r arcs)

/-- **Not proved.** The cut-set certificate theorem (`critical-radius-n5.md`, Theorem 4.2;
`critical-radius-n8.md`, Theorem 3.1): for `r > 1`, a finite union of non-degenerate closed
arcs of circles of radius `r` satisfying (C1)–(C4) forces `GG n n r r` to be finite. -/
def CutSetCertificate (n : ℕ) : Prop :=
  ∀ r : ℝ, 1 < r → ∀ arcs : List Arc, Certificate n r arcs → Finite (GG n n r r)

/-- **Not proved.** A cut-set certificate exists at radius `r`. For `(n, r²)` equal to
`(5, 3 + φ - 1/10)`, `(8, 10 - 5√2 - 1/7)` and `(12, 40 - 22√3 - 1/20)` this is the content of
the external computations of the written notes, which are not formalized. -/
def ExistsCertificate (n : ℕ) (r : ℝ) : Prop :=
  ∃ arcs : List Arc, Certificate n r arcs

/-- The certificate theorem and a certificate at `r₀ > 1` give finiteness of the group for
every radius `r ≤ r₀`. -/
theorem finite_GG_of_certificate {n : ℕ} (hthm : CutSetCertificate n) {r₀ : ℝ} (h₀ : 1 < r₀)
    (hcert : ExistsCertificate n r₀) {r : ℝ} (hr : r ≤ r₀) : Finite (GG n n r r) := by
  obtain ⟨arcs, h⟩ := hcert
  exact finite_GG_of_le n n hr hr (hthm r₀ h₀ arcs h)

/-- If the group is finite for every radius `r ≤ r₀` and infinite for some radius, then
`r₀ ≤ criticalRadius n`. -/
theorem le_criticalRadius_of_forall_finite {n : ℕ} (hne : (infiniteRadii n).Nonempty) {r₀ : ℝ}
    (h : ∀ r ≤ r₀, Finite (GG n n r r)) : r₀ ≤ criticalRadius n := by
  refine le_csInf hne fun r hr ↦ ?_
  by_contra hlt
  exact not_finite_iff_infinite.2 hr (h r (not_le.1 hlt).le)

/-- The certificate theorem and a certificate at `r₀ > 1` give `r₀ ≤ criticalRadius n`, provided
the group is infinite for some radius. -/
theorem le_criticalRadius_of_certificate {n : ℕ} (hne : (infiniteRadii n).Nonempty)
    (hthm : CutSetCertificate n) {r₀ : ℝ} (h₀ : 1 < r₀) (hcert : ExistsCertificate n r₀) :
    r₀ ≤ criticalRadius n :=
  le_criticalRadius_of_forall_finite hne fun _ hr ↦ finite_GG_of_certificate hthm h₀ hcert hr

end TDCSG

end
