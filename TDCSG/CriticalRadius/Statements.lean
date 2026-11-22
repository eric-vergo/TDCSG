/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import TDCSG.CriticalRadius.Certificate
public import TDCSG.CriticalRadius.Eight
public import TDCSG.CriticalRadius.Five
public import TDCSG.CriticalRadius.Ten
public import TDCSG.CriticalRadius.Twelve

/-!
# Critical radii: statements

This file collects, in compact form, what is known about the critical radius
`TDCSG.criticalRadius n` of the equal-radius family `GG n n r r` for `n = 5, 8, 10, 12`. The
written sources are `notes/proofs/critical-radius-n5.md`, `critical-radius-n8.md`,
`critical-radius-n10.md` and `critical-radius-n12.md`.

The declarations below include propositions used by later modules. The module
`TDCSG.CriticalRadius.FiveSharp` proves the fivefold closed form from these definitions.
The initial certificate ranges for orders eight and twelve rely on external computations.

## Proved

* `criticalRadius_five_le`, `infinite_GG_five`, `infinite_orbit_zero_five`: `GG₅(r)` is
  infinite for every `r ≥ √(3 + φ)`, through an infinite orbit of `0`; hence
  `1 ≤ criticalRadius 5 ≤ √(3 + φ)`.
* `criticalRadius_ten_le`, `infinite_GG_ten`, `infinite_orbit_zero_ten`: `GG₁₀(r)` is
  infinite for every `r ≥ √(4 - φ)`, through an infinite orbit of `0`; hence
  `1 ≤ criticalRadius 10 ≤ √(4 - φ)`.
* `mem_orbit_pStar_eight_pow`, `infinite_orbit_pStar_eight`, `infinite_GG_eight`,
  `criticalRadius_eight_le`: for every `r ≥ √(10 - 5√2)` the orbit of `p*` under `GG₈(r)`
  contains `p* + 4 i (√2 - 1)^(k+1)` for all `k`, so `GG₈(r)` is infinite and
  `1 ≤ criticalRadius 8 ≤ √(10 - 5√2)`.
* `mem_orbit_pStar_twelve_pow`, `infinite_orbit_pStar_twelve`, `infinite_GG_twelve`,
  `criticalRadius_twelve_le`: for every `r ≥ √(40 - 22√3)` the orbit of `p*` under `GG₁₂(r)`
  contains `p* + 2 (2 - √3)^(k+2) V` for all `k`, so `GG₁₂(r)` is infinite and
  `1 ≤ criticalRadius 12 ≤ √(40 - 22√3)`.
* `pStar_eight_mem_sphere`, `mem_orbit_pStar_eight`; `pStar_twelve_mem_sphere`,
  `mem_orbit_pStar_twelve`: the critical points for `n = 8, 12` lie on the boundary circle at
  the conjectured critical radius, and the seed words reach the first point of their orbits.
* `finiteBelowFive_of_certificate`, `le_criticalRadius_five_of_finiteBelow` and their analogues
  for `n = 8, 12`: conditional theorems. The propositions `CutSetCertificate n` and
  `ExistsCertificate n r` imply `FiniteBelow…`, which implies the corresponding lower bound on
  the critical radius.
* `criticalRadiusEqFive_of_finiteBelowClosedFormFive`: finiteness below `√(3 + φ)` gives the
  exact value `criticalRadius 5 = √(3 + φ)`. The hypothesis and the equality are theorems
  `finiteBelowClosedFormFive` and `criticalRadius_five_eq` in `FiveSharp`.
* `infinite_GG_of_le`, `finite_GG_of_lt`, `infinite_GG_of_lt`, `finite_GG_of_lt_one`: the
  basic properties of the critical radius, for every `n`.

## Not proved (propositions)

* `CutSetCertificate n`, `ExistsCertificate n r` (in `TDCSG.CriticalRadius.Certificate`).
* `FiniteBelowEight`, `FiniteBelowTwelve`.
* `CriticalRadiusEqEight`, `CriticalRadiusEqTen`, `CriticalRadiusEqTwelve`: the open exact values.
-/

@[expose] public section

open Complex Metric
open scoped Real goldenRatio

namespace TDCSG.CriticalRadius

/-! ### Basic properties of the critical radius -/

/-- Infinitude of the group passes to larger radii. -/
theorem infinite_GG_of_le {n : ℕ} {r r' : ℝ} (h : r ≤ r') (hr : Infinite (GG n n r r)) :
    Infinite (GG n n r' r') :=
  TDCSG.infinite_GG_of_le h hr

/-- Below the critical radius the group is finite. -/
theorem finite_GG_of_lt {n : ℕ} {r : ℝ} (hr : r < criticalRadius n) : Finite (GG n n r r) :=
  TDCSG.finite_GG_of_lt_criticalRadius hr

/-- Above the critical radius the group is infinite, if it is infinite for some radius. -/
theorem infinite_GG_of_lt {n : ℕ} (hne : ∃ r, Infinite (GG n n r r)) {r : ℝ}
    (hr : criticalRadius n < r) : Infinite (GG n n r r) :=
  TDCSG.infinite_GG_of_criticalRadius_lt hne hr

/-- The group is finite for every radius below `1`. -/
theorem finite_GG_of_lt_one (n : ℕ) {r : ℝ} (hr : r < 1) : Finite (GG n n r r) :=
  TDCSG.finite_GG_of_lt_one n hr

/-! ### `n = 5` -/

/-- `GG₅(r)` is infinite for every `r ≥ √(3 + φ)` (`critical-radius-n5.md`, Theorem A). -/
theorem infinite_GG_five {r : ℝ} (hr : √(3 + φ) ≤ r) : Infinite (GG 5 5 r r) :=
  Five.infinite_GG hr

/-- For every `r ≥ √(3 + φ)` the orbit of `0` under `GG₅(r)` is infinite. -/
theorem infinite_orbit_zero_five {r : ℝ} (hr : √(3 + φ) ≤ r) : (orbit 5 5 r r 0).Infinite :=
  Five.infinite_orbit_zero hr

theorem criticalRadius_five_le : criticalRadius 5 ≤ √(3 + φ) :=
  Five.criticalRadius_le

theorem one_le_criticalRadius_five : 1 ≤ criticalRadius 5 :=
  TDCSG.one_le_criticalRadius ⟨_, Five.infinite_GG le_rfl⟩

/-! ### `n = 10` -/

/-- `GG₁₀(r)` is infinite for every `r ≥ √(4 - φ)` (`critical-radius-n10.md`, Theorem A). -/
theorem infinite_GG_ten {r : ℝ} (hr : √(4 - φ) ≤ r) : Infinite (GG 10 10 r r) :=
  Ten.infinite_GG hr

/-- For every `r ≥ √(4 - φ)` the orbit of `0` under `GG₁₀(r)` is infinite. -/
theorem infinite_orbit_zero_ten {r : ℝ} (hr : √(4 - φ) ≤ r) : (orbit 10 10 r r 0).Infinite :=
  Ten.infinite_orbit_zero hr

theorem criticalRadius_ten_le : criticalRadius 10 ≤ √(4 - φ) :=
  Ten.criticalRadius_le

theorem one_le_criticalRadius_ten : 1 ≤ criticalRadius 10 :=
  Ten.one_le_criticalRadius

/-! ### `n = 8` and `n = 12`: the critical points -/

/-- The critical point `p* = 1 - 2ζ + ζ² - ζ³` for `n = 8` lies on the boundary circle of the
left disk of radius `√(10 - 5√2)`. -/
theorem pStar_eight_mem_sphere : Eight.pStar ∈ sphere leftCenter √(10 - 5 * √2) :=
  Eight.pStar_mem_sphere

/-- For `r ≥ √(10 - 5√2)` the orbit of `p*` under `GG₈(r)` contains `p* + 4 (√2 - 1) i`. -/
theorem mem_orbit_pStar_eight {r : ℝ} (hr : √(10 - 5 * √2) ≤ r) :
    Eight.pStar + ((4 * (√2 - 1) : ℝ) : ℂ) * I ∈ orbit 8 8 r r Eight.pStar := by
  convert Eight.mem_orbit_pStar hr using 4
  ring

/-- The critical point `p* = (2 - √3)(1 - 2i)` for `n = 12` lies on the boundary circle of the
left disk of radius `√(40 - 22√3)`. -/
theorem pStar_twelve_mem_sphere : Twelve.pStar ∈ sphere leftCenter √(40 - 22 * √3) :=
  Twelve.pStar_mem_sphere

/-- For `r ≥ √(40 - 22√3)` the orbit of `p*` under `GG₁₂(r)` contains `p* + 2 (2 - √3)² V`,
with `V = ζ⁵ + ζ⁶`. -/
theorem mem_orbit_pStar_twelve {r : ℝ} (hr : √(40 - 22 * √3) ≤ r) :
    Twelve.pStar + ((2 * (2 - √3) ^ 2 : ℝ) : ℂ) * Twelve.chordDir ∈
      orbit 12 12 r r Twelve.pStar := by
  convert Twelve.mem_orbit_pStar hr using 4
  have : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination 2 * this

/-! ### `n = 8` and `n = 12`: infinitude -/

/-- `critical-radius-n8.md`, Theorem A, orbit form: for `r ≥ √(10 - 5√2)` the orbit of `p*`
under `GG₈(r)` contains `p* + 4 i (√2 - 1)^(k+1)` for every `k`. -/
theorem mem_orbit_pStar_eight_pow {r : ℝ} (hr : √(10 - 5 * √2) ≤ r) (k : ℕ) :
    Eight.pStar + ((4 * (√2 - 1) ^ (k + 1) : ℝ) : ℂ) * I ∈ orbit 8 8 r r Eight.pStar :=
  Eight.mem_orbit_pStar_pow hr k

/-- `critical-radius-n12.md`, Theorem A, orbit form: for `r ≥ √(40 - 22√3)` the orbit of `p*`
under `GG₁₂(r)` contains `p* + 2 (2 - √3)^(k+2) V` for every `k`. -/
theorem mem_orbit_pStar_twelve_pow {r : ℝ} (hr : √(40 - 22 * √3) ≤ r) (k : ℕ) :
    Twelve.pStar + ((2 * (2 - √3) ^ (k + 2) : ℝ) : ℂ) * Twelve.chordDir ∈
      orbit 12 12 r r Twelve.pStar :=
  Twelve.mem_orbit_pStar_pow hr k

/-- Points `p + c ε^k V` with `c V ≠ 0` and `0 < ε < 1` are pairwise distinct. -/
theorem injective_add_pow_mul {p V : ℂ} {c ε : ℝ} (hc : c ≠ 0) (hV : V ≠ 0) (h0 : 0 < ε)
    (h1 : ε < 1) (m : ℕ) : Function.Injective fun k : ℕ ↦ p + ((c * ε ^ (k + m) : ℝ) : ℂ) * V := by
  intro k l hkl
  have h := mul_right_cancel₀ hV (add_left_cancel hkl)
  have h' : ε ^ (k + m) = ε ^ (l + m) := by
    have := mul_left_cancel₀ hc (by exact_mod_cast h)
    exact this
  exact Nat.add_right_cancel ((pow_right_strictAnti₀ h0 h1).injective h')

/-- For every `r ≥ √(10 - 5√2)` the orbit of `p*` under `GG₈(r)` is infinite. -/
theorem infinite_orbit_pStar_eight {r : ℝ} (hr : √(10 - 5 * √2) ≤ r) :
    (orbit 8 8 r r Eight.pStar).Infinite := by
  have hs : 1 < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs' : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine Set.infinite_of_injective_forall_mem (injective_add_pow_mul (p := Eight.pStar) (c := 4)
    (ε := √2 - 1) (by norm_num) I_ne_zero (by linarith) (by linarith) 1) fun k ↦ ?_
  simpa using mem_orbit_pStar_eight_pow hr k

/-- `GG₈(r)` is infinite for every `r ≥ √(10 - 5√2)` (`critical-radius-n8.md`, Theorem A). -/
theorem infinite_GG_eight {r : ℝ} (hr : √(10 - 5 * √2) ≤ r) : Infinite (GG 8 8 r r) :=
  infinite_GG_of_infinite_orbit (infinite_orbit_pStar_eight hr)

theorem criticalRadius_eight_le : criticalRadius 8 ≤ √(10 - 5 * √2) :=
  TDCSG.criticalRadius_le (infinite_GG_eight le_rfl)

theorem one_le_criticalRadius_eight : 1 ≤ criticalRadius 8 :=
  TDCSG.one_le_criticalRadius ⟨_, infinite_GG_eight le_rfl⟩

/-- For every `r ≥ √(40 - 22√3)` the orbit of `p*` under `GG₁₂(r)` is infinite. -/
theorem infinite_orbit_pStar_twelve {r : ℝ} (hr : √(40 - 22 * √3) ≤ r) :
    (orbit 12 12 r r Twelve.pStar).Infinite := by
  have hs : 1 < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs' : √3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hV : Twelve.chordDir ≠ 0 := fun h ↦ by
    have := congrArg Complex.im h
    simp [Twelve.chordDir] at this
  refine Set.infinite_of_injective_forall_mem (injective_add_pow_mul (p := Twelve.pStar) (c := 2)
    (ε := 2 - √3) (by norm_num) hV (by linarith) (by linarith) 2) fun k ↦ ?_
  simpa using mem_orbit_pStar_twelve_pow hr k

/-- `GG₁₂(r)` is infinite for every `r ≥ √(40 - 22√3)` (`critical-radius-n12.md`, Theorem A). -/
theorem infinite_GG_twelve {r : ℝ} (hr : √(40 - 22 * √3) ≤ r) : Infinite (GG 12 12 r r) :=
  infinite_GG_of_infinite_orbit (infinite_orbit_pStar_twelve hr)

theorem criticalRadius_twelve_le : criticalRadius 12 ≤ √(40 - 22 * √3) :=
  TDCSG.criticalRadius_le (infinite_GG_twelve le_rfl)

theorem one_le_criticalRadius_twelve : 1 ≤ criticalRadius 12 :=
  TDCSG.one_le_criticalRadius ⟨_, infinite_GG_twelve le_rfl⟩

/-! ### Finiteness on an initial range -/

/-- The initial fivefold certificate range, also covered by the theorem
`finiteBelowClosedFormFive` in `FiveSharp`. -/
def FiniteBelowFive : Prop :=
  ∀ r : ℝ, r ≤ √(3 + φ - 1 / 10) → Finite (GG 5 5 r r)

/-- **Not proved.** `critical-radius-n8.md`, Theorem B: `GG₈(r)` is finite for every
`r ≤ √(10 - 5√2 - 1/7)`. -/
def FiniteBelowEight : Prop :=
  ∀ r : ℝ, r ≤ √(10 - 5 * √2 - 1 / 7) → Finite (GG 8 8 r r)

/-- **Not proved.** `critical-radius-n12.md`, Theorem B: `GG₁₂(r)` is finite for every
`r ≤ √(40 - 22√3 - 1/20)`. -/
def FiniteBelowTwelve : Prop :=
  ∀ r : ℝ, r ≤ √(40 - 22 * √3 - 1 / 20) → Finite (GG 12 12 r r)

theorem one_lt_sqrt_of_one_lt {x : ℝ} (hx : 1 < x) : 1 < √x := by
  rw [Real.lt_sqrt (by norm_num)]
  simpa using hx

/-- The certificate theorem and a certificate at `√(3 + φ - 1/10)` give Theorem B for
`n = 5`. -/
theorem finiteBelowFive_of_certificate (hthm : CutSetCertificate 5)
    (hcert : ExistsCertificate 5 √(3 + φ - 1 / 10)) : FiniteBelowFive :=
  fun _ hr ↦ finite_GG_of_certificate hthm
    (one_lt_sqrt_of_one_lt (by linarith [Real.one_lt_goldenRatio])) hcert hr

/-- The certificate theorem and a certificate at `√(10 - 5√2 - 1/7)` give Theorem B for
`n = 8`. -/
theorem finiteBelowEight_of_certificate (hthm : CutSetCertificate 8)
    (hcert : ExistsCertificate 8 √(10 - 5 * √2 - 1 / 7)) : FiniteBelowEight := by
  have hs : √2 < 1.5 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  exact fun _ hr ↦ finite_GG_of_certificate hthm (one_lt_sqrt_of_one_lt (by linarith)) hcert hr

/-- The certificate theorem and a certificate at `√(40 - 22√3 - 1/20)` give Theorem B for
`n = 12`. -/
theorem finiteBelowTwelve_of_certificate (hthm : CutSetCertificate 12)
    (hcert : ExistsCertificate 12 √(40 - 22 * √3 - 1 / 20)) : FiniteBelowTwelve := by
  have hs : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  exact fun _ hr ↦ finite_GG_of_certificate hthm (one_lt_sqrt_of_one_lt (by linarith)) hcert hr

/-- Theorem B for `n = 5` gives the lower bound `√(3 + φ - 1/10) ≤ criticalRadius 5`. -/
theorem le_criticalRadius_five_of_finiteBelow (h : FiniteBelowFive) :
    √(3 + φ - 1 / 10) ≤ criticalRadius 5 :=
  le_criticalRadius_of_forall_finite ⟨_, Five.infinite_GG le_rfl⟩ h

/-- Theorem B for `n = 8` gives the lower bound `√(10 - 5√2 - 1/7) ≤ criticalRadius 8`. -/
theorem le_criticalRadius_eight_of_finiteBelow (h : FiniteBelowEight) :
    √(10 - 5 * √2 - 1 / 7) ≤ criticalRadius 8 :=
  le_criticalRadius_of_forall_finite ⟨_, infinite_GG_eight le_rfl⟩ h

/-- Theorem B for `n = 12` gives the lower bound `√(40 - 22√3 - 1/20) ≤ criticalRadius 12`. -/
theorem le_criticalRadius_twelve_of_finiteBelow (h : FiniteBelowTwelve) :
    √(40 - 22 * √3 - 1 / 20) ≤ criticalRadius 12 :=
  le_criticalRadius_of_forall_finite ⟨_, infinite_GG_twelve le_rfl⟩ h

/-- Subcritical finiteness for fivefold rotations, proved in `FiveSharp`. -/
def FiniteBelowClosedFormFive : Prop :=
  ∀ r : ℝ, r < √(3 + φ) → Finite (GG 5 5 r r)

/-! ### Exact values of the critical radii -/

/-- The fivefold critical-radius equality, proved as `criticalRadius_five_eq` in `FiveSharp`. -/
def CriticalRadiusEqFive : Prop := criticalRadius 5 = √(3 + φ)

/-- Finiteness below the closed form `√(3 + φ)`, with the infinitude at and above it
(`infinite_GG_five`), gives the exact value of the critical radius. -/
theorem criticalRadiusEqFive_of_finiteBelowClosedFormFive (h : FiniteBelowClosedFormFive) :
    CriticalRadiusEqFive := by
  refine le_antisymm criticalRadius_five_le (le_csInf ⟨_, Five.infinite_GG le_rfl⟩ fun r hr ↦ ?_)
  by_contra hlt
  exact not_finite_iff_infinite.2 hr (h r (not_le.1 hlt))

/-- **Open.** The critical radius of `GG₈` is `√(10 - 5√2)`. -/
def CriticalRadiusEqEight : Prop := criticalRadius 8 = √(10 - 5 * √2)

/-- **Open.** The critical radius of `GG₁₀` is `√(4 - φ)`. -/
def CriticalRadiusEqTen : Prop := criticalRadius 10 = √(4 - φ)

/-- **Open.** The critical radius of `GG₁₂` is `√(40 - 22√3)`. -/
def CriticalRadiusEqTwelve : Prop := criticalRadius 12 = √(40 - 22 * √3)

end TDCSG.CriticalRadius

end
