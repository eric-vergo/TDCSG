/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude, OpenAI GPT-6.2 Astra
-/
module

public import TDCSG.CriticalRadius.Eight
public import TDCSG.CriticalRadius.Ten
public import TDCSG.CriticalRadius.Twelve

/-!
# Critical radii: statements

This file collects, in compact form, what is proved about the critical radius
`TDCSG.criticalRadius n` of the equal-radius family `GG n n r r` for `n = 8, 10, 12`. The
written sources are `notes/proofs/critical-radius-n8.md`, `critical-radius-n10.md` and
`critical-radius-n12.md`. The exact value for `n = 5` is
`TDCSG.CriticalRadius.criticalRadius_five`, and the properties of the critical radius for every
`n` are in `TDCSG.CriticalRadius.Basic`.

## Main statements

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

Whether the critical radii for `n = 8, 10, 12` equal these upper bounds is open.
-/

@[expose] public section

open Complex Metric
open scoped Real goldenRatio

namespace TDCSG.CriticalRadius

/-! ### `n = 10` -/

/-- `GG₁₀(r)` is infinite for every `r ≥ √(4 - φ)` (`critical-radius-n10.md`, Theorem A). -/
theorem infinite_GG_ten {r : ℝ} (hr : √(4 - φ) ≤ r) : Infinite (GG 10 10 r r) :=
  Ten.infinite_GG hr

/-- For every `r ≥ √(4 - φ)` the orbit of `0` under `GG₁₀(r)` is infinite. -/
theorem infinite_orbit_zero_ten {r : ℝ} (hr : √(4 - φ) ≤ r) : (orbit 10 10 r r 0).Infinite :=
  Ten.infinite_orbit_zero hr

/-- The critical radius for `n = 10` is at most `√(4 - φ)`. -/
theorem criticalRadius_ten_le : criticalRadius 10 ≤ √(4 - φ) :=
  Ten.criticalRadius_le

/-- The critical radius for `n = 10` is at least `1`. -/
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

/-- The critical radius for `n = 8` is at most `√(10 - 5√2)`. -/
theorem criticalRadius_eight_le : criticalRadius 8 ≤ √(10 - 5 * √2) :=
  TDCSG.criticalRadius_le (infinite_GG_eight le_rfl)

/-- The critical radius for `n = 8` is at least `1`. -/
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

/-- The critical radius for `n = 12` is at most `√(40 - 22√3)`. -/
theorem criticalRadius_twelve_le : criticalRadius 12 ≤ √(40 - 22 * √3) :=
  TDCSG.criticalRadius_le (infinite_GG_twelve le_rfl)

/-- The critical radius for `n = 12` is at least `1`. -/
theorem one_le_criticalRadius_twelve : 1 ≤ criticalRadius 12 :=
  TDCSG.one_le_criticalRadius ⟨_, infinite_GG_twelve le_rfl⟩

end TDCSG.CriticalRadius

end
