/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Tactic.IntervalCases
public import TDCSG.Monotonicity

/-!
# Finiteness when `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}`

If `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}`, the two-disk compound symmetry group `TDCSG.GG n₁ n₂ r₁ r₂` is
finite for all radii. This is the direction of Theorem 1 of arXiv:2302.12950 that the paper
omits; the written proof is `notes/proofs/theorem1-converse.md`, Theorem 5.1.

## Main statements

* `TDCSG.lcm_mem_iff`: `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}` holds exactly when `n₁, n₂` both divide `4`
  or both divide `6`.
* `TDCSG.apply_eq_of_notMem_diskUnion`, `TDCSG.apply_mem_diskUnion`: every element of the group
  fixes the complement of the union of the disks and maps the union into itself.
* `TDCSG.exists_affine`: at each point, every element of the group acts as `z ↦ u * z + t` with
  `u`, `t` in a lattice `ℤ + ℤ η` closed under multiplication.
* `TDCSG.exists_encard_orbit_le`: under the arithmetic hypothesis the orbits are uniformly
  bounded.
* `TDCSG.finite_GG`: under the arithmetic hypothesis the group is finite.

## Implementation notes

The written proof works in the ring `ℤ[ω]`, `ω = exp (-2πi / lcm n₁ n₂)`. Here we use instead the
Gaussian integers `ℤ + ℤ i` when `n₁, n₂ ∣ 4`, and the Eisenstein integers `ℤ + ℤ ζ₆`,
`ζ₆ = exp (-2πi / 6)`, when `n₁, n₂ ∣ 6`. Each contains the corresponding `ℤ[ω]`, so the bound
on the translation parts is the same argument with a possibly larger, still finite, count.
-/

@[expose] public section

open Complex Metric Equiv
open scoped Real ComplexConjugate

namespace TDCSG

/-! ### Lattices `ℤ + ℤ η` -/

/-- The set `ℤ + ℤ η` of integer combinations of `1` and `η`. -/
def lattice (η : ℂ) : Set ℂ := {z | ∃ x y : ℤ, z = x + y * η}

namespace lattice

variable {η : ℂ}

theorem intCast_mem (k : ℤ) : (k : ℂ) ∈ lattice η := ⟨k, 0, by simp⟩

theorem zero_mem : (0 : ℂ) ∈ lattice η := ⟨0, 0, by simp⟩

theorem one_mem : (1 : ℂ) ∈ lattice η := ⟨1, 0, by simp⟩

theorem self_mem : η ∈ lattice η := ⟨0, 1, by simp⟩

theorem add_mem {a b : ℂ} (ha : a ∈ lattice η) (hb : b ∈ lattice η) : a + b ∈ lattice η := by
  obtain ⟨x, y, rfl⟩ := ha
  obtain ⟨x', y', rfl⟩ := hb
  exact ⟨x + x', y + y', by push_cast; ring⟩

theorem neg_mem {a : ℂ} (ha : a ∈ lattice η) : -a ∈ lattice η := by
  obtain ⟨x, y, rfl⟩ := ha
  exact ⟨-x, -y, by push_cast; ring⟩

theorem sub_mem {a b : ℂ} (ha : a ∈ lattice η) (hb : b ∈ lattice η) : a - b ∈ lattice η := by
  simpa [sub_eq_add_neg] using add_mem ha (neg_mem hb)

theorem mul_mem {p q : ℤ} (hη : η ^ 2 = p * η + q) {a b : ℂ} (ha : a ∈ lattice η)
    (hb : b ∈ lattice η) : a * b ∈ lattice η := by
  obtain ⟨x, y, rfl⟩ := ha
  obtain ⟨x', y', rfl⟩ := hb
  exact ⟨x * x' + y * y' * q, x * y' + x' * y + y * y' * p, by
    push_cast
    linear_combination ((y : ℂ) * y') * hη⟩

theorem pow_mem {p q : ℤ} (hη : η ^ 2 = p * η + q) {a : ℂ} (ha : a ∈ lattice η) (k : ℕ) :
    a ^ k ∈ lattice η := by
  induction k with
  | zero => simpa using one_mem
  | succ k ih => rw [pow_succ]; exact mul_mem hη ih ha

theorem conj_mem {p : ℤ} (hc : conj η = p - η) {a : ℂ} (ha : a ∈ lattice η) :
    conj a ∈ lattice η := by
  obtain ⟨x, y, rfl⟩ := ha
  exact ⟨x + y * p, -y, by simp [hc]; ring⟩

/-- A lattice `ℤ + ℤ η` with `η` not real meets every closed ball in a finite set. -/
theorem finite_inter_closedBall (him : η.im ≠ 0) (ρ : ℝ) :
    (lattice η ∩ closedBall 0 ρ).Finite := by
  set K : ℤ := ⌈ρ / |η.im|⌉
  set K' : ℤ := ⌈ρ + K * ‖η‖⌉
  refine (((Set.finite_Icc (-K') K').prod (Set.finite_Icc (-K) K)).image
    fun xy : ℤ × ℤ ↦ (xy.1 : ℂ) + xy.2 * η).subset ?_
  rintro z ⟨⟨x, y, rfl⟩, hz⟩
  rw [mem_closedBall, dist_zero_right] at hz
  have him' : 0 < |η.im| := abs_pos.2 him
  have hy : |(y : ℝ)| ≤ K := by
    have h := abs_im_le_norm ((x : ℂ) + y * η)
    simp only [add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add,
      abs_mul] at h
    refine le_trans ?_ (Int.le_ceil _)
    rw [le_div_iff₀ him']
    linarith
  have hx : |(x : ℝ)| ≤ K' := by
    refine le_trans ?_ (Int.le_ceil _)
    have h : ‖((x : ℂ))‖ ≤ ‖(x : ℂ) + y * η‖ + ‖(y : ℂ) * η‖ := by
      simpa using norm_sub_le ((x : ℂ) + y * η) (y * η)
    simp only [norm_mul, norm_intCast] at h
    nlinarith [mul_le_mul_of_nonneg_right hy (norm_nonneg η)]
  have hy' : |y| ≤ K := by exact_mod_cast hy
  have hx' : |x| ≤ K' := by exact_mod_cast hx
  exact ⟨(x, y), ⟨abs_le.1 hx', abs_le.1 hy'⟩, rfl⟩

end lattice

/-! ### Concrete lattices -/

/-- `ζ₆ = exp (-2πi / 6)`. -/
theorem exp_sixth : exp (-(2 * π * I / (6 : ℕ))) = 1 / 2 - (Real.sqrt 3 / 2 : ℝ) * I := by
  rw [show -(2 * π * I / (6 : ℕ)) = ((-(π / 3) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast
  ring

theorem exp_fourth : exp (-(2 * π * I / (4 : ℕ))) = -I := by
  rw [show -(2 * π * I / (4 : ℕ)) = -(π / 2 * I) by push_cast; ring, exp_neg,
    exp_pi_div_two_mul_I, inv_I]

/-- `exp (-2πi / n)` is a power of `exp (-2πi / M)` when `n ∣ M`. -/
theorem exp_rotationAngle_eq_pow {n M : ℕ} (hM : M ≠ 0) (h : n ∣ M) :
    exp (-(2 * π * I / n)) = exp (-(2 * π * I / M)) ^ (M / n) := by
  obtain ⟨k, rfl⟩ := h
  have hn : n ≠ 0 := left_ne_zero_of_mul hM
  have hk : k ≠ 0 := right_ne_zero_of_mul hM
  rw [← exp_nat_mul, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)]
  congr 1
  push_cast
  field_simp

theorem sqrt_three_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem exp_sixth_sq :
    exp (-(2 * π * I / (6 : ℕ))) ^ 2 = (1 : ℤ) * exp (-(2 * π * I / (6 : ℕ))) + (-1 : ℤ) := by
  rw [exp_sixth]
  push_cast
  linear_combination (I ^ 2 / 4) * sqrt_three_sq + (3 / 4 : ℂ) * I_sq

theorem conj_exp_sixth :
    conj (exp (-(2 * π * I / (6 : ℕ)))) = (1 : ℤ) - exp (-(2 * π * I / (6 : ℕ))) := by
  rw [exp_sixth]
  simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat, conj_ofReal, conj_I]
  push_cast
  ring

theorem im_exp_sixth : (exp (-(2 * π * I / (6 : ℕ)))).im ≠ 0 := by
  rw [exp_sixth]
  simp

theorem I_sq_eq : I ^ 2 = (0 : ℤ) * I + (-1 : ℤ) := by
  simp

theorem conj_I_eq : conj I = (0 : ℤ) - I := by
  simp

/-! ### Elements of the group -/

/-- Every element of the group fixes each point outside the two disks. -/
theorem apply_eq_of_notMem_diskUnion {n₁ n₂ : ℕ} {r₁ r₂ : ℝ} {g : Perm ℂ}
    (hg : g ∈ GG n₁ n₂ r₁ r₂) {z : ℂ} (hz : z ∉ diskUnion r₁ r₂) : g z = z := by
  have hle : GG n₁ n₂ r₁ r₂ ≤ fixingSubgroup (Perm ℂ) (diskUnion r₁ r₂)ᶜ := by
    rw [GG, Subgroup.closure_le]
    rintro σ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_fixingSubgroup_iff] <;>
      intro y hy <;> simp only [diskUnion, Set.mem_compl_iff, Set.mem_union, not_or] at hy
    · exact diskRotation_of_notMem hy.1
    · exact diskRotation_of_notMem hy.2
  exact (mem_fixingSubgroup_iff _).1 (hle hg) z hz

/-- Every element of the group maps the union of the two disks into itself. -/
theorem apply_mem_diskUnion {n₁ n₂ : ℕ} {r₁ r₂ : ℝ} {g : Perm ℂ} (hg : g ∈ GG n₁ n₂ r₁ r₂)
    {z : ℂ} (hz : z ∈ diskUnion r₁ r₂) : g z ∈ diskUnion r₁ r₂ := by
  by_contra h
  have h' := apply_eq_of_notMem_diskUnion hg h
  rw [g.injective h'] at h
  exact h hz

theorem norm_le_of_mem_diskUnion {r₁ r₂ : ℝ} {z : ℂ} (hz : z ∈ diskUnion r₁ r₂) :
    ‖z‖ ≤ 1 + max r₁ r₂ := by
  rcases hz with hz | hz
  · rw [leftDisk, mem_closedBall, dist_eq_norm, leftCenter, sub_neg_eq_add] at hz
    have := norm_sub_le (z + 1) 1
    simp only [add_sub_cancel_right, norm_one] at this
    linarith [le_max_left r₁ r₂]
  · rw [rightDisk, mem_closedBall, dist_eq_norm, rightCenter] at hz
    have := norm_add_le (z - 1) 1
    simp only [sub_add_cancel, norm_one] at this
    linarith [le_max_right r₁ r₂]

theorem conj_mul_self_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : conj u * u = 1 := by
  rw [mul_comm, mul_conj, normSq_eq_norm_sq, hu]
  simp

/-- At each point, every element of the group acts as `z ↦ u * z + t` with `‖u‖ = 1` and `u`, `t`
in a lattice `ℤ + ℤ η` that is closed under multiplication and conjugation and contains the two
rotation factors. -/
theorem exists_affine {η : ℂ} {p q : ℤ} (hη : η ^ 2 = p * η + q) (hc : conj η = p - η)
    {n₁ n₂ : ℕ} (h₁ : exp (-(2 * π * I / n₁)) ∈ lattice η)
    (h₂ : exp (-(2 * π * I / n₂)) ∈ lattice η) {r₁ r₂ : ℝ} {g : Perm ℂ}
    (hg : g ∈ GG n₁ n₂ r₁ r₂) (z : ℂ) :
    ∃ u ∈ lattice η, ‖u‖ = 1 ∧ ∃ t ∈ lattice η, g z = u * z + t := by
  have hid : ∀ w : ℂ, ∃ u ∈ lattice η, ‖u‖ = 1 ∧ ∃ t ∈ lattice η, w = u * w + t := fun w ↦
    ⟨1, lattice.one_mem, norm_one, 0, lattice.zero_mem, by ring⟩
  induction hg using Subgroup.closure_induction generalizing z with
  | mem σ hσ =>
    rcases hσ with rfl | rfl
    · by_cases hz : z ∈ closedBall leftCenter r₁
      · refine ⟨_, h₁, norm_exp_rotationAngle n₁, _, lattice.sub_mem h₁ lattice.one_mem, ?_⟩
        rw [permA_apply, genA, diskRotation_of_mem hz, rotation, leftCenter]
        ring
      · simpa [genA, diskRotation_of_notMem hz] using hid z
    · by_cases hz : z ∈ closedBall rightCenter r₂
      · refine ⟨_, h₂, norm_exp_rotationAngle n₂, _, lattice.sub_mem lattice.one_mem h₂, ?_⟩
        rw [permB_apply, genB, diskRotation_of_mem hz, rotation, rightCenter]
        ring
      · simpa [genB, diskRotation_of_notMem hz] using hid z
  | one => simpa using hid z
  | mul g h _ _ ihg ihh =>
    obtain ⟨u', hu', hu'1, t', ht', e'⟩ := ihh z
    obtain ⟨u, hu, hu1, t, ht, e⟩ := ihg (h z)
    refine ⟨u * u', lattice.mul_mem hη hu hu', by rw [norm_mul, hu1, hu'1, one_mul],
      u * t' + t, lattice.add_mem (lattice.mul_mem hη hu ht') ht, ?_⟩
    rw [Perm.mul_apply, e, e']
    ring
  | inv g _ ihg =>
    obtain ⟨u, hu, hu1, t, ht, e⟩ := ihg (g⁻¹ z)
    have hgz : g (g⁻¹ z) = z := (Perm.inv_eq_iff_eq.mp rfl).symm
    rw [hgz] at e
    refine ⟨conj u, lattice.conj_mem hc hu, by rw [RCLike.norm_conj, hu1], -(conj u * t),
      lattice.neg_mem (lattice.mul_mem hη (lattice.conj_mem hc hu) ht), ?_⟩
    have h1 := conj_mul_self_of_norm_eq_one hu1
    linear_combination (-conj u) * e - (g⁻¹ z) * h1

/-- If the two rotation factors lie in a lattice `ℤ + ℤ η` with `η` not real that is closed under
multiplication and conjugation, then the orbits are uniformly bounded. -/
theorem exists_encard_orbit_le_of_lattice {η : ℂ} {p q : ℤ} (hη : η ^ 2 = p * η + q)
    (hc : conj η = p - η) (him : η.im ≠ 0) {n₁ n₂ : ℕ}
    (h₁ : exp (-(2 * π * I / n₁)) ∈ lattice η) (h₂ : exp (-(2 * π * I / n₂)) ∈ lattice η)
    (r₁ r₂ : ℝ) : ∃ N : ℕ, ∀ z : ℂ, (orbit n₁ n₂ r₁ r₂ z).encard ≤ N := by
  set R := 1 + max r₁ r₂
  set S := (lattice η ∩ closedBall 0 1) ×ˢ (lattice η ∩ closedBall 0 (2 * R))
  have hS : S.Finite :=
    (lattice.finite_inter_closedBall him 1).prod (lattice.finite_inter_closedBall him _)
  refine ⟨S.ncard + 1, fun z ↦ ?_⟩
  have hsub : orbit n₁ n₂ r₁ r₂ z ⊆ insert z ((fun ut : ℂ × ℂ ↦ ut.1 * z + ut.2) '' S) := by
    rintro y ⟨g, hg, rfl⟩
    by_cases hz : z ∈ diskUnion r₁ r₂
    · right
      obtain ⟨u, hu, hu1, t, ht, e⟩ := exists_affine hη hc h₁ h₂ hg z
      have hgz := norm_le_of_mem_diskUnion (apply_mem_diskUnion hg hz)
      have hzR := norm_le_of_mem_diskUnion hz
      refine ⟨(u, t), ⟨⟨hu, by simp [hu1]⟩, ⟨ht, ?_⟩⟩, e.symm⟩
      rw [mem_closedBall, dist_zero_right]
      have : t = g z - u * z := by rw [e]; ring
      rw [this]
      calc ‖g z - u * z‖ ≤ ‖g z‖ + ‖u * z‖ := norm_sub_le _ _
        _ ≤ R + R := by rw [norm_mul, hu1, one_mul]; exact add_le_add hgz hzR
        _ = 2 * R := by ring
    · left
      exact apply_eq_of_notMem_diskUnion hg hz
  calc (orbit n₁ n₂ r₁ r₂ z).encard
      ≤ (insert z ((fun ut : ℂ × ℂ ↦ ut.1 * z + ut.2) '' S)).encard := Set.encard_le_encard hsub
    _ ≤ ((fun ut : ℂ × ℂ ↦ ut.1 * z + ut.2) '' S).encard + 1 := Set.encard_insert_le _ _
    _ ≤ S.encard + 1 := by gcongr; exact Set.encard_image_le _ _
    _ = ((S.ncard + 1 : ℕ) : ℕ∞) := by rw [← hS.cast_ncard_eq]; push_cast; rfl

/-- `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}` holds exactly when `n₁, n₂` both divide `4` or both divide
`6`. -/
theorem lcm_mem_iff (n₁ n₂ : ℕ) :
    Nat.lcm n₁ n₂ ∈ ({1, 2, 3, 4, 6} : Finset ℕ) ↔ n₁ ∣ 4 ∧ n₂ ∣ 4 ∨ n₁ ∣ 6 ∧ n₂ ∣ 6 := by
  constructor
  · intro h
    have h₁ := Nat.dvd_lcm_left n₁ n₂
    have h₂ := Nat.dvd_lcm_right n₁ n₂
    generalize Nat.lcm n₁ n₂ = m at *
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact .inl ⟨h₁.trans (by norm_num), h₂.trans (by norm_num)⟩
    · exact .inl ⟨h₁.trans (by norm_num), h₂.trans (by norm_num)⟩
    · exact .inr ⟨h₁.trans (by norm_num), h₂.trans (by norm_num)⟩
    · exact .inl ⟨h₁, h₂⟩
    · exact .inr ⟨h₁, h₂⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · have hd := Nat.lcm_dvd h₁ h₂
      have hle := Nat.le_of_dvd (by norm_num) hd
      generalize Nat.lcm n₁ n₂ = m at *
      interval_cases m <;> simp_all
    · have hd := Nat.lcm_dvd h₁ h₂
      have hle := Nat.le_of_dvd (by norm_num) hd
      generalize Nat.lcm n₁ n₂ = m at *
      interval_cases m <;> simp_all

/-- If `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}`, then for all radii the orbits are uniformly bounded. -/
theorem exists_encard_orbit_le {n₁ n₂ : ℕ} (h : Nat.lcm n₁ n₂ ∈ ({1, 2, 3, 4, 6} : Finset ℕ))
    (r₁ r₂ : ℝ) : ∃ N : ℕ, ∀ p : ℂ, (orbit n₁ n₂ r₁ r₂ p).encard ≤ N := by
  rcases (lcm_mem_iff n₁ n₂).1 h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hmem : ∀ {n : ℕ}, n ∣ 4 → exp (-(2 * π * I / n)) ∈ lattice I := fun hn ↦ by
      rw [exp_rotationAngle_eq_pow (by norm_num) hn, exp_fourth]
      exact lattice.pow_mem I_sq_eq (lattice.neg_mem lattice.self_mem) _
    exact exists_encard_orbit_le_of_lattice I_sq_eq conj_I_eq (by simp) (hmem h₁) (hmem h₂) r₁ r₂
  · have hmem : ∀ {n : ℕ}, n ∣ 6 →
        exp (-(2 * π * I / n)) ∈ lattice (exp (-(2 * π * I / (6 : ℕ)))) := fun hn ↦ by
      rw [exp_rotationAngle_eq_pow (by norm_num) hn]
      exact lattice.pow_mem exp_sixth_sq lattice.self_mem _
    exact exists_encard_orbit_le_of_lattice exp_sixth_sq conj_exp_sixth im_exp_sixth (hmem h₁)
      (hmem h₂) r₁ r₂

/-- The converse direction of Theorem 1 of arXiv:2302.12950: if `lcm n₁ n₂ ∈ {1, 2, 3, 4, 6}`,
then the two-disk compound symmetry group is finite for all radii. -/
theorem finite_GG {n₁ n₂ : ℕ} (h : Nat.lcm n₁ n₂ ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) (r₁ r₂ : ℝ) :
    Finite (GG n₁ n₂ r₁ r₂) :=
  let ⟨N, hN⟩ := exists_encard_orbit_le h r₁ r₂
  finite_of_encard_orbit_le N hN

end TDCSG

end
