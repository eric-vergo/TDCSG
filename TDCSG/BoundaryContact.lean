/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Sequences
public import TDCSG.Monotonicity

/-!
# Stability of finite orbits and boundary contact

For a common radius `r` of the two closed disks, a finite orbit is unchanged for radii slightly
above (`TDCSG.exists_orbit_eq_of_finite`), so the radii at which a point has an infinite orbit
form a closed half-line or the empty set (`TDCSG.infinite_orbit_radii`). At the critical radius
of a point, the orbit touches a boundary circle or accumulates at one from inside
(`TDCSG.touchesBoundary_or_accumulatesInside`). This is §§4–5 of
`notes/proofs/boundary-contact.md`.

## Main statements

* `TDCSG.orbit_eq_of_agree`: two radius pairs give the same orbit of `p` if every point of one of
  the orbits lies in the same disks for both pairs.
* `TDCSG.exists_orbit_eq_of_finite`: right stability of finite orbits (Theorem 4.1).
* `TDCSG.infinite_orbit_radii`: the per-point critical radius is attained (Corollary 4.2).
* `TDCSG.boundary_depth`, `TDCSG.touchesBoundary_or_accumulatesInside`,
  `TDCSG.of_not_touchesBoundary`: Theorem 5.1, parts 1–3.

## Implementation notes

The written proofs argue with chains of moves. Here orbits are compared through invariant sets:
`TDCSG.orbit_subset` reduces an inclusion of orbits to checking that both generators preserve a
set, and `TDCSG.mem_preserving_of_eqOn` transfers this between generators that agree on it.
-/

@[expose] public section

open Metric Equiv Filter Topology Set

namespace TDCSG

/-! ### Orbits that see the same disk membership -/

theorem diskRotation_eq_of_iff {n : ℕ} {c z : ℂ} {r s : ℝ}
    (h : z ∈ closedBall c s ↔ z ∈ closedBall c r) :
    diskRotation n c s z = diskRotation n c r z := by
  by_cases hz : z ∈ closedBall c r
  · rw [diskRotation_of_mem hz, diskRotation_of_mem (h.2 hz)]
  · rw [diskRotation_of_notMem hz, diskRotation_of_notMem (mt h.1 hz)]

/-- If every point of the orbit of `p` for the radii `(r₁, r₂)` lies in the same disks for the
radii `(s₁, s₂)`, then the orbit for `(s₁, s₂)` is contained in it. -/
theorem orbit_subset_of_agree {n₁ n₂ : ℕ} {r₁ r₂ s₁ s₂ : ℝ} {p : ℂ}
    (h₁ : ∀ y ∈ orbit n₁ n₂ r₁ r₂ p, y ∈ closedBall leftCenter s₁ ↔ y ∈ closedBall leftCenter r₁)
    (h₂ : ∀ y ∈ orbit n₁ n₂ r₁ r₂ p,
      y ∈ closedBall rightCenter s₂ ↔ y ∈ closedBall rightCenter r₂) :
    orbit n₁ n₂ s₁ s₂ p ⊆ orbit n₁ n₂ r₁ r₂ p :=
  orbit_subset (mem_orbit_self _ _ _ _ p)
    (mem_preserving_of_eqOn (GG_le_preserving_orbit _ _ _ _ p (permA_mem_GG _ _ _ _))
      fun y hy ↦ diskRotation_eq_of_iff (h₁ y hy))
    (mem_preserving_of_eqOn (GG_le_preserving_orbit _ _ _ _ p (permB_mem_GG _ _ _ _))
      fun y hy ↦ diskRotation_eq_of_iff (h₂ y hy))

/-- If every point of the orbit of `p` for the radii `(r₁, r₂)` lies in the same disks for the
radii `(s₁, s₂)`, then the two orbits of `p` are equal. -/
theorem orbit_eq_of_agree {n₁ n₂ : ℕ} {r₁ r₂ s₁ s₂ : ℝ} {p : ℂ}
    (h₁ : ∀ y ∈ orbit n₁ n₂ r₁ r₂ p, y ∈ closedBall leftCenter s₁ ↔ y ∈ closedBall leftCenter r₁)
    (h₂ : ∀ y ∈ orbit n₁ n₂ r₁ r₂ p,
      y ∈ closedBall rightCenter s₂ ↔ y ∈ closedBall rightCenter r₂) :
    orbit n₁ n₂ s₁ s₂ p = orbit n₁ n₂ r₁ r₂ p := by
  have hsub := orbit_subset_of_agree h₁ h₂
  refine hsub.antisymm (orbit_subset_of_agree (fun y hy ↦ (h₁ y (hsub hy)).symm)
    (fun y hy ↦ (h₂ y (hsub hy)).symm))

/-- Equal-radius form of `TDCSG.orbit_eq_of_agree`. -/
theorem orbit_eq_of_agree' {n₁ n₂ : ℕ} {r s : ℝ} {p : ℂ}
    (h : ∀ y ∈ orbit n₁ n₂ r r p, ∀ c ∈ ({leftCenter, rightCenter} : Set ℂ),
      dist y c ≤ s ↔ dist y c ≤ r) :
    orbit n₁ n₂ s s p = orbit n₁ n₂ r r p :=
  orbit_eq_of_agree (fun y hy ↦ h y hy _ (by simp)) (fun y hy ↦ h y hy _ (by simp))

theorem diskRotation_of_nonpos {n : ℕ} {c : ℂ} {r : ℝ} (hr : r ≤ 0) (z : ℂ) :
    diskRotation n c r z = z := by
  by_cases hz : z ∈ closedBall c r
  · have : z = c := dist_le_zero.1 ((mem_closedBall.1 hz).trans hr)
    subst this
    simp [diskRotation_of_mem hz, rotation]
  · exact diskRotation_of_notMem hz

/-- For a non-positive radius both generators are the identity, so every orbit is a point. -/
theorem orbit_of_nonpos (n₁ n₂ : ℕ) {r : ℝ} (hr : r ≤ 0) (p : ℂ) :
    orbit n₁ n₂ r r p ⊆ {p} := by
  have h1 : (1 : Perm ℂ) ∈ preserving {p} := Subgroup.one_mem _
  exact orbit_subset rfl (mem_preserving_of_forall_eq_or h1 fun w ↦ .inl
    (diskRotation_of_nonpos hr w)) (mem_preserving_of_forall_eq_or h1 fun w ↦ .inl
    (diskRotation_of_nonpos hr w))

theorem pos_of_infinite {n₁ n₂ : ℕ} {r : ℝ} {p : ℂ} (h : (orbit n₁ n₂ r r p).Infinite) :
    0 < r := by
  by_contra hr
  exact h ((finite_singleton p).subset (orbit_of_nonpos n₁ n₂ (not_lt.1 hr) p))

private theorem exists_pos_forall_le {α : Type*} {T : Set α} (hT : T.Finite) {f : α → ℝ}
    (hf : ∀ x ∈ T, 0 < f x) : ∃ δ > 0, ∀ x ∈ T, δ ≤ f x := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨m, hm, hmin⟩ := exists_min_image T f hT hne
    exact ⟨f m, hf m hm, hmin⟩

/-! ### Right stability of finite orbits -/

/-- Right stability of finite orbits: a finite orbit for the common radius `r₀` is unchanged for
all radii in some interval `[r₀, r₀ + δ)`. -/
theorem exists_orbit_eq_of_finite (n₁ n₂ : ℕ) {r₀ : ℝ} {p : ℂ}
    (h : (orbit n₁ n₂ r₀ r₀ p).Finite) :
    ∃ δ > 0, ∀ r, r₀ ≤ r → r < r₀ + δ → orbit n₁ n₂ r r p = orbit n₁ n₂ r₀ r₀ p := by
  set T := (orbit n₁ n₂ r₀ r₀ p ×ˢ ({leftCenter, rightCenter} : Set ℂ)) ∩
    {x | r₀ < dist x.1 x.2}
  have hT : T.Finite := (h.prod (toFinite _)).subset inter_subset_left
  obtain ⟨δ, hδ, hle⟩ := exists_pos_forall_le hT (f := fun x ↦ dist x.1 x.2 - r₀)
    fun x hx ↦ sub_pos.2 hx.2
  refine ⟨δ, hδ, fun r hr₁ hr₂ ↦ orbit_eq_of_agree' fun y hy c hc ↦ ⟨fun hyc ↦ ?_,
    fun hyc ↦ hyc.trans hr₁⟩⟩
  by_contra hlt
  have := hle (y, c) ⟨⟨hy, hc⟩, not_le.1 hlt⟩
  simp only at this
  linarith

/-- The radii at which the orbit of `p` is infinite form the empty set or a closed half-line
`[r₀, ∞)` with `r₀ > 0`. -/
theorem infinite_orbit_radii (n₁ n₂ : ℕ) (p : ℂ) :
    {r : ℝ | (orbit n₁ n₂ r r p).Infinite} = ∅ ∨
      ∃ r₀ > 0, {r : ℝ | (orbit n₁ n₂ r r p).Infinite} = Ici r₀ := by
  set I := {r : ℝ | (orbit n₁ n₂ r r p).Infinite}
  rcases I.eq_empty_or_nonempty with hI | hI
  · exact .inl hI
  right
  have hbdd : BddBelow I := ⟨0, fun r hr ↦ (pos_of_infinite hr).le⟩
  have hup : ∀ r ∈ I, ∀ r', r ≤ r' → r' ∈ I := fun r hr r' h ↦
    hr.mono (orbit_mono n₁ n₂ h h p)
  have hmem : sInf I ∈ I := by
    by_contra hfin
    obtain ⟨δ, hδ, heq⟩ := exists_orbit_eq_of_finite n₁ n₂ (not_not.1 hfin)
    have : sInf I + δ ≤ sInf I := le_csInf hI fun r hr ↦ by
      by_contra hlt
      apply hfin
      change (orbit n₁ n₂ (sInf I) (sInf I) p).Infinite
      rw [← heq r (csInf_le hbdd hr) (not_le.1 hlt)]
      exact hr
    linarith
  refine ⟨sInf I, pos_of_infinite hmem, ?_⟩
  ext r
  exact ⟨fun hr ↦ csInf_le hbdd hr, fun hr ↦ hup _ hmem r hr⟩

/-! ### Boundary contact -/

/-- Boundary contact, part 1: at the critical radius `r₀` of `p`, orbit points come arbitrarily
close to a boundary circle from inside (or lie on it). -/
theorem boundary_depth (n₁ n₂ : ℕ) {r₀ : ℝ} {p : ℂ} (hO : (orbit n₁ n₂ r₀ r₀ p).Infinite)
    (hfin : ∀ r < r₀, (orbit n₁ n₂ r r p).Finite) :
    ∀ ε > 0, ∃ y ∈ orbit n₁ n₂ r₀ r₀ p, ∃ c ∈ ({leftCenter, rightCenter} : Set ℂ),
      r₀ - ε < dist y c ∧ dist y c ≤ r₀ := by
  intro ε hε
  by_contra! h
  apply hO
  rw [← orbit_eq_of_agree' (s := r₀ - ε / 2) fun y hy c hc ↦
    ⟨fun hyc ↦ hyc.trans (by linarith), fun hyc ↦ by
      by_contra hlt
      linarith [h y hy c hc (by linarith)]⟩]
  exact hfin _ (by linarith)

/-- If points of `O` come arbitrarily close to a boundary circle of radius `r₀` from inside or on
it, and none lies on it, then they accumulate at a boundary circle from inside. -/
theorem accumulatesInside_of_forall_depth {O : Set ℂ} {r₀ : ℝ}
    (hd : ∀ ε > 0, ∃ y ∈ O, ∃ c ∈ ({leftCenter, rightCenter} : Set ℂ),
      r₀ - ε < dist y c ∧ dist y c ≤ r₀)
    (hB : ¬TouchesBoundary O r₀) : AccumulatesInside O r₀ := by
  have hne : ∀ y ∈ O, ∀ c ∈ ({leftCenter, rightCenter} : Set ℂ), dist y c ≠ r₀ := by
    rintro y hy c (rfl | rfl) he
    exacts [hB ⟨y, hy, .inl he⟩, hB ⟨y, hy, .inr he⟩]
  have hd' : ∀ ε > 0, ∃ y ∈ O, ∃ c ∈ ({leftCenter, rightCenter} : Set ℂ),
      r₀ - ε < dist y c ∧ dist y c < r₀ := fun ε hε ↦ by
    obtain ⟨y, hy, c, hc, h1, h2⟩ := hd ε hε
    exact ⟨y, hy, c, hc, h1, lt_of_le_of_ne h2 (hne y hy c hc)⟩
  refine ⟨fun ε hε hfin ↦ ?_, ?_⟩
  · set T := ({y ∈ O | ∃ c ∈ ({leftCenter, rightCenter} : Set ℂ),
        r₀ - ε < dist y c ∧ dist y c < r₀} ×ˢ ({leftCenter, rightCenter} : Set ℂ)) ∩
      {x | dist x.1 x.2 < r₀}
    have hT : T.Finite := (hfin.prod (toFinite _)).subset inter_subset_left
    obtain ⟨δ, hδ, hle⟩ := exists_pos_forall_le hT (f := fun x ↦ r₀ - dist x.1 x.2)
      fun x hx ↦ sub_pos.2 hx.2
    obtain ⟨y, hy, c, hc, h1, h2⟩ := hd' (min ε δ) (lt_min hε hδ)
    have := hle (y, c) ⟨⟨⟨hy, c, hc, by linarith [min_le_left ε δ], h2⟩, hc⟩, h2⟩
    simp only at this
    linarith [min_le_right ε δ]
  · have hc : ∃ c ∈ ({leftCenter, rightCenter} : Set ℂ), ∀ ε > 0, ∃ y ∈ O,
        r₀ - ε < dist y c ∧ dist y c < r₀ := by
      by_contra! h
      obtain ⟨ε₁, hε₁, h₁⟩ := h leftCenter (by simp)
      obtain ⟨ε₂, hε₂, h₂⟩ := h rightCenter (by simp)
      obtain ⟨y, hy, c, hc, hy1, hy2⟩ := hd' (min ε₁ ε₂) (lt_min hε₁ hε₂)
      rcases hc with rfl | rfl
      · exact absurd hy2 (not_lt.2 (h₁ y hy (by linarith [min_le_left ε₁ ε₂])))
      · exact absurd hy2 (not_lt.2 (h₂ y hy (by linarith [min_le_right ε₁ ε₂])))
    obtain ⟨c, hc, hseq⟩ := hc
    choose y hyO hy1 hy2 using fun k : ℕ ↦ hseq (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
    obtain ⟨x, hx, φ, hφ, hlim⟩ := (isCompact_closedBall c r₀).tendsto_subseq
      (x := y) fun k ↦ mem_closedBall.2 (hy2 k).le
    have hxc : dist x c = r₀ := by
      refine le_antisymm (mem_closedBall.1 hx) ?_
      have hd := (hlim.dist (tendsto_const_nhds (x := c))).add
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at hd
      refine ge_of_tendsto hd (Eventually.of_forall fun k ↦ ?_)
      have hkφ : (k : ℝ) ≤ φ k := by exact_mod_cast hφ.id_le k
      have hk : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have := hy1 (φ k)
      simp only [Function.comp_apply]
      linarith
    refine ⟨c, hc, x, hxc, accPt_iff_nhds.2 fun U hU ↦ ?_⟩
    obtain ⟨k, hk⟩ := (hlim.eventually (p := (· ∈ U)) hU).exists
    refine ⟨y (φ k), ⟨hk, hyO _, mem_ball.2 (hy2 _)⟩, fun he ↦ ?_⟩
    have := hy2 (φ k)
    rw [he, hxc] at this
    exact lt_irrefl _ this

/-- Membership in the union of the orbits at smaller radii is preserved by a generator at the
critical radius when no orbit point lies on its boundary circle. -/
private theorem mem_preserving_iUnion {n : ℕ} {c : ℂ} {r₀ : ℝ} {O : Set ℂ}
    (orb : ℝ → Set ℂ) (hmono : ∀ r r', r ≤ r' → orb r ⊆ orb r')
    (hmem : ∀ s, diskPerm n c s ∈ preserving (orb s)) (hO : diskPerm n c r₀ ∈ preserving O)
    (hVO : (⋃ r ∈ Iio r₀, orb r) ⊆ O) (hB : ∀ y ∈ O, dist y c ≠ r₀) :
    diskPerm n c r₀ ∈ preserving (⋃ r ∈ Iio r₀, orb r) := by
  intro y hy
  have hyO := hVO hy
  obtain ⟨r, hr, hyr⟩ := mem_iUnion₂.1 hy
  have key : ∀ w, dist w c < r₀ → w ∈ orb (max r (dist w c)) → (max r (dist w c)) ∈ Iio r₀ ∧
      w ∈ closedBall c (max r (dist w c)) := fun w hw _ ↦
    ⟨max_lt hr hw, mem_closedBall.2 (le_max_right _ _)⟩
  constructor
  · by_cases hyc : y ∈ closedBall c r₀
    · have hlt : dist y c < r₀ := lt_of_le_of_ne (mem_closedBall.1 hyc) (hB y hyO)
      have hy' : y ∈ orb (max r (dist y c)) := hmono _ _ (le_max_left _ _) hyr
      obtain ⟨h1, h2⟩ := key y hlt hy'
      have : diskPerm n c r₀ y = diskPerm n c (max r (dist y c)) y := by
        simp [diskRotation_of_mem hyc, diskRotation_of_mem h2]
      rw [this]
      exact mem_iUnion₂.2 ⟨_, h1, (hmem _ y hy').1⟩
    · rw [diskPerm_apply, diskRotation_of_notMem hyc]
      exact hy
  · set w := (diskPerm n c r₀)⁻¹ y
    have hwy : diskPerm n c r₀ w = y := (Perm.inv_eq_iff_eq.mp rfl).symm
    have hwO : w ∈ O := (hO y hyO).2
    by_cases hwc : w ∈ closedBall c r₀
    · have hlt : dist w c < r₀ := lt_of_le_of_ne (mem_closedBall.1 hwc) (hB w hwO)
      have hrot : diskPerm n c r₀ w = rotation n c w := diskRotation_of_mem hwc
      have hdist : dist y c = dist w c := by rw [← hwy, hrot, dist_rotation]
      set s := max r (dist w c)
      have hy' : y ∈ orb s := hmono _ _ (le_max_left _ _) hyr
      have hws : w ∈ closedBall c s := mem_closedBall.2 (le_max_right _ _)
      have hs : diskPerm n c s w = y := by
        rw [← hwy, hrot]
        exact diskRotation_of_mem hws
      have : w = (diskPerm n c s)⁻¹ y := by rw [← hs]; exact (Perm.inv_eq_iff_eq.mpr rfl).symm
      rw [this]
      exact mem_iUnion₂.2 ⟨s, max_lt hr hlt, (hmem s y hy').2⟩
    · have : w = y := by rw [← hwy, diskPerm_apply, diskRotation_of_notMem hwc]
      rw [this]
      exact hy

/-- Boundary contact, part 3: if the orbit at the critical radius touches no boundary circle,
then it accumulates at one from inside, it is the union of the orbits at smaller radii, and the
sizes of those orbits tend to infinity. -/
theorem of_not_touchesBoundary (n₁ n₂ : ℕ) {r₀ : ℝ} {p : ℂ}
    (hO : (orbit n₁ n₂ r₀ r₀ p).Infinite) (hfin : ∀ r < r₀, (orbit n₁ n₂ r r p).Finite)
    (hB : ¬TouchesBoundary (orbit n₁ n₂ r₀ r₀ p) r₀) :
    AccumulatesInside (orbit n₁ n₂ r₀ r₀ p) r₀ ∧
      orbit n₁ n₂ r₀ r₀ p = ⋃ r ∈ Iio r₀, orbit n₁ n₂ r r p ∧
      ∀ N : ℕ, ∃ r₁ < r₀, ∀ r ∈ Ico r₁ r₀, (N : ℕ∞) < (orbit n₁ n₂ r r p).encard := by
  set O := orbit n₁ n₂ r₀ r₀ p
  have hmono : ∀ r r', r ≤ r' → orbit n₁ n₂ r r p ⊆ orbit n₁ n₂ r' r' p := fun r r' h ↦
    orbit_mono n₁ n₂ h h p
  have hVO : (⋃ r ∈ Iio r₀, orbit n₁ n₂ r r p) ⊆ O :=
    iUnion₂_subset fun r hr ↦ hmono _ _ (le_of_lt hr)
  have hU : O = ⋃ r ∈ Iio r₀, orbit n₁ n₂ r r p := by
    refine (orbit_subset (mem_iUnion₂.2 ⟨r₀ - 1, by simp, mem_orbit_self _ _ _ _ p⟩) ?_ ?_).antisymm
      hVO
    · exact mem_preserving_iUnion (fun r ↦ orbit n₁ n₂ r r p) hmono
        (fun s ↦ GG_le_preserving_orbit _ _ _ _ p (permA_mem_GG _ _ _ _))
        (GG_le_preserving_orbit _ _ _ _ p (permA_mem_GG _ _ _ _)) hVO
        fun y hy he ↦ hB ⟨y, hy, .inl he⟩
    · exact mem_preserving_iUnion (fun r ↦ orbit n₁ n₂ r r p) hmono
        (fun s ↦ GG_le_preserving_orbit _ _ _ _ p (permB_mem_GG _ _ _ _))
        (GG_le_preserving_orbit _ _ _ _ p (permB_mem_GG _ _ _ _)) hVO
        fun y hy he ↦ hB ⟨y, hy, .inr he⟩
  refine ⟨accumulatesInside_of_forall_depth (boundary_depth n₁ n₂ hO hfin) hB, hU,
    fun N ↦ ?_⟩
  obtain ⟨t, htO, htc⟩ := hO.exists_subset_card_eq (N + 1)
  have : ∀ y ∈ t, ∃ s < r₀, y ∈ orbit n₁ n₂ s s p := fun y hy ↦ by
    have := htO hy
    rw [hU] at this
    obtain ⟨s, hs, h⟩ := mem_iUnion₂.1 this
    exact ⟨s, hs, h⟩
  choose! f hf hft using this
  have htne : t.Nonempty := Finset.card_pos.1 (by omega)
  refine ⟨t.sup' htne f, (Finset.sup'_lt_iff htne).2 hf, fun r hr ↦ ?_⟩
  have hsub : (t : Set ℂ) ⊆ orbit n₁ n₂ r r p := fun y hy ↦
    hmono _ _ ((Finset.le_sup' f hy).trans hr.1) (hft y hy)
  calc (N : ℕ∞) < (N + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self N
    _ = (t : Set ℂ).encard := by rw [Set.encard_coe_eq_coe_finsetCard, htc]
    _ ≤ _ := Set.encard_le_encard hsub

/-- Boundary contact, part 2: at the critical radius of `p`, the orbit touches a boundary circle
or accumulates at one from inside. -/
theorem touchesBoundary_or_accumulatesInside (n₁ n₂ : ℕ) {r₀ : ℝ} {p : ℂ}
    (hO : (orbit n₁ n₂ r₀ r₀ p).Infinite) (hfin : ∀ r < r₀, (orbit n₁ n₂ r r p).Finite) :
    TouchesBoundary (orbit n₁ n₂ r₀ r₀ p) r₀ ∨ AccumulatesInside (orbit n₁ n₂ r₀ r₀ p) r₀ :=
  or_iff_not_imp_left.2 fun hB ↦ (of_not_touchesBoundary n₁ n₂ hO hfin hB).1

end TDCSG

end
