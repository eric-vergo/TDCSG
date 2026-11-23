/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
module

public import TDCSG.CriticalRadius.Basic
public import TDCSG.CriticalRadius.QuadraticSigns
public import TDCSG.CriticalRadius.Renormalization

/-!
# Exact renormalization families for `n = 8` and `n = 12`

An integer model of `ℤ[ζ]` for a primitive `n`-th root of unity `ζ` with `ζ⁴ = -1 + v ζ²` and
real subfield `ℚ(√m)`, `m = v + 2`: this covers `n = 8` (`m = 2`) and `n = 12` (`m = 3`). On top of
it, exact checks of the two hypotheses of the renormalization lemma
`TDCSG.Renormalization.renormalize` for a family of words acting on a line `p + t V`, with domain
end points in `ℚ(√m)(√h₁, √h₂)`; and the theorem `TDCSG.CycQ.mem_orbit_of_checks` that turns
successful checks into points of an orbit at every scale `ε ^ k`.

All numbers on the line are stored doubled, so that their coordinates are integers: a parameter
`t` is stored as `2 t`, a point `z` of the plane as `2 z`.

## Main definitions

* `TDCSG.CycQ m`: the element `c0 + c1 ζ + c2 ζ² + c3 ζ³` of `ℤ[ζ]`.
* `TDCSG.CycQ.IsRoot n m ζ`: `ζ = exp (2πi / n)` satisfies the relations of the model.
* `TDCSG.CycQ.memOK`: an exact test that a point `(P + Q √h) / 2` lies in a closed disk.
* `TDCSG.CycQ.Lin`: a parameter `(A + B₁ √h₁ + B₂ √h₂) / 2` on the line.
* `TDCSG.CycQ.Entry`, `TDCSG.CycQ.Piece`: a family member (a word, the isometry `t ↦ ±t + c` it
  induces on the line, and its domain), and a piece of the closure data.
* `TDCSG.CycQ.realizeOK`, `TDCSG.CycQ.closureOK`: the exact checks of realization and closure.

## Main statements

* `TDCSG.CycQ.mem_orbit_of_checks`: if the checks pass, then for every `k` and every family
  member, the member rescaled by `ε ^ k` maps every point of its rescaled domain into its orbit.
-/

@[expose] public section

open Complex Metric
open scoped Real

namespace TDCSG

open Renormalization

/-- Single-point validity: every letter of `w` is applied, under the global rotations of the
earlier letters, to a point of its closed disk. -/
def PtValid (n : ℕ) (r : ℝ) : List Letter → ℂ → Prop
  | [], _ => True
  | l :: w, z => z ∈ closedBall l.center r ∧ PtValid n r w (l.glob n z)

/-- A word valid at both end points of a segment is valid on the segment. -/
theorem wordValid_of_ptValid {n : ℕ} {r : ℝ} {w : List Letter} {P Q : ℂ} (hP : PtValid n r w P)
    (hQ : PtValid n r w Q) : WordValid n r w P Q := by
  induction w generalizing P Q with
  | nil => trivial
  | cons l w ih => exact ⟨hP.1, hQ.1, ih hP.2 hQ.2⟩

/-- A word valid on the segment from `p + t₀ V` to `p + t₁ V`, whose global rotation maps both
end points to the points of parameters `ract pos c t₀` and `ract pos c t₁`, maps every point of
the segment to the point of parameter `ract pos c t`. -/
theorem applyWord_ract {n : ℕ} {r : ℝ} {w : List Letter} {p V : ℂ} {t₀ t₁ c : ℝ} {pos : Bool}
    (hw : WordValid n r w (p + t₀ * V) (p + t₁ * V))
    (h₀ : globalWord n w (p + t₀ * V) = p + (ract pos c t₀ : ℝ) * V)
    (h₁ : globalWord n w (p + t₁ * V) = p + (ract pos c t₁ : ℝ) * V) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) :
    applyWord n r w (p + t * V) = p + (ract pos c t : ℝ) * V := by
  obtain ⟨s, hs, rfl⟩ : ∃ s ∈ Set.Icc (0 : ℝ) 1, t = t₀ + s * (t₁ - t₀) := by
    rcases eq_or_ne t₀ t₁ with h | h
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by linarith [ht.1, ht.2, h]⟩
    · have hd : 0 < t₁ - t₀ := sub_pos.2 (lt_of_le_of_ne (ht.1.trans ht.2) h)
      refine ⟨(t - t₀) / (t₁ - t₀), ⟨div_nonneg (by linarith [ht.1]) hd.le, ?_⟩, ?_⟩
      · rw [div_le_one hd]
        linarith [ht.2]
      · field_simp
        ring
  have key := applyWord_segment hw hs
  rw [h₀, h₁] at key
  rw [show p + ((t₀ + s * (t₁ - t₀) : ℝ) : ℂ) * V = p + t₀ * V + s * (p + t₁ * V - (p + t₀ * V))
    by push_cast; ring, key]
  cases pos <;> simp only [ract, Bool.false_eq_true, ite_false, ite_true] <;> push_cast <;> ring

/-- Orbits are transitive. -/
theorem mem_orbit_trans {n : ℕ} {r : ℝ} {p y z : ℂ} (hy : y ∈ orbit n n r r p)
    (hz : z ∈ orbit n n r r y) : z ∈ orbit n n r r p := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨h, hh, rfl⟩ := hz
  exact ⟨h * g, Subgroup.mul_mem _ hh hg, rfl⟩

/-- The coefficient `v = m - 2` of the relation `ζ⁴ = -1 + v ζ²`. -/
def CycQ.v (m : ℕ) : ℤ := m - 2

/-- The element `c0 + c1 ζ + c2 ζ² + c3 ζ³` of `ℤ[ζ]`, for `ζ` with `ζ⁴ = -1 + v ζ²`,
`v = m - 2`. -/
@[ext]
structure CycQ (m : ℕ) where
  /-- The coordinate of `1`. -/
  c0 : ℤ
  /-- The coordinate of `ζ`. -/
  c1 : ℤ
  /-- The coordinate of `ζ²`. -/
  c2 : ℤ
  /-- The coordinate of `ζ³`. -/
  c3 : ℤ
  deriving DecidableEq, Repr

namespace CycQ

variable {m : ℕ}

instance : Add (CycQ m) := ⟨fun x y ↦ ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3⟩⟩
instance : Sub (CycQ m) := ⟨fun x y ↦ ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2, x.c3 - y.c3⟩⟩

/-- The integer `k`, in the model. -/
def ofInt (k : ℤ) : CycQ m := ⟨k, 0, 0, 0⟩

/-- Multiplication by an integer. -/
def smul (k : ℤ) (x : CycQ m) : CycQ m := ⟨k * x.c0, k * x.c1, k * x.c2, k * x.c3⟩

/-- Multiplication by `ζ`. -/
def mulZeta (x : CycQ m) : CycQ m := ⟨-x.c3, x.c0, x.c1 + v m * x.c3, x.c2⟩

/-- Multiplication by `ζ⁻¹ = v ζ - ζ³`. -/
def mulZetaInv (x : CycQ m) : CycQ m := ⟨x.c1, x.c2 + v m * x.c0, x.c3, -x.c0⟩

instance : Mul (CycQ m) := ⟨fun x y ↦ smul x.c0 y + smul x.c1 (mulZeta y) +
  smul x.c2 (mulZeta (mulZeta y)) + smul x.c3 (mulZeta (mulZeta (mulZeta y)))⟩

/-- Complex conjugation, which sends `ζ` to `ζ⁻¹`. -/
def conj (x : CycQ m) : CycQ m :=
  ofInt x.c0 + mulZetaInv (ofInt x.c1 + mulZetaInv (ofInt x.c2 + mulZetaInv (ofInt x.c3)))

/-- The element `a + b √m` of the real subfield, if `x` has this shape: `√m = (v + 1) ζ - ζ³`. -/
def toQuad? (x : CycQ m) : Option (Quad m) :=
  if x.c2 = 0 ∧ x.c1 = -(v m + 1) * x.c3 then some ⟨x.c0, -x.c3⟩ else none

/-- The element `a + b √m` of `ℤ[√m]` in the model. -/
def ofQuad (q : Quad m) : CycQ m := ⟨q.a, (v m + 1) * q.b, 0, -q.b⟩

/-- The root `ζ = exp (2πi / n)` satisfies the relations of the model `CycQ m`. -/
structure IsRoot (n m : ℕ) (ζ : ℂ) : Prop where
  /-- `ζ` is the root of unity `exp (2πi / n)`. -/
  exp_eq : exp (2 * π * I / n) = ζ
  /-- The quartic relation of the model. -/
  pow_four : ζ ^ 4 = -1 + (v m : ℂ) * ζ ^ 2
  /-- The representation `√m = (v + 1) ζ - ζ³` of the square root in the model. -/
  sqrt_eq : ((v m : ℂ) + 1) * ζ - ζ ^ 3 = ((√(m : ℝ) : ℝ) : ℂ)

/-- The complex number represented by an element of the model. -/
noncomputable def embed (ζ : ℂ) (x : CycQ m) : ℂ :=
  x.c0 + x.c1 * ζ + x.c2 * ζ ^ 2 + x.c3 * ζ ^ 3

variable {n : ℕ} {ζ : ℂ}

/-- The embedding is additive. -/
@[simp] theorem embed_add (x y : CycQ m) : embed ζ (x + y) = embed ζ x + embed ζ y := by
  simp only [embed, show x + y = ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3⟩ from rfl]
  push_cast
  ring

/-- The embedding commutes with subtraction. -/
@[simp] theorem embed_sub (x y : CycQ m) : embed ζ (x - y) = embed ζ x - embed ζ y := by
  simp only [embed, show x - y = ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2, x.c3 - y.c3⟩ from rfl]
  push_cast
  ring

/-- The embedding sends the integer `k` of the model to `k`. -/
@[simp] theorem embed_ofInt (k : ℤ) : embed ζ (ofInt k : CycQ m) = k := by
  simp [embed, ofInt]

/-- The embedding commutes with multiplication by integers. -/
@[simp] theorem embed_smul (k : ℤ) (x : CycQ m) : embed ζ (smul k x) = k * embed ζ x := by
  simp only [embed, smul]
  push_cast
  ring

/-- The inverse `v ζ - ζ³` of `ζ`. -/
noncomputable def zetaInv (m : ℕ) (ζ : ℂ) : ℂ := (v m : ℂ) * ζ - ζ ^ 3

/-- `zetaInv m ζ` is the inverse of `ζ`. -/
theorem IsRoot.mul_zetaInv (hζ : IsRoot n m ζ) : ζ * zetaInv m ζ = 1 := by
  rw [zetaInv]
  linear_combination -hζ.pow_four

/-- `TDCSG.CycQ.mulZeta` is multiplication by `ζ`. -/
theorem embed_mulZeta (hζ : IsRoot n m ζ) (x : CycQ m) :
    embed ζ (mulZeta x) = ζ * embed ζ x := by
  simp only [embed, mulZeta]
  push_cast
  linear_combination (-(x.c3 : ℂ)) * hζ.pow_four

/-- `TDCSG.CycQ.mulZetaInv` is multiplication by `ζ⁻¹`. -/
theorem embed_mulZetaInv (hζ : IsRoot n m ζ) (x : CycQ m) :
    embed ζ (mulZetaInv x) = zetaInv m ζ * embed ζ x := by
  have h : mulZeta (mulZetaInv x) = x := by
    simp only [mulZeta, mulZetaInv]
    ext <;> simp
  have h' := congrArg (embed ζ) h
  rw [embed_mulZeta hζ] at h'
  rw [← h', ← mul_assoc, mul_comm (zetaInv m ζ), hζ.mul_zetaInv, one_mul]

/-- The embedding is multiplicative. -/
theorem embed_mul (hζ : IsRoot n m ζ) (x y : CycQ m) :
    embed ζ (x * y) = embed ζ x * embed ζ y := by
  simp only [show x * y = smul x.c0 y + smul x.c1 (mulZeta y) + smul x.c2 (mulZeta (mulZeta y)) +
    smul x.c3 (mulZeta (mulZeta (mulZeta y))) from rfl, embed_add, embed_smul,
    embed_mulZeta hζ]
  simp only [embed]
  ring

/-- The complex conjugate of `ζ` is `ζ⁻¹`. -/
theorem IsRoot.conj_eq (hζ : IsRoot n m ζ) : (starRingEnd ℂ) ζ = zetaInv m ζ := by
  have h1 : (starRingEnd ℂ) ζ = exp (-(2 * π * I / n)) := by
    rw [← hζ.exp_eq, ← exp_conj]
    congr 1
    simp [conj_ofReal, map_ofNat, map_natCast]
    ring
  have h2 : exp (-(2 * π * I / n)) * ζ = 1 := by
    rw [← hζ.exp_eq, ← exp_add, neg_add_cancel, exp_zero]
  rw [h1]
  calc exp (-(2 * π * I / n)) = exp (-(2 * π * I / n)) * (ζ * zetaInv m ζ) := by
        rw [hζ.mul_zetaInv, mul_one]
    _ = zetaInv m ζ := by rw [← mul_assoc, h2, one_mul]

/-- The embedding commutes with complex conjugation. -/
theorem embed_conj (hζ : IsRoot n m ζ) (x : CycQ m) :
    embed ζ (conj x) = (starRingEnd ℂ) (embed ζ x) := by
  simp only [conj, embed_add, embed_ofInt, embed_mulZetaInv hζ]
  simp only [embed, map_add, map_mul, map_intCast, map_pow, hζ.conj_eq]
  ring

/-- An element recognized by `TDCSG.CycQ.toQuad?` as `q ∈ ℤ[√m]` embeds as the real number `q`. -/
theorem embed_of_toQuad? (hζ : IsRoot n m ζ) {x : CycQ m} {q : Quad m}
    (h : x.toQuad? = some q) : embed ζ x = (q.toReal : ℂ) := by
  simp only [toQuad?] at h
  split_ifs at h with hx
  obtain ⟨h2, h1⟩ := hx
  cases h
  simp only [embed, Quad.toReal, h2, h1]
  push_cast
  rw [← hζ.sqrt_eq]
  ring

/-- `TDCSG.CycQ.ofQuad q` embeds as the real number `q`. -/
theorem embed_ofQuad (hζ : IsRoot n m ζ) (q : Quad m) : embed ζ (ofQuad q) = (q.toReal : ℂ) := by
  simp only [embed, ofQuad, Quad.toReal]
  push_cast
  rw [← hζ.sqrt_eq]
  ring

/-! ### Letters in the model -/

/-- Twice the centre of the disk of a letter. -/
def center : Letter → CycQ m
  | .a | .aInv => ofInt (-2)
  | .b | .bInv => ofInt 2

/-- The rotation factor of a letter. -/
def rot : Letter → CycQ m → CycQ m
  | .a | .b => mulZetaInv
  | .aInv | .bInv => mulZeta

/-- The global rotation of a letter, on doubled points. -/
def stepP (l : Letter) (P : CycQ m) : CycQ m := center l + rot l (P - center l)

/-- The doubled centre of a letter embeds as twice its centre. -/
theorem embed_center (l : Letter) : embed ζ (center l : CycQ m) = 2 * l.center := by
  cases l <;> simp [center, Letter.center, leftCenter, rightCenter]

/-- `TDCSG.CycQ.rot l` is multiplication by the rotation factor of `l`. -/
theorem embed_rot (hζ : IsRoot n m ζ) (l : Letter) (x : CycQ m) :
    embed ζ (rot l x) = l.factor n * embed ζ x := by
  have hf : exp (-(2 * π * I / n)) = zetaInv m ζ := by
    rw [← hζ.conj_eq, ← hζ.exp_eq, ← exp_conj]
    congr 1
    simp [conj_ofReal, map_ofNat, map_natCast]
    ring
  cases l <;> simp [rot, Letter.factor, embed_mulZeta hζ, embed_mulZetaInv hζ, hf, hζ.exp_eq]

/-- The point `(P + Q s) / 2` of the plane. -/
noncomputable def pt (ζ : ℂ) (s : ℝ) (P Q : CycQ m) : ℂ := (embed ζ P + embed ζ Q * s) / 2

/-- `TDCSG.CycQ.stepP` and `TDCSG.CycQ.rot` compute the global rotation of a letter on the
point `(P + Q s) / 2`. -/
theorem pt_step (hζ : IsRoot n m ζ) (s : ℝ) (l : Letter) (P Q : CycQ m) :
    pt ζ s (stepP l P) (rot l Q) = l.glob n (pt ζ s P Q) := by
  simp only [pt, stepP, embed_add, embed_rot hζ, embed_sub, embed_center, Letter.glob]
  ring

/-- The exact test that `(P + Q √h) / 2` lies in the closed disk of radius `√R` about `C / 2`. -/
def memOK (R h : Quad m) (C P Q : CycQ m) : Bool :=
  match ((P - C) * conj (P - C)).toQuad?, (Q * conj Q).toQuad?,
      ((P - C) * conj Q + conj (P - C) * Q).toQuad? with
  | some n₁, some n₂, some n₃ => Quad.nonneg₂ (⟨4, 0⟩ * R - n₁ - n₂ * h) (-n₃) h
  | _, _, _ => false

/-- Soundness of `TDCSG.CycQ.memOK`: the point `(P + Q √h) / 2` lies in the closed disk of radius
`r ≥ √R` about `C / 2`. -/
theorem mem_of_memOK (hζ : IsRoot n m ζ) {R h : Quad m} {C P Q : CycQ m}
    (H : memOK R h C P Q = true) (hh : 0 ≤ h.toReal) {r : ℝ} (hr : √R.toReal ≤ r) :
    pt ζ √h.toReal P Q ∈ closedBall (embed ζ C / 2) r := by
  simp only [memOK] at H
  split at H
  case h_2 => exact absurd H Bool.false_ne_true
  rename_i n₁ n₂ n₃ e₁ e₂ e₃
  have H' := Quad.nonneg₂_sound hh H
  simp only [Quad.toReal_sub, Quad.toReal_mul, Quad.toReal_neg] at H'
  have h4 : (⟨4, 0⟩ : Quad m).toReal = 4 := by simp [Quad.toReal]
  rw [h4] at H'
  set s := √h.toReal
  have hs : s * s = h.toReal := Real.mul_self_sqrt hh
  set X := embed ζ (P - C)
  set Y := embed ζ Q
  have k₁ := embed_of_toQuad? hζ e₁
  have k₂ := embed_of_toQuad? hζ e₂
  have k₃ := embed_of_toQuad? hζ e₃
  simp only [embed_mul hζ, embed_add, embed_conj hζ] at k₁ k₂ k₃
  have hnorm : ((‖X + Y * s‖ ^ 2 : ℝ) : ℂ) =
      ((n₁.toReal + n₃.toReal * s + n₂.toReal * h.toReal : ℝ) : ℂ) := by
    push_cast
    rw [← mul_conj', map_add, map_mul, conj_ofReal, ← hs]
    push_cast
    linear_combination k₁ + (s : ℂ) * k₃ + (s : ℂ) ^ 2 * k₂
  have hnorm' : ‖X + Y * s‖ ^ 2 = n₁.toReal + n₃.toReal * s + n₂.toReal * h.toReal := by
    exact_mod_cast hnorm
  have hR : 0 ≤ R.toReal := by nlinarith [sq_nonneg ‖X + Y * s‖]
  have hr0 : 0 ≤ r := (Real.sqrt_nonneg _).trans hr
  have hr2 : R.toReal ≤ r ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hr 2
    rwa [Real.sq_sqrt hR] at this
  rw [mem_closedBall, dist_eq_norm, pt]
  have hXY : (embed ζ P + Y * s) / 2 - embed ζ C / 2 = (X + Y * s) / 2 := by
    simp only [X, embed_sub]
    ring
  rw [hXY, norm_div, Complex.norm_two, div_le_iff₀ two_pos]
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, hnorm']
  nlinarith

/-- The exact test that a word is valid at `(P + Q √h) / 2` at every radius `r ≥ √R`. -/
def validOK (R h : Quad m) : List Letter → CycQ m → CycQ m → Bool
  | [], _, _ => true
  | l :: w, P, Q => memOK R h (center l) P Q && validOK R h w (stepP l P) (rot l Q)

/-- The global rotation of a word, on the rational part of a doubled point. -/
def runP : List Letter → CycQ m → CycQ m
  | [], P => P
  | l :: w, P => runP w (stepP l P)

/-- The global rotation of a word, on the coefficient of the square root of a doubled point. -/
def runQ : List Letter → CycQ m → CycQ m
  | [], Q => Q
  | l :: w, Q => runQ w (rot l Q)

/-- `TDCSG.CycQ.runP` and `TDCSG.CycQ.runQ` compute the global rotation of a word on the point
`(P + Q s) / 2`. -/
theorem globalWord_pt (hζ : IsRoot n m ζ) (s : ℝ) (w : List Letter) (P Q : CycQ m) :
    globalWord n w (pt ζ s P Q) = pt ζ s (runP w P) (runQ w Q) := by
  induction w generalizing P Q with
  | nil => rfl
  | cons l w ih => rw [globalWord, ← pt_step hζ, ih, runP, runQ]

/-- Soundness of `TDCSG.CycQ.validOK`: the word is valid at `(P + Q √h) / 2` at every radius
`r ≥ √R`. -/
theorem ptValid_of_validOK (hζ : IsRoot n m ζ) {R h : Quad m} (hh : 0 ≤ h.toReal) {r : ℝ}
    (hr : √R.toReal ≤ r) {w : List Letter} {P Q : CycQ m} (H : validOK R h w P Q = true) :
    PtValid n r w (pt ζ √h.toReal P Q) := by
  induction w generalizing P Q with
  | nil => trivial
  | cons l w ih =>
    simp only [validOK, Bool.and_eq_true] at H
    refine ⟨?_, ?_⟩
    · have := mem_of_memOK hζ H.1 hh hr
      rwa [embed_center, mul_div_cancel_left₀ _ two_ne_zero] at this
    · rw [← pt_step hζ]
      exact ih H.2

/-! ### Parameters on the line -/

/-- The parameter `(A + B₁ √h₁ + B₂ √h₂) / 2` of a point of the line, stored doubled. -/
@[ext]
structure Lin (m : ℕ) where
  /-- Twice the part in `ℚ(√m)`. -/
  A : Quad m
  /-- Twice the coefficient of `√h₁`. -/
  B₁ : Quad m
  /-- Twice the coefficient of `√h₂`. -/
  B₂ : Quad m
  deriving DecidableEq, Repr

namespace Lin

/-- The real number `(A + B₁ √h₁ + B₂ √h₂) / 2`. -/
noncomputable def val (h₁ h₂ : Quad m) (x : Lin m) : ℝ :=
  (x.A.toReal + x.B₁.toReal * √h₁.toReal + x.B₂.toReal * √h₂.toReal) / 2

/-- The exact test for `x ≤ y`. -/
def le (h₁ h₂ : Quad m) (x y : Lin m) : Bool :=
  Quad.nonneg₃ (y.A - x.A) (y.B₁ - x.B₁) (y.B₂ - x.B₂) h₁ h₂

/-- Soundness of `TDCSG.CycQ.Lin.le`. -/
theorem val_le_of_le {h₁ h₂ : Quad m} (hh₁ : 0 ≤ h₁.toReal) (hh₂ : 0 ≤ h₂.toReal) {x y : Lin m}
    (H : le h₁ h₂ x y = true) : x.val h₁ h₂ ≤ y.val h₁ h₂ := by
  have := Quad.nonneg₃_sound hh₁ hh₂ H
  simp only [Quad.toReal_sub] at this
  simp only [val]
  linarith

/-- The isometry `t ↦ t + c / 2` (if `pos`) or `t ↦ c / 2 - t`, on doubled parameters. -/
def act (pos : Bool) (c : Quad m) (x : Lin m) : Lin m :=
  if pos then ⟨x.A + c, x.B₁, x.B₂⟩ else ⟨c - x.A, -x.B₁, -x.B₂⟩

/-- `TDCSG.CycQ.Lin.act` computes the isometry `TDCSG.Renormalization.ract` on parameters. -/
theorem val_act (h₁ h₂ : Quad m) (pos : Bool) (c : Quad m) (x : Lin m) :
    (act pos c x).val h₁ h₂ = ract pos (c.toReal / 2) (x.val h₁ h₂) := by
  cases pos <;> simp only [act, ract, val, Bool.false_eq_true, ite_false, ite_true,
    Quad.toReal_add, Quad.toReal_sub, Quad.toReal_neg] <;> ring

/-- Multiplication by `e ∈ ℤ[√m]`. -/
def scale (e : Quad m) (x : Lin m) : Lin m := ⟨e * x.A, e * x.B₁, e * x.B₂⟩

/-- `TDCSG.CycQ.Lin.scale e` multiplies the parameter by `e`. -/
theorem val_scale (h₁ h₂ : Quad m) (e : Quad m) (x : Lin m) :
    (scale e x).val h₁ h₂ = e.toReal * x.val h₁ h₂ := by
  simp only [scale, val, Quad.toReal_mul]
  ring

end Lin

/-! ### Families of words -/

/-- A member of a family: a word, which acts on the line as `t ↦ t + c / 2` (if `pos`) or
`t ↦ c / 2 - t`, on the domain `[lo / 2, hi / 2]`. All numbers are stored doubled. -/
structure Entry (m : ℕ) where
  /-- The word. -/
  word : List Letter
  /-- Whether the word acts as a translation (rather than a reflection) of the line. -/
  pos : Bool
  /-- Twice the shift. -/
  c : Quad m
  /-- Twice the lower end point of the domain. -/
  lo : Lin m
  /-- Twice the upper end point of the domain. -/
  hi : Lin m

instance : Inhabited (Entry m) := ⟨⟨[], true, 0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩⟩

/-- A piece of the closure data: on the interval from `x / 2` to `y / 2`, the composite of the
family members with indices `seq`, applied left to right. -/
structure Piece (m : ℕ) where
  /-- The indices of the family members, applied left to right. -/
  seq : List ℕ
  /-- Twice the lower end point. -/
  x : Lin m
  /-- Twice the upper end point. -/
  y : Lin m

/-- The exact test that a doubled point `(P + Q √h) / 2` with parameter `(A + B √h) / 2` is
mapped by the word `w`, validly at every radius `r ≥ √R`, to the point with parameter
`(A' + B' √h) / 2`, on the line through `p` in the direction `V`. -/
def wordOK (R h : Quad m) (p V : CycQ m) (w : List Letter) (A B A' B' : Quad m) : Bool :=
  validOK R h w (p + p + V * ofQuad A) (V * ofQuad B) &&
    decide (runP w (p + p + V * ofQuad A) = p + p + V * ofQuad A') &&
    decide (runQ w (V * ofQuad B) = V * ofQuad B')

/-- The exact test that the word of `e` maps the point of parameter `x / 2` as it should. The
parameter may involve one of the two square roots. -/
def endOK (R h₁ h₂ : Quad m) (p V : CycQ m) (e : Entry m) (x : Lin m) : Bool :=
  let y := Lin.act e.pos e.c x
  decide (x.B₂ = 0) && wordOK R h₁ p V e.word x.A x.B₁ y.A y.B₁ ||
    decide (x.B₁ = 0) && wordOK R h₂ p V e.word x.A x.B₂ y.A y.B₂

/-- The exact check of realization: every word is valid, with the right action, at both end
points of its domain. -/
def realizeOK (R h₁ h₂ : Quad m) (p V : CycQ m) (F : List (Entry m)) : Bool :=
  F.all fun e ↦ endOK R h₁ h₂ p V e e.lo && endOK R h₁ h₂ p V e e.hi

/-- The composite of the family members with indices `gs`, applied left to right, as a pair
(`pos`, twice the shift). -/
def chainComp (F : List (Entry m)) : List ℕ → Bool × Quad m
  | [] => (true, 0)
  | g :: gs =>
    let e := F.getD g default
    let r := chainComp F gs
    (r.1 == e.pos, (if r.1 then e.c else -e.c) + r.2)

/-- The exact test that `x / 2` lies in the domain of `e`. -/
def inDom (h₁ h₂ : Quad m) (e : Entry m) (x : Lin m) : Bool :=
  Lin.le h₁ h₂ e.lo x && Lin.le h₁ h₂ x e.hi

/-- The exact test that along the chain `gs` the images of `x / 2` and `y / 2` lie in the
domain of the next member. -/
def chainOK (h₁ h₂ : Quad m) (F : List (Entry m)) : List ℕ → Lin m → Lin m → Bool
  | [], _, _ => true
  | g :: gs, x, y =>
    let e := F.getD g default
    decide (g < F.length) && inDom h₁ h₂ e x && inDom h₁ h₂ e y &&
      chainOK h₁ h₂ F gs (Lin.act e.pos e.c x) (Lin.act e.pos e.c y)

/-- The exact test that the pieces cover the interval from `x₀ / 2` to `e / 2` consecutively,
each one realizing the isometry `t ↦ ±t + c / 2` by a valid chain. -/
def piecesOK (h₁ h₂ : Quad m) (F : List (Entry m)) (pos : Bool) (c : Quad m) :
    Lin m → Lin m → List (Piece m) → Bool
  | _, _, [] => false
  | x₀, e, [p] => decide (p.x = x₀) && decide (p.y = e) && chainOK h₁ h₂ F p.seq p.x p.y &&
      decide (chainComp F p.seq = (pos, c))
  | x₀, e, p :: q :: ps => decide (p.x = x₀) && chainOK h₁ h₂ F p.seq p.x p.y &&
      decide (chainComp F p.seq = (pos, c)) && piecesOK h₁ h₂ F pos c p.y e (q :: ps)

/-- The exact check of closure under rescaling by `ε`: for each member, its domain rescaled by
`ε` is covered by the listed pieces, which realize the member rescaled by `ε`. -/
def closureOK (h₁ h₂ ε : Quad m) (F : List (Entry m)) (P : List (List (Piece m))) : Bool :=
  (List.range F.length).all fun i ↦
    let e := F.getD i default
    piecesOK h₁ h₂ F e.pos (ε * e.c) (e.lo.scale ε) (e.hi.scale ε) (P.getD i [])

section Soundness

variable {h₁ h₂ : Quad m} (hh₁ : 0 ≤ h₁.toReal) (hh₂ : 0 ≤ h₂.toReal) (F : List (Entry m))

/-- The family, as real data for `TDCSG.Renormalization.renormalize`. -/
abbrev famS (i : ℕ) : Prop := i < F.length
/-- The kinds of the family members. -/
abbrev famPos (i : ℕ) : Bool := (F.getD i default).pos
/-- The shifts of the family members. -/
noncomputable abbrev famC (i : ℕ) : ℝ := (F.getD i default).c.toReal / 2
/-- The lower end points of the domains. -/
noncomputable abbrev famLo (h₁ h₂ : Quad m) (i : ℕ) : ℝ := (F.getD i default).lo.val h₁ h₂
/-- The upper end points of the domains. -/
noncomputable abbrev famHi (h₁ h₂ : Quad m) (i : ℕ) : ℝ := (F.getD i default).hi.val h₁ h₂

include hh₁ hh₂ in
/-- Soundness of `TDCSG.CycQ.chainOK`: every parameter between `x / 2` and `y / 2` is carried
along the chain `gs` by members applied inside their domains, to its image under the composite. -/
theorem isComposite_of_chainOK {gs : List ℕ} {x y : Lin m} (H : chainOK h₁ h₂ F gs x y = true)
    {s : ℝ} (hs : s ∈ Set.uIcc (x.val h₁ h₂) (y.val h₁ h₂)) :
    IsComposite (famS F) (famPos F) (famC F) (famLo F h₁ h₂) (famHi F h₁ h₂) s gs
      (ract (chainComp F gs).1 ((chainComp F gs).2.toReal / 2) s) := by
  induction gs generalizing x y s with
  | nil => simp [IsComposite, chainComp, ract]
  | cons g gs ih =>
    simp only [chainOK, inDom, Bool.and_eq_true, decide_eq_true_eq] at H
    obtain ⟨⟨⟨hg, hx₁, hx₂⟩, hy₁, hy₂⟩, hrest⟩ := H
    set e := F.getD g default
    refine ⟨hg, ?_, ?_⟩
    · have h1 := Lin.val_le_of_le hh₁ hh₂ hx₁
      have h2 := Lin.val_le_of_le hh₁ hh₂ hx₂
      have h3 := Lin.val_le_of_le hh₁ hh₂ hy₁
      have h4 := Lin.val_le_of_le hh₁ hh₂ hy₂
      rw [Set.mem_uIcc] at hs
      constructor <;> rcases hs with ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩ <;> linarith
    · have hs' := ract_mem_uIcc (pos := e.pos) (c := e.c.toReal / 2) hs
      rw [← Lin.val_act, ← Lin.val_act] at hs'
      have := ih hrest hs'
      simp only [chainComp]
      rw [ract_ract] at this
      convert this using 2
      split_ifs <;> simp [e] <;> ring

include hh₁ hh₂ in
/-- Soundness of `TDCSG.CycQ.piecesOK`: on the interval from `x₀ / 2` to `e / 2` the isometry
`t ↦ ±t + c / 2` is, pointwise, a composite of family members applied inside their domains. -/
theorem exists_isComposite_of_piecesOK {pos : Bool} {c : Quad m} {ps : List (Piece m)} :
    ∀ {x₀ e : Lin m}, piecesOK h₁ h₂ F pos c x₀ e ps = true →
    ∀ s ∈ Set.Icc (x₀.val h₁ h₂) (e.val h₁ h₂), ∃ gs,
      IsComposite (famS F) (famPos F) (famC F) (famLo F h₁ h₂) (famHi F h₁ h₂) s gs
        (ract pos (c.toReal / 2) s) := by
  induction ps with
  | nil => intro _ _ H; simp [piecesOK] at H
  | cons p ps ih =>
    intro x₀ e H s hs
    have piece : chainOK h₁ h₂ F p.seq p.x p.y = true → chainComp F p.seq = (pos, c) →
        s ∈ Set.Icc (p.x.val h₁ h₂) (p.y.val h₁ h₂) → ∃ gs,
        IsComposite (famS F) (famPos F) (famC F) (famLo F h₁ h₂) (famHi F h₁ h₂) s gs
          (ract pos (c.toReal / 2) s) := by
      intro hc hcomp hsp
      refine ⟨p.seq, ?_⟩
      have := isComposite_of_chainOK hh₁ hh₂ F hc (Set.Icc_subset_uIcc hsp)
      rwa [hcomp] at this
    match ps, H with
    | [], H =>
      simp only [piecesOK, Bool.and_eq_true, decide_eq_true_eq] at H
      obtain ⟨⟨⟨rfl, rfl⟩, hc⟩, hcomp⟩ := H
      exact piece hc hcomp hs
    | q :: qs, H =>
      simp only [piecesOK, Bool.and_eq_true, decide_eq_true_eq] at H
      obtain ⟨⟨⟨rfl, hc⟩, hcomp⟩, hrest⟩ := H
      rcases le_or_gt s (p.y.val h₁ h₂) with h | h
      · exact piece hc hcomp ⟨hs.1, h⟩
      · exact ih hrest s ⟨h.le, hs.2⟩

end Soundness

variable {R h₁ h₂ ε : Quad m} {p V : CycQ m} {F : List (Entry m)} {P : List (List (Piece m))}

/-- The point `(2p + A V + (B V) s) / 2` is `p + ((A + B s) / 2) V`. -/
theorem pt_ofQuad (hζ : IsRoot n m ζ) (s : ℝ) (A B : Quad m) :
    pt ζ s (p + p + V * ofQuad A) (V * ofQuad B) =
      embed ζ p + (((A.toReal + B.toReal * s) / 2 : ℝ) : ℂ) * embed ζ V := by
  simp only [pt, embed_add, embed_mul hζ, embed_ofQuad hζ]
  push_cast
  ring

/-- A word checked by `TDCSG.CycQ.wordOK` is valid at the point of parameter `(A + B √h) / 2`
and maps it to the point of parameter `(A' + B' √h) / 2`. -/
theorem of_wordOK (hζ : IsRoot n m ζ) {h : Quad m} (hh : 0 ≤ h.toReal) {r : ℝ}
    (hr : √R.toReal ≤ r) {w : List Letter} {A B A' B' : Quad m}
    (H : wordOK R h p V w A B A' B' = true) :
    PtValid n r w (embed ζ p + (((A.toReal + B.toReal * √h.toReal) / 2 : ℝ) : ℂ) * embed ζ V) ∧
      globalWord n w (embed ζ p + (((A.toReal + B.toReal * √h.toReal) / 2 : ℝ) : ℂ) *
        embed ζ V) =
        embed ζ p + (((A'.toReal + B'.toReal * √h.toReal) / 2 : ℝ) : ℂ) * embed ζ V := by
  simp only [wordOK, Bool.and_eq_true, decide_eq_true_eq] at H
  obtain ⟨⟨hv, hP⟩, hQ⟩ := H
  rw [← pt_ofQuad hζ, ← pt_ofQuad hζ]
  exact ⟨ptValid_of_validOK hζ hh hr hv, by rw [globalWord_pt hζ, hP, hQ]⟩

/-- Soundness of `TDCSG.CycQ.endOK`: the word of `e` is valid at the point of parameter `x / 2`
and maps it to the point of parameter given by the action of `e`. -/
theorem of_endOK (hζ : IsRoot n m ζ) (hh₁ : 0 ≤ h₁.toReal) (hh₂ : 0 ≤ h₂.toReal) {r : ℝ}
    (hr : √R.toReal ≤ r) {e : Entry m} {x : Lin m} (H : endOK R h₁ h₂ p V e x = true) :
    PtValid n r e.word (embed ζ p + (x.val h₁ h₂ : ℂ) * embed ζ V) ∧
      globalWord n e.word (embed ζ p + (x.val h₁ h₂ : ℂ) * embed ζ V) =
        embed ζ p + (ract e.pos (e.c.toReal / 2) (x.val h₁ h₂) : ℂ) * embed ζ V := by
  rw [← Lin.val_act]
  simp only [endOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at H
  rcases H with ⟨hB, H⟩ | ⟨hB, H⟩
  · have hB' : (Lin.act e.pos e.c x).B₂ = 0 := by
      cases e.pos <;> simp [Lin.act, hB, show -(0 : Quad m) = 0 from rfl]
    have := of_wordOK hζ hh₁ hr H
    simpa [Lin.val, hB, hB'] using this
  · have hB' : (Lin.act e.pos e.c x).B₁ = 0 := by
      cases e.pos <;> simp [Lin.act, hB, show -(0 : Quad m) = 0 from rfl]
    have := of_wordOK hζ hh₂ hr H
    simpa [Lin.val, hB, hB'] using this

/-- **Exact renormalization.** If a family passes the realization and closure checks, then for
every `k` and every member `t ↦ ±t + c`, every point of parameter `t` in the domain rescaled by
`ε ^ k` has the point of parameter `±t + ε ^ k c` in its orbit, for every radius `r ≥ √R`. -/
theorem mem_orbit_of_checks (hζ : IsRoot n m ζ) (hh₁ : 0 ≤ h₁.toReal) (hh₂ : 0 ≤ h₂.toReal)
    (hε : 0 < ε.toReal) (hreal : realizeOK R h₁ h₂ p V F = true)
    (hclos : closureOK h₁ h₂ ε F P = true) {r : ℝ} (hr : √R.toReal ≤ r) (k : ℕ) {i : ℕ}
    (hi : i < F.length) {t : ℝ}
    (ht : t ∈ Set.Icc (ε.toReal ^ k * (F.getD i default).lo.val h₁ h₂)
      (ε.toReal ^ k * (F.getD i default).hi.val h₁ h₂)) :
    embed ζ p + (ract (F.getD i default).pos (ε.toReal ^ k * ((F.getD i default).c.toReal / 2))
      t : ℂ) * embed ζ V ∈ orbit n n r r (embed ζ p + t * embed ζ V) := by
  refine renormalize (famS F) (famPos F) (famC F) (famLo F h₁ h₂) (famHi F h₁ h₂)
    (fun t t' ↦ embed ζ p + (t' : ℂ) * embed ζ V ∈ orbit n n r r (embed ζ p + t * embed ζ V))
    (fun t ↦ mem_orbit_self _ _ _ _ _) (fun _ _ _ h₁ h₂ ↦ mem_orbit_trans h₁ h₂) hε ?_ ?_ k hi ht
  · intro j hj t ht
    have hmem : F.getD j default ∈ F := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact List.getElem_mem hj
    have hall := List.all_eq_true.1 hreal _ hmem
    simp only [Bool.and_eq_true] at hall
    obtain ⟨hlo, hhi⟩ := hall
    obtain ⟨vlo, glo⟩ := of_endOK hζ hh₁ hh₂ hr hlo
    obtain ⟨vhi, ghi⟩ := of_endOK hζ hh₁ hh₂ hr hhi
    rw [← applyWord_ract (wordValid_of_ptValid vlo vhi) glo ghi ht]
    exact applyWord_mem_orbit _ (mem_orbit_self _ _ _ _ _)
  · intro j hj s hs
    have hall := List.all_eq_true.1 hclos j (List.mem_range.2 hj)
    simp only at hall
    have := exists_isComposite_of_piecesOK hh₁ hh₂ F hall s
      (by rwa [Lin.val_scale, Lin.val_scale])
    rw [Quad.toReal_mul, mul_div_assoc] at this
    exact this

end CycQ

end TDCSG

end
