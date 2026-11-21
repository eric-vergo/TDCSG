/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Field

/-!
# Exact signs in multi-quadratic extensions of `ℚ(ζ_n)⁺`

Let `K = ℚ(ζ_n)⁺ ⊂ ℝ` be the real subfield, embedded by the identity embedding, and let
`r_0, …, r_{k-1}` be **positive** real elements of `ℤ[ζ_n]⁺`. A *tower element* is a real number

`x = ∑_{I ⊆ {0, …, k-1}} a_I ∏_{i ∈ I} √r_i`,  `a_I ∈ ℤ[ζ_n]⁺`,

stored as the array of its `2 ^ k` coefficients `a_I`, the subset `I` encoded as the bit mask of
the index (bit `i` set means the factor `√r_i`). The square roots are the positive ones. Nothing
here assumes that the `√r_i` are independent over `K`: the representation of a number need not
be unique, but its value, and so its sign, is well defined.

## Products

`√r_I · √r_J = (∏_{i ∈ I ∩ J} r_i) · √r_{I △ J}` with `√r_I = ∏_{i ∈ I} √r_i`, so `mul` is the
bilinear extension of this rule; it is exact (coefficients are arbitrary-precision integers).

## Signs

`sign` decides the sign of `x` exactly by induction on `k`.

* `k = 0`: `x = a_∅ ∈ ℤ[ζ_n]⁺`, decided by `RealSign.sign` (below).
* `k > 0`: write `x = P + Q √r` with `r = r_{k-1}` and `P`, `Q` tower elements in the first
  `k - 1` radicals (`P` holds the coefficients whose index has bit `k - 1` clear, `Q` the others).
  Let `s_P`, `s_Q` be their signs (by induction). If `s_Q = 0` the sign is `s_P`; if `s_P = 0` it
  is `s_Q` (as `√r > 0`); if `s_P = s_Q` it is that common sign. Otherwise `P` and `Q √r` have
  opposite signs, and `|P| > |Q| √r` exactly when `P² - r Q² > 0`; so the sign is
  `s_P · sign (P² - r Q²)`, where `P² - r Q²` is again a tower element in `k - 1` radicals. In
  particular `x = 0` exactly when the result is `0`.

Every step is an exact identity between real numbers, so `sign` returns the true sign whenever
the base case does; `none` is returned only if `CycField.signReal` reports its (provably
unreachable) precision failure, and callers treat it as a fatal error.

## Signs in `ℤ[ζ_n]⁺` itself

For a real element `x = Σ x_i ζ^i` (power basis) we have `2x = x + x̄ = Σ x_i θ_i` with
`θ_i = ζ^i + ζ^{-i}`. When the real subfield has degree `m ≤ 2` this gives a sign test in integer
arithmetic only (`RealSign`):

* `m = 1` (`n = 3, 4, 6`): every `θ_i` is an integer, so `2x ∈ ℤ`.
* `m = 2` (`n = 5, 8, 10, 12`): write `θ_i = p_i + q_i θ` in the basis `1, θ`, `θ = θ_1`, and
  `θ² = s_0 + s_1 θ` (all checked exactly by `CycField.toRealBasis`). Then `θ` is the larger root
  `(s_1 + √D) / 2` of `X² - s_1 X - s_0`, `D = s_1² + 4 s_0`, because `2 cos (2π/n)` exceeds its
  conjugate `2 cos (2πk/n)` (`1 < k < n/2`). With `P = Σ x_i p_i`, `Q = Σ x_i q_i` we get
  `4x = u + v √D`, `u = 2P + s_1 Q`, `v = Q`, whose sign is that of `u` if `v = 0`, of `v` if
  `u = 0`, the common sign if they agree, and otherwise `sign u · sign (u² - D v²)`.

For `m > 2` the sign is `CycField.signReal` (exact zero test, then certified ball evaluation; see
`TDCSGCompute.Field`).
-/

namespace TDCSGCompute

/-- Coefficients of a tower element, indexed by bit masks of radicals (see the module docstring). -/
abbrev TowerElem := Array Elem

/-- Exact signs of real elements of `ℤ[ζ_n]` (see the module docstring). -/
structure RealSign where
  /-- The ring. -/
  F : CycField
  /-- `m ≤ 2`: the coordinates `(p_i, q_i)` of `θ_i` in the basis `1, θ_1` (`q_i = 0` if `m = 1`),
  for `i < φ(n)`; empty if `m > 2`. -/
  pq : Array (Int × Int)
  /-- `s_1` (for `m = 2`). -/
  s1 : Int
  /-- `D = s_1² + 4 s_0` (for `m = 2`). -/
  D : Int

/-- Set up the sign test for `F`. -/
def RealSign.make (F : CycField) : RealSign := Id.run do
  let m := F.realDim
  if m > 2 then return { F, pq := #[], s1 := 0, D := 0 }
  let mut pq : Array (Int × Int) := #[]
  for i in [0:F.deg] do
    match F.toRealBasis F.thetas[i]! with
    | some b => pq := pq.push (b[0]?.getD 0, b[1]?.getD 0)
    | none => return { F, pq := #[], s1 := 0, D := 0 }
  if m == 1 then return { F, pq, s1 := 0, D := 0 }
  match F.toRealBasis (F.mul F.thetas[1]! F.thetas[1]!) with
  | some b =>
    let s0 := b[0]?.getD 0
    let s1 := b[1]?.getD 0
    return { F, pq, s1, D := s1 * s1 + 4 * s0 }
  | none => return { F, pq := #[], s1 := 0, D := 0 }

/-- The exact sign of a real element `x` (power basis). -/
def RealSign.sign (S : RealSign) (x : Elem) : Option Int :=
  if S.pq.isEmpty || x.size != S.pq.size then S.F.signReal x else Id.run do
  let mut P : Int := 0
  let mut Q : Int := 0
  for i in [0:x.size] do
    let c := x[i]!
    if c != 0 then
      let (p, q) := S.pq[i]!
      P := P + c * p
      Q := Q + c * q
  let sgn (z : Int) : Int := if z > 0 then 1 else if z < 0 then -1 else 0
  if S.F.realDim == 1 then return some (sgn P)
  let u := 2 * P + S.s1 * Q
  let v := Q
  let su := sgn u
  let sv := sgn v
  if sv == 0 then return some su
  if su == 0 || su == sv then return some sv
  return some (su * sgn (u * u - S.D * v * v))

namespace Tower

/-- The zero element with `2 ^ k` coefficients. -/
def zero (F : CycField) (k : Nat) : TowerElem := Array.replicate (2 ^ k) F.zero

/-- The product of the radicands `r_i` over the bits `i` set in `mask`. -/
def radProd (F : CycField) (rs : Array Elem) (mask : Nat) : Elem := Id.run do
  let mut t := F.one
  for b in [0:rs.size] do
    if (mask >>> b) % 2 == 1 then t := F.mul t rs[b]!
  return t

/-- The product of two tower elements over the radicands `rs`. -/
def mul (F : CycField) (rs : Array Elem) (x y : TowerElem) : TowerElem := Id.run do
  let sz := x.size
  let mut out := Array.replicate sz F.zero
  for i in [0:sz] do
    let xi := x[i]!
    if F.isZero xi then continue
    for j in [0:sz] do
      let yj := y[j]!
      if F.isZero yj then continue
      let mut t := F.mul xi yj
      let common := i &&& j
      if common != 0 then t := F.mul t (radProd F rs common)
      let k := i ^^^ j
      out := out.set! k (F.add out[k]! t)
  return out

/-- Difference of two tower elements. -/
def sub (F : CycField) (x y : TowerElem) : TowerElem := Array.zipWith (F.sub · ·) x y

/-- Multiplication of every coefficient by an element of `ℤ[ζ_n]⁺`. -/
def scale (F : CycField) (r : Elem) (x : TowerElem) : TowerElem := x.map (F.mul r ·)

/-- The sign of a tower element over the first `k` radicands of `rs` (`x` has `2 ^ k`
coefficients); see the module docstring. -/
def signAux (S : RealSign) (rs : Array Elem) : Nat → TowerElem → Option Int
  | 0, x => S.sign x[0]!
  | k + 1, x => do
    let half := 2 ^ k
    let P := x.extract 0 half
    let Q := x.extract half (2 * half)
    let F := S.F
    let sQ ← if Q.all F.isZero then pure 0 else signAux S rs k Q
    if sQ == 0 then return (← signAux S rs k P)
    let sP ← if P.all F.isZero then pure 0 else signAux S rs k P
    if sP == 0 then return sQ
    if sP == sQ then return sP
    let rsk := rs.extract 0 k
    let D := sub F (mul F rsk P P) (scale F rs[k]! (mul F rsk Q Q))
    let sD ← signAux S rs k D
    return sP * sD

/-- The sign (`-1`, `0`, `1`) of a tower element over the positive radicands `rs`. -/
def sign (S : RealSign) (rs : Array Elem) (x : TowerElem) : Option Int :=
  signAux S rs rs.size x

end Tower

end TDCSGCompute
