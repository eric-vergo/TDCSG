/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Ball

/-!
# Exact arithmetic in `ℤ[ζ_n]`

`CycField.make n` sets up the ring `ℤ[ζ_n]`, `ζ_n = e^{2πi/n}`, for `n ≥ 3`. An element (`Elem`) is
its coefficient vector in the power basis `1, ζ, …, ζ^{d-1}`, `d = φ(n)`, i.e. a polynomial of
degree `< d` taken modulo the cyclotomic polynomial `Φ_n`. Because `Φ_n` is the minimal polynomial
of `ζ` and is monic, this representation is unique: two elements are equal exactly when their
coefficient vectors are equal. In particular an element is zero exactly when all its coefficients
are zero, which is how the engine tests equality and boundary contact.

Coefficients are arbitrary-precision `Int`s here, so no arithmetic in this file can overflow. The
compact fixed-width encoding used for storage lives in `TDCSGCompute.Store`.

## Real elements

The real subfield `ℚ(ζ_n)⁺` has the basis `1, θ_1, …, θ_{m-1}`, `m = d / 2`, with
`θ_k = ζ^k + ζ^{-k} = 2 cos (2πk/n)`. Each `θ_k` is a monic polynomial of degree `k` in `θ_1`, so
this is also a `ℤ`-basis of `ℤ[ζ_n]⁺ = ℤ[θ_1]`. `ofRealBasis` and `toRealBasis` convert between
these coordinates and the power basis; `toRealBasis` checks its answer exactly.

## Embeddings and signs

`cosB`, `sinB` hold certified enclosures of `cos (2πk/n)`, `sin (2πk/n)` (see
`TDCSGCompute.Ball`). A real element `x = ∑ x_i ζ^i` has value `∑ x_i cos (2πi/n)` in the identity
embedding (its imaginary part `∑ x_i sin (2πi/n)` is `0`). `signReal` decides the sign of a real
element: zero by the exact test, otherwise by evaluating that sum in ball arithmetic, doubling the
precision until the ball excludes `0`. This terminates: a nonzero `x ∈ ℤ[ζ_n]⁺` has
`|N(x)| ≥ 1` and its other `m - 1` real conjugates are bounded by `B = ∑ |x_i|`, so
`|x| ≥ B^{-(m-1)}`, and a precision of `m * (log₂ B + 2) + 64` bits always decides the sign.
`signReal` returns `none` only if that bound is exceeded, which the argument rules out; callers
treat `none` as a fatal error.

`cosF`, `sinF` are double-precision copies of the same tables, with a certified bound `trigErr` on
their error, for the floating-point filter in `TDCSGCompute.Disk`.
-/

namespace TDCSGCompute

/-- The float `0`, as a constant (float literals in compiled code are otherwise rebuilt at each use). -/
def fl0 : Float := 0

/-- The float `1`. -/
def fl1 : Float := 1

/-- The float `2`. -/
def fl2 : Float := 2

/-- The float `3`. -/
def fl3 : Float := 3

/-- The float `-1`. -/
def flm1 : Float := -1

/-- Integer polynomials, with the coefficient of `X ^ i` at index `i`. -/
abbrev IntPoly := Array Int

namespace IntPoly

/-- Quotient and remainder of `p` by a monic polynomial `m` of positive degree. -/
def divModMonic (p m : IntPoly) : IntPoly × IntPoly := Id.run do
  let k := m.size - 1
  if p.size ≤ k then return (#[], p)
  let mut r := p
  let mut q : IntPoly := Array.replicate (p.size - k) 0
  for t in [0:p.size - k] do
    let i := p.size - 1 - t
    let c := r[i]!
    if c != 0 then
      q := q.set! (i - k) c
      for j in [0:k + 1] do
        r := r.modify (i - k + j) (· - c * m[j]!)
  return (q, r.extract 0 k)

end IntPoly

/-- Euler's totient function. -/
def totient (n : Nat) : Nat := ((List.range n).filter (fun k ↦ Nat.gcd k n == 1)).length

/-- The cyclotomic polynomial `Φ_n`, for `n ≥ 1`, computed from `X ^ m - 1 = ∏_{e ∣ m} Φ_e` over
the divisors `m` of `n`. -/
def cyclotomic (n : Nat) : IntPoly := Id.run do
  let divs := (List.range (n + 1)).filter (fun m ↦ m > 0 && n % m == 0)
  let mut tab : Array (Nat × IntPoly) := #[]
  for m in divs do
    let mut p : IntPoly := ((Array.replicate (m + 1) (0 : Int)).set! 0 (-1)).set! m 1
    for (e, q) in tab do
      if m % e == 0 then p := (IntPoly.divModMonic p q).1
    tab := tab.push (m, p)
  return tab.back!.2

/-- An element of `ℤ[ζ_n]` as its coefficient vector in the power basis. -/
abbrev Elem := Array Int

/-- Gauss–Jordan elimination: for a `rows × cols` rational matrix `A` of full column rank, returns
a `rows × rows` matrix `E` with `E * A` equal to the identity in its first `cols` rows and zero
below. Returns `none` if `A` does not have full column rank. -/
def leftReducer (A : Array (Array Rat)) (cols : Nat) : Option (Array (Array Rat)) := Id.run do
  let rows := A.size
  let mut M := A
  let mut E : Array (Array Rat) :=
    (Array.range rows).map fun i ↦ (Array.replicate rows (0 : Rat)).set! i 1
  for c in [0:cols] do
    -- find a pivot in column `c` at or below row `c`
    let mut piv := rows
    for i in [c:rows] do
      if piv == rows && M[i]![c]! != 0 then piv := i
    if piv == rows then return none
    if piv != c then
      let (mc, mp) := (M[c]!, M[piv]!)
      M := (M.set! c mp).set! piv mc
      let (ec, ep) := (E[c]!, E[piv]!)
      E := (E.set! c ep).set! piv ec
    let inv := 1 / M[c]![c]!
    M := M.set! c (M[c]!.map (· * inv))
    E := E.set! c (E[c]!.map (· * inv))
    for i in [0:rows] do
      if i != c then
        let f := M[i]![c]!
        if f != 0 then
          let mc := M[c]!
          let ec := E[c]!
          M := M.set! i ((Array.range cols).map fun j ↦ M[i]![j]! - f * mc[j]!)
          E := E.set! i ((Array.range rows).map fun j ↦ E[i]![j]! - f * ec[j]!)
  return some E

/-- The ring `ℤ[ζ_n]` with the tables used by the engine. -/
structure CycField where
  /-- The order `n` of the root of unity. -/
  n : Nat
  /-- The degree `d = φ(n)`. -/
  deg : Nat
  /-- The cyclotomic polynomial `Φ_n`. -/
  phi : IntPoly
  /-- `pows[j] = ζ ^ j` in the power basis, for `0 ≤ j < n`. -/
  pows : Array Elem
  /-- `thetas[k] = ζ ^ k + ζ ^ (-k)`, for `0 ≤ k < n` (with `thetas[0] = 2`). -/
  thetas : Array Elem
  /-- Elimination matrix for `toRealBasis`. -/
  reducer : Array (Array Rat)
  /-- The base precision of `cosB`, `sinB`. -/
  basePrec : Nat
  /-- Enclosures of `cos (2πk/n)` at precision `basePrec`. -/
  cosB : Array Ball
  /-- Enclosures of `sin (2πk/n)` at precision `basePrec`. -/
  sinB : Array Ball
  /-- Doubles near `cos (2πk/n)`. -/
  cosF : FloatArray
  /-- Doubles near `sin (2πk/n)`. -/
  sinF : FloatArray
  /-- A certified bound on `|cosF[k] - cos (2πk/n)|` and `|sinF[k] - sin (2πk/n)|`. -/
  trigErr : Float

namespace CycField

variable (F : CycField)

/-- Dimension `m = φ(n) / 2` of the real subfield. -/
def realDim : Nat := F.deg / 2

/-- The zero element. -/
def zero : Elem := Array.replicate F.deg 0

/-- The integer `k` as an element. -/
def ofInt (k : Int) : Elem := F.zero.set! 0 k

/-- The element `1`. -/
def one : Elem := F.ofInt 1

/-- Sum. -/
def add (_ : CycField) (a b : Elem) : Elem := Array.zipWith (· + ·) a b

/-- Difference. -/
def sub (_ : CycField) (a b : Elem) : Elem := Array.zipWith (· - ·) a b

/-- Negation. -/
def neg (_ : CycField) (a : Elem) : Elem := a.map (- ·)

/-- Multiplication by an integer. -/
def smul (_ : CycField) (k : Int) (a : Elem) : Elem := a.map (k * ·)

/-- `a + k` for an integer `k`. -/
def addInt (_ : CycField) (a : Elem) (k : Int) : Elem := a.modify 0 (· + k)

/-- Whether `a = 0` (exact, by uniqueness of the representation). -/
def isZero (_ : CycField) (a : Elem) : Bool := a.all (· == 0)

/-- Reduce a polynomial in `ζ` of any degree modulo `Φ_n`. -/
def reducePoly (p : IntPoly) : Elem := Id.run do
  let d := F.deg
  let mut r := p
  if r.size < d then r := r ++ Array.replicate (d - r.size) 0
  for t in [0:r.size - d] do
    let i := r.size - 1 - t
    let c := r[i]!
    if c != 0 then
      for j in [0:d] do
        r := r.modify (i - d + j) (· - c * F.phi[j]!)
      r := r.set! i 0
  return r.extract 0 d

/-- Product. -/
def mul (a b : Elem) : Elem := Id.run do
  let d := F.deg
  let mut r : IntPoly := Array.replicate (2 * d) 0
  for i in [0:d] do
    let ai := a[i]!
    if ai != 0 then
      for j in [0:d] do
        r := r.modify (i + j) (· + ai * b[j]!)
  return F.reducePoly r

/-- Multiplication by `ζ`. -/
def mulZeta (a : Elem) : Elem := Id.run do
  let d := F.deg
  let top := a[d - 1]!
  let mut r : Elem := Array.emptyWithCapacity d
  r := r.push 0
  for i in [0:d - 1] do
    r := r.push a[i]!
  if top != 0 then
    for j in [0:d] do
      r := r.modify j (· - top * F.phi[j]!)
  return r

/-- Multiplication by `ζ⁻¹`. -/
def mulZetaInv (a : Elem) : Elem := Id.run do
  let d := F.deg
  let c := a[0]!
  let mut r : Elem := Array.emptyWithCapacity d
  for i in [1:d] do
    r := r.push a[i]!
  r := r.push 0
  if c != 0 then
    let zi := F.pows[F.n - 1]!
    for j in [0:d] do
      r := r.modify j (· + c * zi[j]!)
  return r

/-- `ζ ^ k` for any integer `k`. -/
def zetaPow (k : Int) : Elem := F.pows[(k % (F.n : Int)).toNat]!

/-- Multiplication by `ζ ^ k`. -/
def mulZetaPow (a : Elem) (k : Int) : Elem := F.mul a (F.zetaPow k)

/-- The Galois automorphism `σ_k : ζ ↦ ζ ^ k`, for `k` coprime to `n`. -/
def galois (k : Nat) (a : Elem) : Elem := Id.run do
  let d := F.deg
  let mut r : Elem := F.zero
  for i in [0:d] do
    let c := a[i]!
    if c != 0 then
      let v := F.pows[(i * k) % F.n]!
      for j in [0:d] do
        r := r.modify j (· + c * v[j]!)
  return r

/-- Complex conjugation `σ_{-1}`. -/
def conj (a : Elem) : Elem := F.galois (F.n - 1) a

/-- `|a|² = a * conj a`, an element of `ℤ[ζ_n]⁺`, computed from the autocorrelation
`A_k = ∑_i a_{i+k} a_i` as `A_0 + ∑_{k ≥ 1} A_k (ζ ^ k + ζ ^ (-k))`. -/
def normSq (a : Elem) : Elem := Id.run do
  let d := F.deg
  let mut a0 : Int := 0
  for i in [0:d] do
    a0 := a0 + a[i]! * a[i]!
  let mut r : Elem := F.ofInt a0
  for k in [1:d] do
    let mut ak : Int := 0
    for i in [0:d - k] do
      ak := ak + a[i + k]! * a[i]!
    if ak != 0 then
      let v := F.thetas[k]!
      for j in [0:d] do
        r := r.modify j (· + ak * v[j]!)
  return r

/-- The adjugate and norm of `a ≠ 0`: `adj = ∏_{σ ≠ 1} σ a` over the Galois automorphisms
`σ_k`, `k` coprime to `n`, `1 < k < n`, and `N = a · adj ∈ ℤ`, so that `a⁻¹ = adj / N`. Returns
`none` if `a · adj` is not an integer (impossible for `a ≠ 0`; a consistency check). -/
def normAdj (a : Elem) : Option (Elem × Int) := Id.run do
  let mut adj := F.one
  for k in [2:F.n] do
    if Nat.gcd k F.n == 1 then adj := F.mul adj (F.galois k a)
  let N := F.mul a adj
  if (N.extract 1 N.size).all (· == 0) then return some (adj, N[0]!) else return none

/-- Whether `a` is real, i.e. fixed by complex conjugation. -/
def isReal (a : Elem) : Bool := F.conj a == a

/-- The element `b_0 + ∑_{k ≥ 1} b_k (ζ ^ k + ζ ^ (-k))` of the real subfield. -/
def ofRealBasis (b : Array Int) : Elem := Id.run do
  let mut r := F.ofInt (b[0]?.getD 0)
  for k in [1:b.size] do
    let c := b[k]!
    if c != 0 then
      r := F.add r (F.smul c F.thetas[k % F.n]!)
  return r

/-- Coordinates of a real element in the basis `1, θ_1, …, θ_{m-1}` of `ℤ[ζ_n]⁺`, or `none` if the
element is not real. The answer is checked exactly. -/
def toRealBasis (x : Elem) : Option (Array Int) := Id.run do
  let m := F.realDim
  let xs : Array Rat := x.map Rat.ofInt
  let mut b : Array Int := #[]
  for i in [0:m] do
    let row := F.reducer[i]!
    let mut s : Rat := 0
    for j in [0:F.deg] do
      s := s + row[j]! * xs[j]!
    if s.den != 1 then return none
    b := b.push s.num
  if F.ofRealBasis b == x then return some b else return none

/-- Construct `ℤ[ζ_n]` for `n ≥ 3`, with tables at base precision `basePrec`. -/
def make (n : Nat) (basePrec : Nat := 192) : CycField := Id.run do
  let phi := cyclotomic n
  let d := phi.size - 1
  -- powers of ζ by repeated multiplication by ζ
  let mut pows : Array Elem := #[]
  let mut cur : Elem := (Array.replicate d (0 : Int)).set! 0 1
  for _ in [0:n] do
    pows := pows.push cur
    -- multiply by ζ
    let top := cur[d - 1]!
    let mut r : Elem := #[0]
    for i in [0:d - 1] do
      r := r.push cur[i]!
    if top != 0 then
      for j in [0:d] do
        r := r.modify j (· - top * phi[j]!)
    cur := r
  let thetas := (Array.range n).map fun k ↦
    Array.zipWith (· + ·) pows[k]! pows[(n - k) % n]!
  -- columns `1, θ_1, …, θ_{m-1}` of the real basis, as a `d × m` matrix
  let m := d / 2
  let cols : Array Elem := (Array.range m).map fun k ↦
    if k == 0 then (Array.replicate d (0 : Int)).set! 0 1 else thetas[k]!
  let A : Array (Array Rat) := (Array.range d).map fun i ↦
    (Array.range m).map fun k ↦ Rat.ofInt (cols[k]!)[i]!
  let reducer := (leftReducer A m).getD #[]
  let (cosB, sinB) := Ball.trigTable basePrec n
  let mut cosF : FloatArray := FloatArray.emptyWithCapacity n
  let mut sinF : FloatArray := FloatArray.emptyWithCapacity n
  let mut err : Float := 0.0
  for k in [0:n] do
    let (c, ec) := Ball.toFloatCert basePrec cosB[k]!
    let (s, es) := Ball.toFloatCert basePrec sinB[k]!
    cosF := cosF.push c
    sinF := sinF.push s
    err := max err (max ec es)
  return { n, deg := d, phi, pows, thetas, reducer, basePrec, cosB, sinB, cosF, sinF,
           trigErr := err }

/-- Ball enclosure, at precision `p`, of the value `∑ x_i cos (2πi/n)` of a real element, using the
cosine table `cos` (at precision `p`). -/
def realBallWith (_ : CycField) (cos : Array Ball) (x : Elem) : Ball := Id.run do
  let mut mid : Int := 0
  let mut rad : Nat := 0
  for i in [0:x.size] do
    let c := x[i]!
    if c != 0 then
      let b := cos[i]!
      mid := mid + c * b.mid
      rad := rad + c.natAbs * b.rad
  return ⟨mid, rad⟩

/-- Ball enclosure at precision `p` (at least `basePrec`) of a real element. -/
def realBall (x : Elem) (p : Nat) : Ball :=
  if p == F.basePrec then F.realBallWith F.cosB x
  else F.realBallWith (Ball.trigTable p F.n).1 x

/-- The precision at which `signReal` is guaranteed to decide the sign of a nonzero real element
of `ℤ[ζ_n]⁺` with power-basis coefficients `x`. -/
def signPrecBound (x : Elem) : Nat :=
  let B := x.foldl (fun s c ↦ s + c.natAbs) 0
  F.realDim * (B.log2 + 3) + 64

/-- The sign (`-1`, `0` or `1`) of a real element of `ℤ[ζ_n]⁺` in the identity embedding. `0` is
decided exactly; otherwise the precision is doubled until the enclosure excludes `0`. Returns
`none` only if the proven precision bound is exceeded. -/
def signReal (x : Elem) : Option Int := Id.run do
  if F.isZero x then return some 0
  let s := (F.realBallWith F.cosB x).sign
  if s != 0 then return some s
  let pmax := F.signPrecBound x
  let mut p := 2 * F.basePrec
  while true do
    let s := (F.realBallWith (Ball.trigTable p F.n).1 x).sign
    if s != 0 then return some s
    if p ≥ pmax then return none
    p := min pmax (2 * p)
  return none

/-- Compare two real elements exactly: `.lt`, `.eq` or `.gt`; `none` signals a fatal error. -/
def compareReal (x y : Elem) : Option Ordering :=
  (F.signReal (F.sub x y)).map fun s ↦ if s < 0 then .lt else if s == 0 then .eq else .gt

/-- Approximate complex value of `σ_k a` (for reporting only). -/
def evalConjF (k : Nat) (a : Elem) : Float × Float := Id.run do
  let mut x : Float := fl0
  let mut y : Float := fl0
  for i in [0:a.size] do
    let c := (Int64.ofInt a[i]!).toFloat
    let j := (i * k) % F.n
    x := x + c * F.cosF[j]!
    y := y + c * F.sinF[j]!
  return (x, y)

/-- The representatives `1 ≤ k < n/2` of `(ℤ/n)ˣ / {±1}`; `k = 1` is the identity embedding. -/
def embeddings : Array Nat :=
  ((Array.range F.n).filter fun k ↦ 2 * k < F.n && Nat.gcd k F.n == 1)

/-- Value of a real element as a ball at a precision large enough for about `digits` significant
decimal digits, then formatted. -/
def realToSci (x : Elem) (den : Nat := 1) (digits : Nat := 15) : String := Id.run do
  if F.isZero x then return "0"
  let mut p := F.basePrec
  for _ in [0:12] do
    let b := (F.realBall x p).divNat den
    -- need rad * 10^(digits+2) < |mid|
    if b.rad * 10 ^ (digits + 2) < b.mid.natAbs then
      return Ball.sciString p b digits
    p := 2 * p
  return "?"

end CycField

/-- Format a `Float` in decimal scientific notation with `digits` significant digits, exactly from
its binary value. -/
def fmtFloat (f : Float) (digits : Nat := 10) : String :=
  match Ball.floatExact f with
  | none => toString f
  | some (m, e) =>
    if m == 0 then "0" else
    if e ≥ 0 then Ball.sciString 0 ⟨m * ((2 ^ e.toNat : Nat) : Int), 0⟩ digits
    else Ball.sciString (-e).toNat ⟨m, 0⟩ digits

end TDCSGCompute
