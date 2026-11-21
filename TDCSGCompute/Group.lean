/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Perm
import TDCSGCompute.Thresholds

/-!
# The group `GG_n(r)` as a permutation group, merged thresholds, and orbit scans

## Generic points and faithfulness

A point `z = w / p` with `w ∈ ℤ[ζ_n] \ p ℤ[ζ_n]`, `p` a prime not dividing `n`, is fixed by no
non-trivial motion `z ↦ ζ^j z + t` with `t ∈ ℤ[ζ_n]`: for `j = 0` this needs `t = 0`, and for
`j ≠ 0` it needs `(1 - ζ^j) w ∈ p ℤ[ζ_n]`, impossible since `1 - ζ^j` is invertible modulo `p`
(its norm is a product of primes dividing `n`). The same holds for every point of its orbit, because
the motions of `GG_n(r)` preserve `w mod p` up to a power of `ζ`. Call such an orbit *generic* if,
moreover, none of its points lies on a boundary circle (decided exactly).

Let `G = GG_n(r)` be finite. Its elements are piecewise motions, discontinuous only on finitely many
circle arcs; the complement of the union of those arcs splits into open *atoms*, on each of which
every element is a single motion, and `G` permutes the atoms. If `x` is generic and `g x = x`, then
`g` is locally a motion fixing `x`, hence the identity near `x`, hence on the whole atom of `x`. So
if the sample set `X` meets every `G`-orbit of atoms, an element acting trivially on `G X` is the
identity off the arcs: the action on `G X` is a faithful representation of the group `G_gen` of
these maps up to null sets. `G = GG_n(r)` (bijections of the plane) maps onto `G_gen`, and the
order of the action on any `G X` is a lower bound for `|GG_n(r)|`.

Points of `X` in the same atom, or in atoms of the same `G`-orbit, have the same stabiliser, so
their orbits give equivalent constituents; `ConstituentSet` drops these.

## Samples

`gridSamples p r²` are the points `(α + β ζ) / p` in the union of the two disks; `cloudSamples`
are generic points `(p v + α + β ζ) / p` near given points `v`. `lensFamily` lists the points
`(1 - ζ) x`, `x` with power-basis coefficients in `[-B, B]`, in the lens at a given radius, one per
class under the symmetries `z ↦ -z` and `z ↦ z̄` of the system.
-/

namespace TDCSGCompute

/-! ### Orbits with their permutation action -/

/-- An orbit of `⟨a, b⟩` with the images of each point under `a` and `b`. -/
structure ActionOrbit where
  /-- The points `w` (the point is `w / M`). -/
  pts : Array Elem
  /-- `a` on the indices of `pts`. -/
  a : Perm
  /-- `b` on the indices of `pts`. -/
  b : Perm
  /-- No point of the orbit lies on a boundary circle. -/
  generic : Bool
  /-- The orbit was exhausted (if `false`, the cap was reached or a boundary point stopped it). -/
  complete : Bool
  /-- With tracking: the germ `(j, t)` of each point, `w_i / M = ζ^j (w_0 / M) + t`. -/
  germs : Array (Nat × Elem) := #[]
  deriving Inhabited

/-- Breadth-first orbit of `start / M` with the action of `a` and `b`. Stops at a boundary point
when `stopAtBoundary`, and at `cap` points. -/
def actionOrbit (T : DiskTest) (M : Nat) (start : Elem) (cap : Nat)
    (stopAtBoundary : Bool := true) (track : Bool := false) : IO ActionOrbit := do
  let F := T.F
  let n := F.n
  let m : Int := M
  let mut idx : Std.HashMap Elem Nat := ({} : Std.HashMap Elem Nat).insert start 0
  let mut pts : Array Elem := #[start]
  let mut germs : Array (Nat × Elem) := if track then #[(0, F.zero)] else #[]
  let mut aI : Array Nat := #[]
  let mut bI : Array Nat := #[]
  let mut generic := true
  let mut head := 0
  while head < pts.size do
    if pts.size > cap then
      return { pts, a := aI, b := bI, generic, complete := false, germs }
    let z := pts[head]!
    let fd := filterData F z
    let dl := T.decideWith fd z m
    let dr := T.decideWith fd z (-m)
    if dl == .failure || dr == .failure then
      throw <| IO.userError s!"membership could not be certified for {z}"
    if dl == .boundary || dr == .boundary then
      generic := false
      if stopAtBoundary then return { pts, a := aI, b := bI, generic, complete := false, germs }
    let mut ia := head
    if dl.inside then
      let w := F.rotCW z m
      match idx[w]? with
      | some j => ia := j
      | none =>
        ia := pts.size
        idx := idx.insert w pts.size
        pts := pts.push w
        if track then
          let (j, t) := germs[head]!
          germs := germs.push ((j + n - 1) % n, F.rotCW t 1)
    let mut ib := head
    if dr.inside then
      let w := F.rotCW z (-m)
      match idx[w]? with
      | some j => ib := j
      | none =>
        ib := pts.size
        idx := idx.insert w pts.size
        pts := pts.push w
        if track then
          let (j, t) := germs[head]!
          germs := germs.push ((j + n - 1) % n, F.rotCW t (-1))
    aI := aI.push ia
    bI := bI.push ib
    head := head + 1
  return { pts, a := aI, b := bI, generic, complete := true, germs }

/-! ### Samples -/

/-- Approximate position of `w / M` in the plane. -/
def approxPoint (F : CycField) (w : Elem) (M : Nat) : Float × Float :=
  let (x, y) := F.evalConjF 1 w
  (x / M.toFloat, y / M.toFloat)

/-- Whether the approximate point `(x, y)` is within `r` (plus a margin) of `-1` or of `1`. -/
def nearDisks (x y r2 : Float) : Bool :=
  (x + 1) * (x + 1) + y * y ≤ r2 + 1e-9 || (x - 1) * (x - 1) + y * y ≤ r2 + 1e-9

/-- The point `α + β ζ`. -/
def CycField.linear (F : CycField) (α β : Int) : Elem := F.reducePoly #[α, β]

/-- The grid points `(α + β ζ) / p` (`α, β` not both divisible by `p`) in the union of the disks of
squared radius about `r2` (a float; points slightly outside are harmless, they are fixed). -/
def gridSamples (F : CycField) (p : Nat) (r2 : Float) : Array (Nat × Elem) := Id.run do
  let θ := 2 * 3.141592653589793 / F.n.toFloat
  let (c, s) := (Float.cos θ, Float.sin θ)
  let r := Float.sqrt r2
  let P := p.toFloat
  let bmax := (r * P / s).ceil.toUInt64.toNat + 1
  let amax := ((1 + r) * P + bmax.toFloat * c.abs).ceil.toUInt64.toNat + 1
  let mut out : Array (Nat × Elem) := #[]
  for bi in [0:2 * bmax + 1] do
    let β : Int := (bi : Int) - bmax
    for ai in [0:2 * amax + 1] do
      let α : Int := (ai : Int) - amax
      if α % (p : Int) == 0 && β % (p : Int) == 0 then continue
      let x := (Float.ofInt α + Float.ofInt β * c) / P
      let y := Float.ofInt β * s / P
      if nearDisks x y r2 then out := out.push (p, F.linear α β)
  return out

/-- Generic points `(p v + α + β ζ) / p`, `|α|, |β| ≤ k`, `(α, β) ≠ 0`, near each `v`. -/
def cloudSamples (F : CycField) (p k : Nat) (vs : Array Elem) : Array (Nat × Elem) := Id.run do
  let mut out : Array (Nat × Elem) := #[]
  for v in vs do
    for ai in [0:2 * k + 1] do
      for bi in [0:2 * k + 1] do
        let α : Int := (ai : Int) - k
        let β : Int := (bi : Int) - k
        if α == 0 && β == 0 then continue
        out := out.push (p, F.add (F.smul p v) (F.linear α β))
  return out

/-- Generic points near the boundary circles: `(α + β ζ) / p` rounded from
`∓1 + (r - δ) e^{iθ}` for `K` angles `θ` and each depth `δ` in `deltas` (`r = √r2`). -/
def rimSamples (F : CycField) (r2 : Float) (K p : Nat) (deltas : Array Float) :
    Array (Nat × Elem) := Id.run do
  let θn := 2 * 3.141592653589793 / F.n.toFloat
  let (c, s) := (Float.cos θn, Float.sin θn)
  let r := Float.sqrt r2
  let P := p.toFloat
  let mut out : Array (Nat × Elem) := #[]
  for c0 in [(-1 : Float), 1] do
    for δ in deltas do
      for k in [0:K] do
        let φ := 2 * 3.141592653589793 * (k.toFloat + 0.5) / K.toFloat
        let x := c0 + (r - δ) * Float.cos φ
        let y := (r - δ) * Float.sin φ
        let β := (P * y / s).round
        let α := (P * x - β * c).round
        let αi : Int := if α < 0 then -((-α).toUInt64.toNat : Int) else (α.toUInt64.toNat : Int)
        let βi : Int := if β < 0 then -((-β).toUInt64.toNat : Int) else (β.toUInt64.toNat : Int)
        if αi % (p : Int) == 0 && βi % (p : Int) == 0 then continue
        out := out.push (p, F.linear αi βi)
  return out

/-- Generic points `u / D + (α + β ζ) / p` (`|α|, |β| ≤ k`, `(α, β) ≠ 0`) near the point `u / D`,
written `w / (p D)` with `w = p u + D (α + β ζ)`; generic when `p` is a prime dividing neither `n`
nor `D`. -/
def cloudAround (F : CycField) (p k : Nat) (u : Elem) (D : Nat) : Array (Nat × Elem) := Id.run do
  let mut out : Array (Nat × Elem) := #[]
  for ai in [0:2 * k + 1] do
    for bi in [0:2 * k + 1] do
      let α : Int := (ai : Int) - k
      let β : Int := (bi : Int) - k
      if α == 0 && β == 0 then continue
      out := out.push (p * D, F.add (F.smul p u) (F.smul D (F.linear α β)))
  return out

/-- Lexicographic order on coefficient vectors. -/
def elemLt (a b : Elem) : Bool := decide (a.toList < b.toList)

/-- The representative of `z` under `z ↦ -z` and `z ↦ z̄` (the lexicographically least). -/
def CycField.canonical (F : CycField) (z : Elem) : Elem :=
  let c := F.conj z
  #[F.neg z, c, F.neg c].foldl (fun m x ↦ if elemLt x m then x else m) z

/-- Whether `z` lies in both closed disks (the lens) at `T`. -/
def inLens (T : DiskTest) (z : Elem) : IO Bool := do
  let dl := T.decide z 1
  let dr := T.decide z (-1)
  if dl == .failure || dr == .failure then throw <| IO.userError s!"membership failed for {z}"
  return dl.inside && dr.inside

/-- The points `(1 - ζ) x`, `x` with power-basis coefficients in `[-B, B]`, in the lens at `r2`,
one per symmetry class, sorted by distance from the origin. -/
def lensFamily (F : CycField) (B : Nat) (r2 : RadiusSq) : IO (Array Elem) := do
  let T := DiskTest.make F r2
  let r2f := (Ball.toFloatCert F.basePrec ((F.realBall r2.num F.basePrec).divNat r2.den)).1
  let d := F.deg
  let base := 2 * B + 1
  let oneMinus := F.sub F.one (F.zetaPow 1)
  let mut seen : Std.HashSet Elem := {}
  let mut out : Array (Elem × Float) := #[]
  for code in [0:base ^ d] do
    let mut c := code
    let mut x : Elem := Array.emptyWithCapacity d
    for _ in [0:d] do
      x := x.push ((c % base : Nat) - (B : Int))
      c := c / base
    let z := F.mul oneMinus x
    let (px, py) := approxPoint F z 1
    if (px + 1) * (px + 1) + py * py > r2f + 1e-9 || (px - 1) * (px - 1) + py * py > r2f + 1e-9 then
      continue
    if !(← inLens T z) then continue
    let k := F.canonical z
    if seen.contains k then continue
    seen := seen.insert k
    out := out.push (k, px * px + py * py)
  return (out.qsort (fun a b ↦ a.2 < b.2)).map (·.1)

/-! ### The group on a sample set -/

/-- Limits of `groupOn`. -/
structure GroupOptions where
  /-- Largest orbit computed. -/
  orbitCap : Nat := 200000
  /-- Largest total number of orbit points. -/
  totalCap : Nat := 5000000
  /-- Random elements tried for witnesses. -/
  tries : Nat := 400
  /-- Schreier–Sims work limit for the quotient. -/
  ssLimit : Nat := 20000000

/-- Result of `groupOn`. -/
structure GroupReport where
  /-- Number of samples. -/
  samples : Nat := 0
  /-- Samples outside both disks (fixed by the group). -/
  fixed : Nat := 0
  /-- Samples already in an earlier orbit. -/
  seen : Nat := 0
  /-- Samples whose orbit meets a boundary circle (discarded). -/
  nongeneric : Nat := 0
  /-- Samples whose orbit reached the cap (the order is then undetermined). -/
  capped : Nat := 0
  /-- Generic orbits computed. -/
  orbits : Nat := 0
  /-- Points in those orbits. -/
  points : Nat := 0
  /-- Size of the largest generic orbit. -/
  maxOrbit : Nat := 0
  /-- The structural order computation on the inequivalent constituents. -/
  result : StructuralResult := default
  /-- Orders of `a`, `b`, `ab`, `[a, b] = a b a⁻¹ b⁻¹` on the constituents. -/
  wordOrders : Array Nat := #[]
  /-- The orbit sizes of the inequivalent constituents (sorted). -/
  sizes : Array Nat := #[]
  /-- For each inequivalent constituent: its degree and the sample `(M, w)` that produced it. -/
  reps : Array (Nat × Nat × Elem) := #[]
  /-- The samples whose orbit reached the orbit cap. -/
  cappedSamples : Array (Nat × Elem) := #[]

/-- The orders of `a`, `b`, `ab` and `a b a⁻¹ b⁻¹` on a constituent with generators `a, b`. -/
def wordOrdersOf (C : Constituent) : Array Nat :=
  let a := C.gens[0]!
  let b := C.gens[1]!
  #[a.order, b.order, (Perm.mul a b).order,
    (Perm.mul a (Perm.mul b (Perm.mul a.inv b.inv))).order]

/-- The incremental state of a group computation at one radius. -/
structure GroupState where
  /-- The ring. -/
  F : CycField
  /-- The squared radius. -/
  r2 : RadiusSq
  /-- Limits. -/
  opts : GroupOptions
  /-- Disk tests by scale. -/
  tests : Std.HashMap Nat DiskTest := {}
  /-- Points of the orbits computed so far, with their scale. -/
  seen : Std.HashSet (Nat × Elem) := {}
  /-- The inequivalent constituents. -/
  cs : ConstituentSet := {}
  /-- The report so far. -/
  rep : GroupReport := {}
  /-- Running orders of `a`, `b`, `ab`, `[a, b]`. -/
  orders : Array Nat := #[1, 1, 1, 1]
  /-- Whether to collect the centres of the germs. -/
  track : Bool := false
  /-- Centres `ζ^{-j}(±1 - t)` of the germs of the generic orbits. -/
  centres : Std.HashSet Elem := {}

/-- A fresh state. -/
def GroupState.init (F : CycField) (r2 : RadiusSq) (opts : GroupOptions) (track : Bool := false) :
    GroupState := { F, r2, opts, track }

/-- Process more samples. -/
def GroupState.add (st : GroupState) (samples : Array (Nat × Elem)) : IO GroupState := do
  let F := st.F
  let mut st := st
  st := { st with rep := { st.rep with samples := st.rep.samples + samples.size } }
  for (M, w) in samples do
    if st.seen.contains (M, w) then
      st := { st with rep := { st.rep with seen := st.rep.seen + 1 } }
      continue
    if st.rep.points ≥ st.opts.totalCap then
      st := { st with rep := { st.rep with capped := st.rep.capped + 1 } }
      continue
    let T ← match st.tests[M]? with
      | some T => pure T
      | none =>
        let T := DiskTest.makeScaled F st.r2 M
        st := { st with tests := st.tests.insert M T }
        pure T
    let o ← actionOrbit T M w st.opts.orbitCap (track := st.track)
    if o.pts.size == 1 && o.complete then
      st := { st with rep := { st.rep with fixed := st.rep.fixed + 1 } }
      continue
    let mut seen := st.seen
    for z in o.pts do
      seen := seen.insert (M, z)
    st := { st with seen }
    if !o.generic then
      st := { st with rep := { st.rep with nongeneric := st.rep.nongeneric + 1 } }
      continue
    if !o.complete then
      let repc := { st.rep with capped := st.rep.capped + 1,
                                cappedSamples := st.rep.cappedSamples.push (M, w) }
      st := { st with rep := repc }
      continue
    let rep1 := st.rep
    let rep1 := { rep1 with orbits := rep1.orbits + 1, points := rep1.points + o.pts.size,
                            maxOrbit := max rep1.maxOrbit o.pts.size }
    st := { st with rep := rep1 }
    if st.track then
      let mut cen := st.centres
      for (j, t) in o.germs do
        for c in [(1 : Int), -1] do
          cen := cen.insert (F.mul (F.zetaPow (-(j : Int))) (F.addInt (F.neg t) c))
      st := { st with centres := cen }
    let C := Constituent.make #[o.a, o.b]
    let (S', isNew) := st.cs.insert C
    st := { st with cs := S' }
    if isNew then
      let rep2 := { st.rep with reps := st.rep.reps.push (C.deg, M, w) }
      st := { st with orders := Array.zipWith Nat.lcm st.orders (wordOrdersOf C), rep := rep2 }
  return st

/-- The report: the structural order on the constituents found. -/
def GroupState.finish (st : GroupState) : GroupReport :=
  let res := structuralOrder st.cs.items st.opts.tries st.opts.ssLimit
  let res := { res with duplicates := res.duplicates + st.cs.duplicates }
  { st.rep with result := res, wordOrders := st.orders,
                sizes := (st.cs.items.map (·.deg)).qsort (· < ·) }

/-- The permutation group generated by `a` and `b` on the orbits of the samples, at the squared
radius `r2`. -/
def groupOn (F : CycField) (r2 : RadiusSq) (samples : Array (Nat × Elem)) (opts : GroupOptions) :
    IO GroupReport := do
  return (← (GroupState.init F r2 opts).add samples).finish

/-! ### Rim-vertex sampling

Every `G`-orbit of atoms contains an atom adjacent to `∂D_L` or `∂D_R` along an arc. (Take a
non-vertex point `q` on the boundary of an atom `A`, on an arc of discontinuity of `g = s_k ⋯ s_1`;
for the first `i` at which `h_i = s_i ⋯ s_1` is discontinuous at `q`, `h_{i-1}` is a single motion
`m` near `q`, so `h_{i-1} A` is an atom and `m` maps the arc near `q` into the circle `∂D` of
`s_i`.) Along `∂D_L`, the atoms adjacent on each side are separated by the points where other arcs
cross `∂D_L`; these lie on circles of radius `r` about the centres of the germs. So it suffices to
sample, on both sides of each boundary circle, one point at small depth `δ` at the angular midpoint
of every pair of consecutive crossing points. The centres are learnt from the orbits of the
samples; `groupFixpoint` repeats until no new crossing point appears, which certifies that every
gap between consecutive known crossing points is one atom on each side (the sampled atom's own
bounding circles would otherwise cross inside the gap), up to the depth `δ` being smaller than the
atoms' thickness at the sampled points. -/

/-- Angles (in `[0, 2π)`) at which circles of radius `r` about the centres `cs` cross the circle
of radius `r` about `c0`. -/
def crossingAngles (F : CycField) (r : Float) (c0 : Float) (cs : Array Elem) : Array Float :=
  Id.run do
  let mut out : Array Float := #[]
  let twoPi := 2 * 3.141592653589793
  for c in cs do
    let (x, y) := approxPoint F c 1
    let dx := x - c0
    let d := Float.sqrt (dx * dx + y * y)
    if d < 1e-12 || d ≥ 2 * r then continue
    let base := Float.atan2 y dx
    let h := Float.acos (d / (2 * r))
    for φ in [base + h, base - h] do
      let φ' := φ - twoPi * (φ / twoPi).floor
      out := out.push φ'
  return out

/-- Midpoints of consecutive distinct angles (cyclically), with a resolution `tol`. -/
def angleMidpoints (angles : Array Float) (tol : Float := 1e-12) : Array Float := Id.run do
  let twoPi := 2 * 3.141592653589793
  let a := angles.qsort (· < ·)
  let mut u : Array Float := #[]
  for x in a do
    if u.isEmpty || x - u.back! > tol then u := u.push x
  if u.isEmpty then return #[0, 3.141592653589793]
  let mut out : Array Float := #[]
  for i in [0:u.size] do
    let x := u[i]!
    let y := if i + 1 < u.size then u[i + 1]! else u[0]! + twoPi
    out := out.push ((x + y) / 2)
  return out

/-- A generic sample `(α + β ζ) / p` rounded from the plane point `(x, y)`. -/
def roundedSample (F : CycField) (p : Nat) (x y : Float) : Option (Nat × Elem) :=
  let θn := 2 * 3.141592653589793 / F.n.toFloat
  let (c, s) := (Float.cos θn, Float.sin θn)
  let P := p.toFloat
  let β := (P * y / s).round
  let α := (P * x - β * c).round
  let toI (v : Float) : Int :=
    if v < 0 then -((-v).toUInt64.toNat : Int) else (v.toUInt64.toNat : Int)
  let (αi, βi) := (toI α, toI β)
  if αi % (p : Int) == 0 && βi % (p : Int) == 0 then none else some (p, F.linear αi βi)

/-- Samples at depth `δ` on both sides of both boundary circles, at the midpoints between the
crossing points of the circles about `cs`. -/
def rimVertexSamples (F : CycField) (r : Float) (cs : Array Elem) (δ : Float) (p : Nat) :
    Array (Nat × Elem) × Nat := Id.run do
  let mut out : Array (Nat × Elem) := #[]
  let mut nv := 0
  for c0 in [(-1 : Float), 1] do
    let mids := angleMidpoints (crossingAngles F r c0 cs)
    nv := nv + mids.size
    for φ in mids do
      for ρ in [r - δ, r + δ] do
        if let some smp := roundedSample F p (c0 + ρ * Float.cos φ) (ρ * Float.sin φ) then
          out := out.push smp
  return (out, nv)

/-- Rim-vertex sampling to a fixpoint (at most `maxIter` rounds), starting from `initial`
samples. Returns the report and, per round, the number of crossing-point gaps. -/
def groupFixpoint (F : CycField) (r2 : RadiusSq) (initial : Array (Nat × Elem))
    (opts : GroupOptions) (δ : Float) (p : Nat) (maxIter : Nat := 12) :
    IO (GroupReport × Array Nat × Bool × Array Elem) := do
  let r2b := (F.realBall r2.num F.basePrec).divNat r2.den
  let r := Float.sqrt (Ball.toFloatCert F.basePrec r2b).1
  let mut st ← (GroupState.init F r2 opts (track := true)).add initial
  let mut rounds : Array Nat := #[]
  let mut prev := 0
  let mut converged := false
  let mut done : Std.HashSet (Nat × Elem) := {}
  for _ in [0:maxIter] do
    let cs := (st.centres.toArray.push (F.ofInt 1)).push (F.ofInt (-1))
    let (smp, nv) := rimVertexSamples F r cs δ p
    rounds := rounds.push nv
    if nv == prev then
      converged := true
      break
    prev := nv
    let fresh := smp.filter fun x ↦ !done.contains x
    for x in fresh do
      done := done.insert x
    st ← st.add fresh
    if st.rep.capped > 0 then break
  return (st.finish, rounds, converged, st.centres.toArray)

/-! ### Germs and candidate events of the arrangement

Every element of `GG_n(r)` is, on each atom, a motion `m(z) = ζ^j z + t` with `t ∈ ℤ[ζ_n]` (a
*germ*). Its discontinuities lie on circles `m'⁻¹(∂D_L)`, `m'⁻¹(∂D_R)` for germs `m'` of prefixes,
of radius `r` about the *centres* `m'⁻¹(∓1) = ζ^{-j}(∓1 - t)`. The arrangement of these arcs
changes combinatorially only where three of the circles pass through one point or two become
tangent. Since the set of arcs is invariant under the group up to the discontinuities of the
group elements themselves, one of the circles may be taken to be `∂D_L` or `∂D_R`. So every event
radius is, for some centres `c, c'`,
* the circumradius `R(c₀, c, c')` of `c₀ ∈ {-1, 1}`, `c`, `c'` (vertex: the circumcentre), or
* `|c₀ - c| / 2` (vertex: the midpoint),

an element of `ℚ(ζ_n)⁺` together with a vertex in `ℚ(ζ_n)`. `germsOf` collects the germs seen on
generic sample orbits; `eventCandidates` lists the candidates in a window. The group can change only
at events, so every change of the group lies among these candidates once the germs present just
below the change have been collected. -/

/-- The germs `(j, t)` (`g x = ζ^j x + t`) of the orbit of a generic point `x = w / M`, tracked
along the breadth-first search: `a` sends `(j, t)` to `(j - 1, ζ⁻¹ (t + 1) - 1)` and `b` to
`(j - 1, ζ⁻¹ (t - 1) + 1)`. -/
def germOrbit (T : DiskTest) (M : Nat) (start : Elem) (cap : Nat) : IO (Array (Nat × Elem)) := do
  let F := T.F
  let n := F.n
  let m : Int := M
  let mut idx : Std.HashSet Elem := ({} : Std.HashSet Elem).insert start
  let mut pts : Array (Elem × Nat × Elem) := #[(start, 0, F.zero)]
  let mut head := 0
  while head < pts.size && pts.size ≤ cap do
    let (z, j, t) := pts[head]!
    head := head + 1
    let fd := filterData F z
    for side in [m, -m] do
      let dcs := T.decideWith fd z side
      if dcs == .failure then throw <| IO.userError s!"membership could not be certified for {z}"
      if dcs.inside then
        let w := F.rotCW z side
        if !idx.contains w then
          idx := idx.insert w
          let c : Int := if side > 0 then 1 else -1
          pts := pts.push (w, (j + n - 1) % n, F.rotCW t c)
  return pts.map fun (_, j, t) ↦ (j, t)

/-- The circumcentre of `a, b, c` and its squared circumradius, as `(u, D, R²)` with centre
`u / D`; `none` if the points are collinear. -/
def circumcircle (F : CycField) (a b c : Elem) : Option (Elem × Nat × RealQ) := do
  let u := F.sub b a
  let v := F.sub c a
  let den := F.sub (F.mul (F.conj u) v) (F.mul u (F.conj v))
  if F.isZero den then none
  let num := F.sub (F.mul (F.normSq u) v) (F.mul (F.normSq v) u)
  let (adj, N) ← F.normAdj den
  let z := F.mul num adj
  let z := if N < 0 then F.neg z else z
  let D := N.natAbs
  let ctr := F.add (F.smul D a) z
  let g := ctr.foldl (fun g x ↦ Nat.gcd g x.natAbs) D
  let ctr := ctr.map (· / (g : Int))
  let D := D / g
  let zz := z.map id
  let g2 := zz.foldl (fun g x ↦ Nat.gcd g x.natAbs) N.natAbs
  let zr := zz.map (· / (g2 : Int))
  let Dz := N.natAbs / g2
  return (ctr, D, RealQ.normalize { num := F.normSq zr, den := Dz * Dz })

/-- A candidate event: the squared radius and a vertex `u / D`. -/
structure EventCandidate where
  /-- The squared radius. -/
  r2 : RealQ
  /-- The vertex numerator. -/
  u : Elem
  /-- The vertex denominator. -/
  D : Nat
  /-- `true` for a tangency, `false` for a triple point. -/
  tangency : Bool
  deriving Inhabited

/-- The candidate events in the open window `(lo, hi)` from the centres of the germs: tangencies
`|c₀ - c|² / 4` and circumradii `R²(c₀, c, c')`, `c₀ = ±1`, with all pairwise distances below
`2 r_hi` (other triples cannot meet in a common point at radius `≤ r_hi`). Distinct values only,
with one vertex each, sorted. -/
def eventCandidatesOfCentres (F : CycField) (cs : Array Elem) (lo hi : RealQ) :
    IO (Array EventCandidate) := do
  let hiF := (Ball.toFloatCert F.basePrec ((F.realBall hi.num F.basePrec).divNat hi.den)).1
  let lim := 4 * hiF + 1e-9
  let pos := cs.map fun c ↦ approxPoint F c 1
  let d2 (p q : Float × Float) : Float := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2
  let inWin (x : RealQ) : Bool :=
    RealQ.compare F lo x == some .lt && RealQ.compare F x hi == some .lt
  let mut found : Std.HashMap Elem (EventCandidate) := {}
  for c0 in [(1 : Int), -1] do
    let p0 : Float × Float := (Float.ofInt c0, 0)
    let e0 := F.ofInt c0
    let near := (Array.range cs.size).filter fun i ↦ d2 pos[i]! p0 < lim && cs[i]! != e0
    for i in near do
      let c := cs[i]!
      -- tangency
      let t2 := RealQ.normalize { num := F.normSq (F.sub c e0), den := 4 }
      if inWin t2 then
        let key := t2.num.push (t2.den : Int)
        if !found.contains key then
          found := found.insert key { r2 := t2, u := F.add c e0, D := 2, tangency := true }
      for k in near do
        if k ≤ i then continue
        if d2 pos[i]! pos[k]! ≥ lim then continue
        match circumcircle F e0 c cs[k]! with
        | none => pure ()
        | some (u, D, R2) =>
          if inWin R2 then
            let key := R2.num.push (R2.den : Int)
            if !found.contains key then
              found := found.insert key { r2 := R2, u, D, tangency := false }
  let arr := found.toArray.map (·.2)
  return arr.qsort fun x y ↦ RealQ.compare F x.r2 y.r2 == some .lt

/-- The candidate events in `(lo, hi)` from the centres `ζ^{-j}(∓1 - t)` of the germs. -/
def eventCandidates (F : CycField) (germs : Array (Nat × Elem)) (lo hi : RealQ) :
    IO (Array EventCandidate) := do
  let mut cset : Std.HashSet Elem := {}
  for (j, t) in germs do
    for c in [(1 : Int), -1] do
      cset := cset.insert (F.mul (F.zetaPow (-(j : Int))) (F.addInt (F.neg t) c))
  eventCandidatesOfCentres F cset.toArray lo hi

/-- The germs seen on the generic orbits of the samples at `r2`. -/
def germsOf (F : CycField) (r2 : RadiusSq) (samples : Array (Nat × Elem)) (cap : Nat) :
    IO (Array (Nat × Elem)) := do
  let mut tests : Std.HashMap Nat DiskTest := {}
  let mut seen : Std.HashSet (Nat × Elem) := {}
  for (M, w) in samples do
    let T ← match tests[M]? with
      | some T => pure T
      | none =>
        let T := DiskTest.makeScaled F r2 M
        tests := tests.insert M T
        pure T
    let gs ← germOrbit T M w cap
    for g in gs do
      seen := seen.insert g
  return seen.toArray

/-- A comparable description of a group computation: certification, order, and the sorted
degrees of the alternating and of the other constituents with their orders. -/
def GroupReport.signature (rep : GroupReport) : String :=
  let R := rep.result
  let big := (R.bigDegrees.qsort (· < ·)).toList
  let oth := (R.others.map fun (d, _, o) ↦ (d, o.getD 0)).qsort (fun x y ↦ x.1 < y.1 ||
    (x.1 == y.1 && x.2 < y.2))
  s!"{R.certified}|{rep.capped}|{R.quotientOrder}|{big}|{oth.toList}"

/-! ### Merged thresholds of a family of points -/

/-- The thresholds of several orbits, merged. -/
structure MergedThresholds where
  /-- Distinct threshold values `r²` in increasing order, each with the number of starting points
  whose orbit has that threshold. -/
  values : Array (Elem × Nat)
  /-- `none` if every sweep reached `upto`; otherwise the least last threshold of a sweep that
  stopped at its cap (the merged list is complete up to and including this value). -/
  completeUpTo : Option Elem
  /-- Number of sweeps that stopped at the cap. -/
  cappedStarts : Nat

/-- Sweep each start (integral points) up to `upto` with the given cap, and merge the threshold
values in `[lo, upto)` exactly. -/
def mergedThresholds (F : CycField) (starts : Array Elem) (lo upto : RadiusSq) (cap : Nat) :
    IO MergedThresholds := do
  let mut counts : Std.HashMap Elem Nat := {}
  let mut complete : Option Elem := none
  let mut capped := 0
  for z in starts do
    let res ← sweep F z { cap, upto := some upto }
    for th in res.thresholds do
      match RealQ.compare F (RealQ.ofElem th.value) lo with
      | some .lt => pure ()
      | _ => counts := counts.insert th.value (counts.getD th.value 0 + 1)
    if res.stopReason == "cap reached" then
      capped := capped + 1
      if let some last := res.thresholds.back? then
        complete := match complete with
          | none => some last.value
          | some c => if F.compareReal last.value c == some .lt then some last.value else some c
      else complete := some (F.ofInt 0)
  let vals := counts.toArray.qsort fun x y ↦ F.compareReal x.1 y.1 == some .lt
  return { values := vals, completeUpTo := complete, cappedStarts := capped }

/-- A short rational strictly between the real elements `x < y`, if one with at most 40 decimal
digits is found. -/
def rationalBetween (F : CycField) (x y : RealQ) : Option Rat := Id.run do
  let p := 4 * F.basePrec
  let toRat (v : RealQ) : Rat :=
    ((F.realBall v.num p).mid : Rat) / ((2 ^ p : Nat) : Rat) / (v.den : Rat)
  let mid := (toRat x + toRat y) / 2
  for j in [0:41] do
    let s : Nat := 10 ^ j
    let q : Rat := ((mid * s).floor : Rat) / s
    let q' : Rat := ((mid * s).ceil : Rat) / s
    for c in [q, q'] do
      if RealQ.compare F x (RealQ.ofRat F c) == some .lt &&
          RealQ.compare F (RealQ.ofRat F c) y == some .lt then return some c
  return none

/-! ### Scans of many starting points -/

/-- Signed sums of `k` distinct powers of `ζ` (`1 ≤ k ≤ K`), as `(exponent, sign)` lists, with the
first exponent's sign `+` (the sign flip `z ↦ -z` is a symmetry). -/
partial def signedSums (n K : Nat) : Array (List (Nat × Int)) := Id.run do
  let mut out : Array (List (Nat × Int)) := #[]
  let mut stack : Array (List (Nat × Int)) := (Array.range n).map fun e ↦ [(e, 1)]
  while !stack.isEmpty do
    let t := stack.back!
    stack := stack.pop
    out := out.push t
    if t.length < K then
      let last := t.head!.1
      for e in [last + 1:n] do
        stack := stack.push ((e, 1) :: t)
        stack := stack.push ((e, -1) :: t)
  return out

end TDCSGCompute
