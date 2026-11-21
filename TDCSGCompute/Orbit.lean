/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Disk
import TDCSGCompute.Store

/-!
# Breadth-first orbit search

The generators act on `z ∈ ℤ[ζ_n]` by
`a z = ζ⁻¹ (z + 1) - 1`, `a⁻¹ z = ζ (z + 1) - 1` when `|z + 1| ≤ r`, and
`b z = ζ⁻¹ (z - 1) + 1`, `b⁻¹ z = ζ (z - 1) + 1` when `|z - 1| ≤ r`; each fixes every point outside
its disk. Since each generator maps its disk to itself, `a⁻¹` and `b⁻¹` are given by the same disk
tests. The orbit of a starting point is explored breadth first, with the frontier stored implicitly
as a range of insertion indices of the `PointSet`.

The search stops either when no new point appears (the orbit is finite and its exact size is
reported) or when the number of points reaches the cap (reported as "cap reached"; nothing is
claimed about finiteness).

`orbitParallel` expands each generation in parallel `Task`s: the main thread decodes the frontier,
each task computes the disk decisions and the images for a slice of it, and the main thread then
inserts the images in slice order. The result is identical to the serial
search.
-/

namespace TDCSGCompute

/-- `ζ⁻¹ (z + c) - c`, the rotation by `-2π/n` about `-c`, in one pass. -/
@[inline] def CycField.rotCW (F : CycField) (z : Elem) (c : Int) : Elem := Id.run do
  let d := F.deg
  let c0 := z[0]! + c
  let mut r : Elem := Array.emptyWithCapacity d
  for i in [1:d] do
    r := r.push z[i]!
  r := r.push 0
  if c0 != 0 then
    let zi := F.pows[F.n - 1]!
    for j in [0:d] do
      r := r.modify j (· + c0 * zi[j]!)
  return r.modify 0 (· - c)

/-- `ζ (z + c) - c`, the rotation by `2π/n` about `-c`, in one pass. -/
@[inline] def CycField.rotCCW (F : CycField) (z : Elem) (c : Int) : Elem := Id.run do
  let d := F.deg
  let top := z[d - 1]!
  let mut r : Elem := Array.emptyWithCapacity d
  r := r.push 0
  r := r.push (z[0]! + c)
  for i in [1:d - 1] do
    r := r.push z[i]!
  if top != 0 then
    for j in [0:d] do
      r := r.modify j (· - top * F.phi[j]!)
  return r.modify 0 (· - c)

/-- `a z = ζ⁻¹ (z + 1) - 1`. -/
@[inline] def CycField.genA (F : CycField) (z : Elem) : Elem := F.rotCW z 1

/-- `a⁻¹ z = ζ (z + 1) - 1`. -/
@[inline] def CycField.genAInv (F : CycField) (z : Elem) : Elem := F.rotCCW z 1

/-- `b z = ζ⁻¹ (z - 1) + 1`. -/
@[inline] def CycField.genB (F : CycField) (z : Elem) : Elem := F.rotCW z (-1)

/-- `b⁻¹ z = ζ (z - 1) + 1`. -/
@[inline] def CycField.genBInv (F : CycField) (z : Elem) : Elem := F.rotCCW z (-1)

/-- Counters of how membership decisions were reached. -/
structure DecisionStats where
  /-- Decisions made by the floating-point filter. -/
  filter : Nat := 0
  /-- Decisions that needed the exact path, the point being off the boundary. -/
  exact : Nat := 0
  /-- Points found exactly on a boundary circle. -/
  boundary : Nat := 0
  deriving Inhabited, Repr

/-- Add a decision to the counters. -/
def DecisionStats.record (st : DecisionStats) : Decision → DecisionStats
  | .filter _ => { st with filter := st.filter + 1 }
  | .exact _ => { st with exact := st.exact + 1 }
  | .boundary => { st with boundary := st.boundary + 1 }
  | .failure => st

/-- Sum of counters. -/
def DecisionStats.add (a b : DecisionStats) : DecisionStats :=
  { filter := a.filter + b.filter, exact := a.exact + b.exact, boundary := a.boundary + b.boundary }

/-- Options of an orbit search. -/
structure OrbitOptions where
  /-- Stop once the orbit has this many points. -/
  cap : Nat := 1000000
  /-- Track the maximal modulus of each Galois conjugate. -/
  conj : Bool := true
  /-- Number of worker tasks (`1` for the serial search). -/
  threads : Nat := 1
  /-- Initial bytes per stored coefficient. -/
  width : Nat := 2

/-- Result of an orbit search. -/
structure OrbitResult where
  /-- Number of points found. -/
  size : Nat
  /-- `true` if the orbit was exhausted (finite, of exactly `size` points), `false` if the cap was
  reached. -/
  complete : Bool
  /-- Number of points first reached in each breadth-first generation (generation `0` is the
  starting point). -/
  generations : Array Nat
  /-- For each embedding `σ_k` (`k` from `CycField.embeddings`), the maximal `|σ_k z|`. -/
  maxConj : Array (Nat × Float)
  /-- How the membership decisions were made. -/
  stats : DecisionStats
  /-- The orbit points. -/
  points : PointSet

/-- Update the running conjugate maxima with a point. -/
@[inline] def updateConj (F : CycField) (ks : Array Nat) (mx : Array Float) (z : Elem) :
    Array Float := Id.run do
  let mut m := mx
  for i in [0:ks.size] do
    let (x, y) := F.evalConjF ks[i]! z
    let v := Float.sqrt (x * x + y * y)
    if v > m[i]! then m := m.set! i v
  return m

/-- The images of `z` under the generators that move it, with the two disk decisions. -/
@[inline] def expandPoint (T : DiskTest) (z : Elem) : Decision × Decision × Array Elem :=
  let F := T.F
  let fd := filterData F z
  let dl := T.decideWith fd z 1
  let dr := T.decideWith fd z (-1)
  let imgs : Array Elem := Array.emptyWithCapacity 4
  let imgs := if dl.inside then (imgs.push (F.genA z)).push (F.genAInv z) else imgs
  let imgs := if dr.inside then (imgs.push (F.genB z)).push (F.genBInv z) else imgs
  (dl, dr, imgs)

/-- Serial breadth-first search of the orbit of `start` at the squared radius of `T`. -/
def orbitSerial (T : DiskTest) (start : Elem) (opts : OrbitOptions) : IO OrbitResult := do
  let F := T.F
  let ks := F.embeddings
  let mut mx : Array Float := Array.replicate ks.size 0
  let mut set := PointSet.empty F.deg opts.width
  match set.insert start with
  | .added s => set := s
  | _ => throw <| IO.userError "starting point does not fit in 64-bit coefficients"
  let mut head := 0
  let mut genEnd := 1
  let mut gens : Array Nat := #[1]
  let mut stats : DecisionStats := {}
  let mut capped : Bool := set.size ≥ opts.cap
  while head < set.size && !capped do
    let z := set.get head
    if opts.conj then mx := updateConj F ks mx z
    let (dl, dr, imgs) := expandPoint T z
    if dl == .failure || dr == .failure then
      throw <| IO.userError s!"membership could not be certified for {z}"
    stats := (stats.record dl).record dr
    for w in imgs do
      if !capped then
        match set.insert w with
        | .added s =>
          set := s
          if set.size ≥ opts.cap then capped := true
        | .present s => set := s
        | .overflow _ => throw <| IO.userError s!"coefficient overflow (beyond 64 bits) at {w}"
    head := head + 1
    if head == genEnd then
      if set.size > genEnd then gens := gens.push (set.size - genEnd)
      genEnd := set.size
  if capped && set.size > genEnd then
    gens := gens.push (set.size - genEnd)
  return { size := set.size, complete := !capped, generations := gens,
           maxConj := ks.zip mx, stats, points := set }

/-- Work done by one task on a slice of the frontier. -/
structure SliceResult where
  /-- Images of the slice's points, in order (duplicates are removed on insertion). -/
  candidates : Array Elem
  /-- Decision counters. -/
  stats : DecisionStats
  /-- Conjugate maxima over the slice. -/
  maxConj : Array Float
  /-- A point whose membership could not be certified, if any. -/
  failure : Option Elem

/-- Expand the frontier points `pts[lo:hi]`. -/
def expandSlice (T : DiskTest) (pts : Array Elem) (ks : Array Nat) (conj : Bool) (lo hi : Nat) :
    SliceResult := Id.run do
  let F := T.F
  let mut cands : Array Elem := #[]
  let mut stats : DecisionStats := {}
  let mut mx : Array Float := Array.replicate ks.size 0
  for i in [lo:hi] do
    let z := pts[i]!
    if conj then mx := updateConj F ks mx z
    let (dl, dr, imgs) := expandPoint T z
    if dl == .failure || dr == .failure then
      return { candidates := cands, stats, maxConj := mx, failure := some z }
    stats := (stats.record dl).record dr
    for w in imgs do
      cands := cands.push w
  return { candidates := cands, stats, maxConj := mx, failure := none }

/-- Breadth-first search with each generation expanded by `opts.threads` parallel tasks. Small
generations are expanded serially. -/
def orbitParallel (T : DiskTest) (start : Elem) (opts : OrbitOptions) : IO OrbitResult := do
  let F := T.F
  let ks := F.embeddings
  let mut mx : Array Float := Array.replicate ks.size 0
  let mut set := PointSet.empty F.deg opts.width
  match set.insert start with
  | .added s => set := s
  | _ => throw <| IO.userError "starting point does not fit in 64-bit coefficients"
  let mut lo := 0
  let mut gens : Array Nat := #[1]
  let mut stats : DecisionStats := {}
  let mut capped : Bool := set.size ≥ opts.cap
  while lo < set.size && !capped do
    let hi := set.size
    let len := hi - lo
    let nt := min opts.threads (max 1 (len / 512))
    let chunk := (len + nt - 1) / nt
    let results : Array SliceResult ← do
      if nt == 1 then
        pure #[expandSlice T ((Array.range len).map fun i ↦ set.get (lo + i)) ks opts.conj 0 len]
      else
        let pts := (Array.range len).map fun i ↦ set.get (lo + i)
        let tasks := (Array.range nt).map fun t ↦
          Task.spawn fun _ ↦
            expandSlice T pts ks opts.conj (t * chunk) (min len ((t + 1) * chunk))
        pure (tasks.map Task.get)
    for r in results do
      if let some z := r.failure then
        throw <| IO.userError s!"membership could not be certified for {z}"
      stats := stats.add r.stats
      if opts.conj then
        mx := (Array.zipWith max mx r.maxConj)
    for r in results do
      for w in r.candidates do
        if !capped then
          match set.insert w with
          | .added s =>
            set := s
            if set.size ≥ opts.cap then capped := true
          | .present s => set := s
          | .overflow _ => throw <| IO.userError s!"coefficient overflow (beyond 64 bits) at {w}"
    if set.size > hi then gens := gens.push (set.size - hi)
    lo := hi
  return { size := set.size, complete := !capped, generations := gens,
           maxConj := ks.zip mx, stats, points := set }

/-- Orbit search, serial or parallel according to `opts.threads`. -/
def orbit (T : DiskTest) (start : Elem) (opts : OrbitOptions) : IO OrbitResult :=
  if opts.threads ≤ 1 then orbitSerial T start opts else orbitParallel T start opts

end TDCSGCompute
