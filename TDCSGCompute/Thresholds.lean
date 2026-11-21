/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Orbit
import TDCSGCompute.Spec

/-!
# Exact thresholds of an orbit

Disks grow with `r`, and a point inside a disk at radius `r` is moved the same way at every larger
radius, so the orbit `O(r)` of a point only grows with `r`. It changes exactly at the values
`t = |z ± 1|²` (`z ∈ O(r)`) at which a point of the current orbit enters a disk; each such `t` is
an element of `ℤ[ζ_n]⁺`.

The sweep keeps the current orbit, the current level `L` (the last threshold), and a binary heap of
the pairs `(z, side)` with `z` outside that disk, keyed by `|z + side|²`. It repeatedly pops the
smallest key `t`, together with every entry whose key equals `t` exactly, sets `L = t`, lets those
points move, and continues the breadth-first search at `r² = t` (closed disks: a new point at
distance exactly `r` is inside). The heap order uses certified float enclosures and falls back to
exact comparison in `ℤ[ζ_n]⁺` (`CycField.compareReal`) whenever the enclosures overlap, so ties are
detected exactly.

The orbit size reported for a threshold `t_k` is `|O(r)|` for `t_k ≤ r² < t_{k+1}`.
-/

namespace TDCSGCompute

/-- A pending disk entry: point `idx` lies outside the disk on `side`. -/
structure HeapEntry where
  /-- Approximation of `|z + side|²`. -/
  q : Float
  /-- A bound on the error of `q`, inflated to absorb the rounding of the comparisons. -/
  e : Float
  /-- Index of the point in the orbit's `PointSet`. -/
  idx : Nat
  /-- `1` for the left disk, `-1` for the right disk. -/
  side : Int
  deriving Inhabited

/-- One threshold of the sweep. -/
structure Threshold where
  /-- The exact value `t = r²` at which the orbit grows. -/
  value : Elem
  /-- Number of (point, disk) pairs that enter at `t`. -/
  entering : Nat
  /-- Orbit size for `t ≤ r² < next threshold` (or the cap, if reached during this step). -/
  size : Nat
  deriving Inhabited

/-- State of a sweep. -/
structure SweepState where
  /-- The orbit so far. -/
  set : PointSet
  /-- The binary heap of pending entries. -/
  heap : Array HeapEntry
  /-- Decision counters. -/
  stats : DecisionStats := {}

/-- The exact key of an entry. -/
def entryValue (F : CycField) (set : PointSet) (h : HeapEntry) : Elem :=
  F.normSq (F.addInt (set.get h.idx) h.side)

/-- Compare two entries, exactly when their enclosures overlap. -/
def cmpEntry (F : CycField) (set : PointSet) (a b : HeapEntry) : IO Ordering := do
  if a.q + a.e < b.q - b.e then return .lt
  if a.q - a.e > b.q + b.e then return .gt
  match F.compareReal (entryValue F set a) (entryValue F set b) with
  | some o => return o
  | none => throw <| IO.userError "exact comparison of thresholds failed"

/-- Push onto the heap. -/
def heapPush (F : CycField) (set : PointSet) (heap : Array HeapEntry) (x : HeapEntry) :
    IO (Array HeapEntry) := do
  let mut h := heap.push x
  let mut i := h.size - 1
  while i > 0 do
    let p := (i - 1) / 2
    if (← cmpEntry F set h[i]! h[p]!) == .lt then
      h := h.swapIfInBounds i p
      i := p
    else break
  return h

/-- Pop the minimum of a nonempty heap. -/
def heapPop (F : CycField) (set : PointSet) (heap : Array HeapEntry) :
    IO (HeapEntry × Array HeapEntry) := do
  let top := heap[0]!
  let last := heap.back!
  let mut h := heap.pop
  if h.isEmpty then return (top, h)
  h := h.set! 0 last
  let mut i := 0
  while true do
    let l := 2 * i + 1
    let r := l + 1
    let mut m := i
    if l < h.size then
      if (← cmpEntry F set h[l]! h[m]!) == .lt then m := l
    if r < h.size then
      if (← cmpEntry F set h[r]! h[m]!) == .lt then m := r
    if m == i then break
    h := h.swapIfInBounds i m
    i := m
  return (top, h)

/-- The heap entry for point `idx` and `side`. -/
def mkEntry (F : CycField) (z : Elem) (idx : Nat) (side : Int) : HeapEntry :=
  let fd := filterData F z
  if fd.big then { q := 0, e := (1.0 : Float) / 0.0, idx, side } else
  let (q, e) := filterNormSq F (filterGamma F) fd (if side > 0 then 1.0 else -1.0)
  { q, e := 2 * e + 8 * unitRoundoff * q.abs + (1.0 : Float).scaleB (-1000), idx, side }

/-- Continue the breadth-first search from the points with indices in `queue` at the squared
radius of `T`: points inside a disk are moved, the others are queued in the heap. Stops adding
points at the cap. -/
def sweepExpand (T : DiskTest) (st : SweepState) (queue : Array Nat) (cap : Nat) :
    IO SweepState := do
  let F := T.F
  let mut st := st
  let mut q := queue
  let mut head := 0
  while head < q.size do
    let idx := q[head]!
    head := head + 1
    let z := st.set.get idx
    let fd := filterData F z
    for side in [(1 : Int), -1] do
      let dcs := T.decideWith fd z side
      if dcs == .failure then throw <| IO.userError s!"membership could not be certified for {z}"
      st := { st with stats := st.stats.record dcs }
      if dcs.inside then
        let imgs := if side > 0 then #[F.genA z, F.genAInv z] else #[F.genB z, F.genBInv z]
        for w in imgs do
          if st.set.size < cap then
            match st.set.insert w with
            | .added s =>
              q := q.push st.set.size
              st := { st with set := s }
            | .present s => st := { st with set := s }
            | .overflow _ => throw <| IO.userError s!"coefficient overflow at {w}"
      else
        let e := mkEntry F z idx side
        st := { st with heap := ← heapPush F st.set st.heap e }
  return st

/-- Options of a threshold sweep. -/
structure SweepOptions where
  /-- Stop once the orbit reaches this size. -/
  cap : Nat := 1000000
  /-- Stop before a threshold `≥ upto`. -/
  upto : Option RadiusSq := none
  /-- Start from the orbit at this squared radius instead of from `{start}`. -/
  start2 : Option RadiusSq := none
  /-- Stop after this many thresholds. -/
  maxSteps : Nat := 1000000000

/-- Result of a sweep. -/
structure SweepResult where
  /-- Orbit size before the first threshold. -/
  initialSize : Nat
  /-- The thresholds in increasing order. -/
  thresholds : Array Threshold
  /-- Why the sweep stopped. -/
  stopReason : String
  /-- Decision counters. -/
  stats : DecisionStats

/-- Sweep the thresholds of the orbit of `start`, calling `report` on each. -/
def sweep (F : CycField) (start : Elem) (opts : SweepOptions) (width : Nat := 2)
    (report : Threshold → IO Unit := fun _ ↦ pure ()) : IO SweepResult := do
  let mut set := PointSet.empty F.deg width
  match set.insert start with
  | .added s => set := s
  | _ => throw <| IO.userError "starting point does not fit in 64-bit coefficients"
  let r0 : RadiusSq := opts.start2.getD { num := F.ofInt (-1), den := 1 }
  let mut st : SweepState := { set, heap := #[] }
  st ← sweepExpand (DiskTest.make F r0) st #[0] opts.cap
  let initialSize := st.set.size
  let mut ths : Array Threshold := #[]
  let mut reason := "heap empty"
  while true do
    if st.set.size ≥ opts.cap then reason := "cap reached"; break
    if ths.size ≥ opts.maxSteps then reason := "step limit"; break
    if st.heap.isEmpty then reason := "heap empty"; break
    let (top, h) ← heapPop F st.set st.heap
    st := { st with heap := h }
    let t := entryValue F st.set top
    if let some u := opts.upto then
      match RealQ.compare F (RealQ.ofElem t) u with
      | some .lt => pure ()
      | some _ => reason := "reached upto"; break
      | none => throw <| IO.userError "exact comparison with upto failed"
    -- collect every entry with key exactly `t`
    let mut entering := #[top]
    while !st.heap.isEmpty do
      let nxt := st.heap[0]!
      let same ← do
        if nxt.q - nxt.e > top.q + top.e then pure false
        else pure (entryValue F st.set nxt == t)
      if !same then break
      let (e, h) ← heapPop F st.set st.heap
      st := { st with heap := h }
      entering := entering.push e
    let T := DiskTest.make F { num := t, den := 1 }
    -- move the entering points; their images continue the search at level `t`
    let mut queue : Array Nat := #[]
    for e in entering do
      let z := st.set.get e.idx
      let imgs := if e.side > 0 then #[F.genA z, F.genAInv z] else #[F.genB z, F.genBInv z]
      for w in imgs do
        if st.set.size < opts.cap then
          match st.set.insert w with
          | .added s =>
            queue := queue.push st.set.size
            st := { st with set := s }
          | .present s => st := { st with set := s }
          | .overflow _ => throw <| IO.userError s!"coefficient overflow at {w}"
    st ← sweepExpand T st queue opts.cap
    let th : Threshold := { value := t, entering := entering.size, size := st.set.size }
    report th
    ths := ths.push th
  return { initialSize, thresholds := ths, stopReason := reason, stats := st.stats }

end TDCSGCompute
