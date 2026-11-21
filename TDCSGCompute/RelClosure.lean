/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Closure

/-!
# Relative (window-clipped) closures at a norm radius

This module computes the *restricted closure* of Definition 4.1 of
`notes/proofs/sharp-lower-bound-combined.md` and exports it as a *relative certificate*. The
theorem it serves (Theorem 4.2 there, restated in `notes/relative-certificates.md`): a finite
union `K'` of closed arcs of radius `r` with

* **(R1)** `∂D_L ∪ ∂D_R ∪ ∂W ⊆ K'`, and
* **(R2)** for every arc `α` of `K'` and every `S ∈ {A^{±1}, B^{±1}}`, with `D_S` the closed disk
  of radius `r` on which `S` acts, every non-degenerate component of `α ∩ D_S ∖ int W` is mapped
  by `S` into `K'`,

bounds the number of endpoints of all *strict* chains (steps taken only in the open disks) whose
intermediate points avoid `W` by `1 + 20 n F`, `F` the number of bounded faces of `ℂ ∖ K'` outside
`W`. Since a chain at any smaller radius is a strict chain at `r`, the bound holds for every
radius below `r` at once. No tangency or endpoint conditions are needed, so `r` may be a norm
radius such as `r_c`, where tangencies and triple points occur.

## Critical points and windows

The *critical points* at `r` are the lattice points on `∂D_L ∪ ∂D_R`: `P = p + w`, `p = ±1`,
`w ∈ ℤ[ζ_n]` with `|w|² = r²`. `latticeOfNorm` finds all such `w` from an exact bound: the trace
form `Tr(w w̄) = Σ_σ |σ w|² = xᵀ G x` (`x` the coefficient vector, `G_ij = Tr ζ^{i-j}`) is positive
definite with `Tr(w w̄) = Tr(r²)`, so `x_i² ≤ Tr(r²) (G⁻¹)_ii`; every vector in that box is tested.

A *window shape* is a lattice element `w ≠ 0` with `|w| < r`; with `V = {w, -w, w̄, -w̄}` it defines
`W₀ = ⋂_{v ∈ V} D(v, r)`, and `W_P = P + W₀` for every critical point `P` (the definition of §3 of
the note, for every `n`). `W₀` is compact, convex, invariant under `z ↦ -z` and `z ↦ z̄`, and its
boundary consists of arcs of the circles `C(P + v)`. The windows must be pairwise disjoint; this is
verified exactly (`windowsDisjoint`): the farthest point of `W₀` from `0` is a *corner* (a point of
two of the circles lying in all four disks), because each boundary arc lies on a circle `C(v)` and
misses that circle's farthest point from `0` (which is outside `D(-v)`), and `|x|` is unimodal along
`C(v)`. So the windows about `P ≠ Q` are disjoint if `|P - Q|² > 4 |x|²` for every corner `x`.

## Algorithm

As `TDCSGCompute.Closure`, with three changes:

1. **Window boundary arcs.** The arc of `∂W_P` on `C(P + v)` is the intersection of the arcs of
   `C(P + v)` inside the other disks `D(P + v')`; these arcs are inserted at the start.
2. **Clipping.** Every piece `α ∩ D_p` has the open arcs `α ∩ int W_P` removed before it is rotated.
   `C(c) ∩ int W_P` is the intersection of the open arcs of `C(c)` inside `D(P + v)`, from
   `(P + v, -)` to `(P + v, +)`; each is shorter than `π`, so the intersection is one arc (or
   empty). It is empty if `C(c)` does not cross every `C(P + v)` (`c = P + v`, tangency, or
   distance at least `2r` leave `C(c) ∩ int D(P + v)` empty).
3. **Tangency.** A circle tangent to `∂D_p` meets `D_p` in one point; it contributes no
   non-degenerate component, so nothing is mapped. Such tangencies are recorded with their point
   of contact `(c + p) / 2`, which by the norm argument of Lemma 2.1 of the note is a critical
   point when `c` is a lattice point.

Every order decision is the certified one of `Gen.cmp` (float filter with error bounds, exact
comparison otherwise); equal points with different symbols (triple points, which occur at norm
radii) are identified exactly and logged. After the run, `classifyCoincidences` locates each
logged coincidence exactly: whether it is a lattice point, a critical point, inside a window, on a
window boundary or in the bulk.
-/

namespace TDCSGCompute

namespace CycField

variable (F : CycField)

/-- The trace `Tr_{ℚ(ζ_n)/ℚ}` of an element (the sum of its Galois conjugates is an integer). -/
def trace (x : Elem) : Int := Id.run do
  let mut s : Int := 0
  for k in [1:F.n] do
    if Nat.gcd k F.n == 1 then s := s + (F.galois k x)[0]!
  return s

end CycField

/-- The diagonal of the inverse of a positive definite rational matrix (Gauss–Jordan), or `none`
if the matrix is singular. -/
def ratInverseDiag (G : Array (Array Rat)) : Option (Array Rat) := Id.run do
  let m := G.size
  let mut A := G
  let mut E : Array (Array Rat) :=
    (Array.range m).map fun i ↦ (Array.replicate m (0 : Rat)).set! i 1
  for col in [0:m] do
    let mut piv : Option Nat := none
    for i in [col:m] do
      if piv.isNone && A[i]![col]! != 0 then piv := some i
    let some pr := piv | return none
    let tA := A[pr]!
    let tE := E[pr]!
    A := (A.set! pr A[col]!).set! col tA
    E := (E.set! pr E[col]!).set! col tE
    let pv := A[col]![col]!
    A := A.set! col (A[col]!.map (· / pv))
    E := E.set! col (E[col]!.map (· / pv))
    for i in [0:m] do
      if i == col then continue
      let f := A[i]![col]!
      if f != 0 then
        let ac := A[col]!
        let ec := E[col]!
        A := A.set! i ((Array.range m).map fun j ↦ A[i]![j]! - f * ac[j]!)
        E := E.set! i ((Array.range m).map fun j ↦ E[i]![j]! - f * ec[j]!)
  return some ((Array.range m).map fun i ↦ E[i]![i]!)

/-- The largest natural number `b` with `b² ≤ x` (for rational `x ≥ 0`). -/
def ratFloorSqrt (x : Rat) : Nat := Id.run do
  if x ≤ 0 then return 0
  let fl : Nat := (x.num / x.den).toNat
  let mut b := 0
  while (b + 1) * (b + 1) ≤ fl do b := b + 1
  return b

/-- All `w ∈ ℤ[ζ_n]` with `|w|² = r²` (`q |w|² = R`), found from the trace-form bound of the
module docstring. Fails if the search box exceeds `maxBox` vectors. -/
def latticeOfNorm (F : CycField) (r2 : RadiusSq) (maxBox : Nat := 100000000) :
    Except String (Array Elem) := do
  let d := F.deg
  let T : Rat := (F.trace r2.num : Rat) / (r2.den : Rat)
  if T ≤ 0 then return #[]
  let G : Array (Array Rat) := (Array.range d).map fun (i : Nat) ↦ (Array.range d).map
    fun (j : Nat) ↦ ((F.trace (F.zetaPow (Int.ofNat i - Int.ofNat j)) : Int) : Rat)
  let some gd := ratInverseDiag G | throw "the trace form is singular"
  let bounds := gd.map fun g ↦ ratFloorSqrt (T * g)
  let box := bounds.foldl (fun acc b ↦ acc * (2 * b + 1)) 1
  if box > maxBox then throw s!"search box of {box} vectors is too large"
  let target := r2.num
  let q : Int := r2.den
  let mut out : Array Elem := #[]
  let mut x : Array Int := bounds.map fun (b : Nat) ↦ -(Int.ofNat b)
  for _ in [0:box] do
    if F.smul q (F.normSq x) == target then out := out.push x
    -- next vector of the box (mixed radix)
    let mut i := 0
    let mut carry := true
    while carry && i < d do
      if x[i]! < (bounds[i]! : Int) then
        x := x.set! i (x[i]! + 1)
        carry := false
      else
        x := x.set! i (-(bounds[i]! : Int))
        i := i + 1
  return out

/-- The images of `x` under the symmetries `z ↦ z, -z, z̄, -z̄` of the system. -/
def symOrbit (F : CycField) (x : Elem) : Array Elem :=
  let xc := F.conj x
  #[x, F.neg x, xc, F.neg xc]

/-- The lexicographically least element of the symmetry orbit of `x`. -/
def symCanonical (F : CycField) (x : Elem) : Elem :=
  (symOrbit F x).foldl (fun m y ↦ if elemLexLt y m then y else m) x

/-- The symmetry `g ∈ {0, 1, 2, 3}` applied to a point: bit 1 is `z ↦ z̄` (applied first), bit 0
is `z ↦ -z`. -/
def symApply (F : CycField) (g : Nat) (x : Elem) : Elem :=
  let x := if g &&& 2 != 0 then F.conj x else x
  if g &&& 1 != 0 then F.neg x else x

/-- The symmetry `g` applied to the arc of the circle about `c` from `(a)` counterclockwise to
`(b)`. A symbol `(e, s)` becomes `(g e, s)` under `z ↦ -z` and `(ē, -s)` under `z ↦ z̄`; the
reflection reverses the orientation, so the endpoints are exchanged. -/
def symArc (F : CycField) (g : Nat) (c : Elem) (a b : Sym) : Elem × Sym × Sym :=
  let c' := symApply F g c
  let a' : Sym := { a with e := symApply F g a.e }
  let b' : Sym := { b with e := symApply F g b.e }
  if g &&& 2 != 0 then (c', { b' with plus := !b'.plus }, { a' with plus := !a'.plus })
  else (c', a', b')

/-- A symmetry taking `c` to `symCanonical F c`. -/
def symCanonG (F : CycField) (c : Elem) : Nat := Id.run do
  let mut best := 0
  let mut bc := c
  for g in [1:4] do
    let x := symApply F g c
    if elemLexLt x bc then
      bc := x
      best := g
  return best

/-- Remove duplicates and sort lexicographically. -/
def sortDedup (xs : Array Elem) : Array Elem := Id.run do
  let s := xs.qsort elemLexLt
  let mut out : Array Elem := #[]
  for x in s do
    if out.back? != some x then out := out.push x
  return out

/-- The critical points at `r`: the lattice points on `∂D_L ∪ ∂D_R`, sorted. -/
def criticalPoints (F : CycField) (r2 : RadiusSq) : Except String (Array Elem) := do
  let ws ← latticeOfNorm F r2
  let mut out : Array Elem := #[]
  for w in ws do
    out := out.push (F.addInt w (-1))
    out := out.push (F.addInt w 1)
  return sortDedup out

/-- The windows about the critical points for a shape vector `w`. -/
structure WindowSet where
  /-- The shape vector. -/
  w : Elem
  /-- The distinct elements of `{w, -w, w̄, -w̄}`. -/
  shape : Array Elem
  /-- The critical points (sorted). -/
  crit : Array Elem
  /-- For each critical point `P`, the centres `P + v` of the disks bounding its window. -/
  centres : Array (Array Elem)
  /-- `m` with `ρ̄ = m / 2¹⁶` an upper bound for the circumradius of `W₀` (`circumBound`; set by
  `WindowSet.withBound`). -/
  rhoNum : Nat := 0

/-- The window set at `r² = r2` for the shape `w`: checks `w ≠ 0` and `|w| < r` exactly. -/
def WindowSet.make (C : CircleCtx) (w : Elem) : Except String WindowSet := do
  let F := C.F
  if F.isZero w then throw "the window shape vector must be non-zero (use `WindowSet.none`)"
  -- |w| < r  ⟺  R - q |w|² > 0
  match C.S.sign (F.sub C.r2.num (F.smul (C.r2.den : Int) (F.normSq w))) with
  | some s => if s ≤ 0 then throw "the window shape needs |w| < r"
  | none => throw "sign determination failed"
  let shape := sortDedup (symOrbit F w)
  let crit ← criticalPoints F C.r2
  let centres := crit.map fun P ↦ shape.map fun v ↦ F.add P v
  return { w, shape, crit, centres }

/-- No windows (`W = ∅`): the critical points are still listed. With `W = ∅` a restricted
closure is a cut set closed under the strict dynamics. -/
def WindowSet.none (C : CircleCtx) : Except String WindowSet := do
  return { w := C.F.zero, shape := #[], crit := ← criticalPoints C.F C.r2, centres := #[] }

/-- Whether there are windows. -/
def WindowSet.active (WS : WindowSet) : Bool := !WS.centres.isEmpty

/-- The corners of `W₀`: points named by `(v', ±)` on `C(v)`, `v ≠ v'` in the shape, lying in
every closed disk `D(v'', r)`. -/
def windowCorners (C : CircleCtx) (shape : Array Elem) : Except String (Array (Elem × Sym)) := do
  let mut out := #[]
  for v in shape do
    for v' in shape do
      if v == v' then continue
      if (← C.gapSign v v') ≤ 0 then continue
      for side in [false, true] do
        let s : Sym := ⟨v', side⟩
        let mut inAll := true
        for v'' in shape do
          if v'' == v || v'' == v' then continue
          if (← C.diskSign v s v'' C.r2) < 0 then inAll := false
        if inAll then out := out.push (v, s)
  return out

/-- Whether every corner `x` of `W₀` satisfies `|x| < m / 2¹⁶` (exact). -/
def cornersWithin (C : CircleCtx) (corners : Array (Elem × Sym)) (m : Nat) :
    Except String Bool := do
  let t : RadiusSq := { num := C.F.ofInt ((m * m : Nat) : Int), den := 2 ^ 32 }
  for (v, s) in corners do
    if (← C.diskSign v s C.F.zero t) ≤ 0 then return false
  return true

/-- The least `m` (by doubling, then bisection) with every corner of `W₀` at distance less than
`m / 2¹⁶` from `0`: so `ρ̄ = m / 2¹⁶` bounds the circumradius of the windows (module
docstring), up to `2⁻¹⁶`. -/
def circumBound (C : CircleCtx) (corners : Array (Elem × Sym)) : Except String Nat := do
  let mut hi := 2 ^ 16
  while !(← cornersWithin C corners hi) do hi := 2 * hi
  let mut lo := 0
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if ← cornersWithin C corners mid then hi := mid else lo := mid
  return hi

/-- Whether the windows about distinct critical points are pairwise disjoint, decided exactly by
the corner bound of the module docstring. Returns the number of pairs tested. -/
def windowsDisjoint (C : CircleCtx) (WS : WindowSet) : Except String (Bool × Nat) := do
  let F := C.F
  let corners ← windowCorners C WS.shape
  if corners.isEmpty then throw "the window has no corners"
  let mut pairs := 0
  for i in [0:WS.crit.size] do
    for j in [i + 1:WS.crit.size] do
      let t : RadiusSq := { num := F.normSq (F.sub WS.crit[i]! WS.crit[j]!), den := 4 }
      pairs := pairs + 1
      for (v, s) in corners do
        if (← C.diskSign v s F.zero t) ≤ 0 then return (false, pairs)
  return (true, pairs)

/-- The window set with its circumradius bound computed. -/
def WindowSet.withBound (C : CircleCtx) (WS : WindowSet) : Except String WindowSet := do
  if !WS.active then return WS
  let corners ← windowCorners C WS.shape
  if corners.isEmpty then throw "the window has no corners"
  return { WS with rhoNum := ← circumBound C corners }

namespace Gen

variable (G : Gen)

/-- Whether the circle about `c` certainly misses the disk of radius `ρ̄ = m / 2¹⁶` about `P`,
i.e. `| |c - P| - r | > ρ̄`, by the certified float filter (`false` if undecided). A circle that
meets `int W_P` passes within the circumradius of `P`, so such windows can be skipped. -/
def missesBall (c P : Elem) (m : Nat) : Bool :=
  let F := G.C.F
  let fd := filterData F (F.sub c P)
  if fd.big then false else
  let δ := F.trigErr
  let dx : FE := ⟨fd.x, fl2 * (G.FC.gam * fd.ax + δ * fd.s1)⟩
  let dy : FE := ⟨fd.y, fl2 * (G.FC.gam * fd.ay + δ * fd.s1)⟩
  let dist := ((dx.mul dx).add (dy.mul dy)).sqrtNonneg
  let r := (FE.mk (G.FC.rho4.v / 4) (G.FC.rho4.e / 4)).sqrtNonneg
  let t := dist.sub r
  let ρ := (m.toFloat).scaleB (-16)
  t.v.isFinite && t.e.isFinite && (t.v - t.e > ρ || t.v + t.e < -ρ)

/-- The exact sign of `4ρ - |x - y|²`, with the certified float filter first. -/
def gapSignF (x y : Elem) : IO Int := do
  let F := G.C.F
  let fd := filterData F (F.sub y x)
  if !fd.big then
    let δ := F.trigErr
    let dx : FE := ⟨fd.x, fl2 * (G.FC.gam * fd.ax + δ * fd.s1)⟩
    let dy : FE := ⟨fd.y, fl2 * (G.FC.gam * fd.ay + δ * fd.s1)⟩
    let N := (dx.mul dx).add (dy.mul dy)
    match (G.FC.rho4.sub N).sign? with
    | some s => return s
    | none => pure ()
  liftE (G.C.gapSign x y)

/-- The intersection of closed arcs of one circle, each shorter than `π` (so the result is one
arc, or `none` if it is empty or a single point). -/
def intersectArcs (c : Elem) (arcs : Array GArc) : IO (Option GArc) := do
  let some first := arcs[0]? | return none
  let mut J := first
  for i in [1:arcs.size] do
    let parts ← G.clip c J arcs[i]!
    if parts.isEmpty then return none
    if parts.size > 1 then
      throw <| IO.userError "intersection of short arcs is not connected (impossible)"
    J := parts[0]!
  return some J

/-- The closed arc `C(c) ∩ W_P` whose interior is removed when clipping (`none` if
`C(c) ∩ int W_P = ∅`). The centres must all cross `C(c)` (`CircSt.wins`). -/
def windowArc (c : Elem) (centres : Array Elem) : IO (Option GArc) := do
  let mut arcs := #[]
  for f in centres do
    arcs := arcs.push { a := ← G.mkPt c ⟨f, false⟩, b := ← G.mkPt c ⟨f, true⟩ }
  G.intersectArcs c arcs

/-- The arc of `∂W_P` on the circle about `centres[i]`. -/
def windowBoundaryArc (centres : Array Elem) (i : Nat) : IO (Option GArc) := do
  let f := centres[i]!
  let mut arcs := #[]
  for j in [0:centres.size] do
    if j == i then continue
    let f' := centres[j]!
    arcs := arcs.push { a := ← G.mkPt f ⟨f', false⟩, b := ← G.mkPt f ⟨f', true⟩ }
  G.intersectArcs f arcs

end Gen

/-- Outcome of a relative closure. -/
inductive RelStatus where
  /-- The closure terminated. -/
  | closed
  /-- A cap was reached; nothing is claimed. -/
  | cap (what : String)
  deriving Inhabited

/-- The result of a relative closure. -/
structure RelResult where
  /-- How it ended. -/
  status : RelStatus
  /-- The store. -/
  store : Std.HashMap Elem CircSt
  /-- Counters of the shared machinery. -/
  stats : Stats
  /-- Circles tangent to a boundary circle, `(c, p)`. -/
  tangencies : Array (Elem × Elem)
  /-- Clipped pieces on circles that cross the interior of some window. -/
  windowClips : Nat
  /-- Run time in milliseconds. -/
  millis : Nat

/-- The state of a circle seen for the first time: its relation to the two disks and the windows
whose bounding circles all cross it. Tangencies to `∂D_p` are allowed (sign `0`). -/
def relNewCircle (G : Gen) (WS : WindowSet) (c : Elem) : IO CircSt := do
  let C := G.C
  let mL ← if c == C.left then pure 0 else G.gapSignF c C.left
  let mR ← if c == C.right then pure 0 else G.gapSignF c C.right
  let mut wins := #[]
  for k in [0:WS.centres.size] do
    if G.missesBall c WS.crit[k]! WS.rhoNum then continue
    let mut all := true
    for f in WS.centres[k]! do
      if !all then break
      if f == c then all := false
      else if (← G.gapSignF c f) ≤ 0 then all := false
    if all then wins := wins.push k
  return { meetL := mL, meetR := mR, wins }

/-- Insert the arc `X` of the circle about `c` into the store; the uncovered parts go on the work
list. Returns the updated store, work list and the number of new pieces. -/
def relInsert (G : Gen) (WS : WindowSet) (store : Std.HashMap Elem CircSt)
    (work : Array (Elem × Option GArc)) (tang : IO.Ref (Array (Elem × Elem))) (c : Elem)
    (sa sb : Sym) : IO (Std.HashMap Elem CircSt × Array (Elem × Option GArc) × Nat) := do
  let st ← match store.get? c with
    | some st => pure st
    | none =>
      let st ← relNewCircle G WS c
      for (p, m) in [(G.C.left, st.meetL), (G.C.right, st.meetR)] do
        if c != p && m == 0 then tang.modify (·.push (c, p))
      pure st
  if st.full then
    return (if store.contains c then store else store.insert c st, work, 0)
  let X : GArc := { a := ← G.mkPt c sa, b := ← G.mkPt c sb }
  let gaps ← G.uncovered c X st.arcs
  let mut st := st
  let mut work := work
  for g in gaps do
    st ← G.mergeArc c st g
    work := work.push (c, some g)
  return (store.insert c st, work, gaps.size)

/-- Insert an image arc, in the symmetric mode reduced to the canonical circle of its orbit
together with its images under the stabiliser of that circle. -/
def relInsertS (G : Gen) (WS : WindowSet) (sym : Bool) (store : Std.HashMap Elem CircSt)
    (work : Array (Elem × Option GArc)) (tang : IO.Ref (Array (Elem × Elem))) (c : Elem)
    (sa sb : Sym) : IO (Std.HashMap Elem CircSt × Array (Elem × Option GArc) × Nat) := do
  if !sym then return ← relInsert G WS store work tang c sa sb
  let F := G.C.F
  let (c0, a0, b0) := symArc F (symCanonG F c) c sa sb
  let (s, w, k) ← relInsert G WS store work tang c0 a0 b0
  let mut store := s
  let mut work := w
  let mut total := k
  for h in [1:4] do
    if symApply F h c0 == c0 then
      let (_, a1, b1) := symArc F h c0 a0 b0
      let (s, w, k) ← relInsert G WS store work tang c0 a1 b1
      store := s
      work := w
      total := total + k
  return (store, work, total)

/-- Compute the smallest restricted closure for the windows `WS` (module docstring). With `sym`,
only one circle of each orbit of `z ↦ ±z, ±z̄` is stored (the lexicographically least, with all
arcs of `K'` on it); this is exact because the system, the windows and hence the smallest
restricted closure are invariant under these maps (`z ↦ -z` exchanges `A` and `B`, `z ↦ z̄`
exchanges `A` and `A⁻¹`), and the images of `g(α)` are the `g`-images of the images of `α`. -/
def relClosure (G : Gen) (WS : WindowSet) (opts : CloseOptions) (sym : Bool := false) :
    IO RelResult := do
  let t0 ← IO.monoMsNow
  let C := G.C
  let tang ← IO.mkRef (#[] : Array (Elem × Elem))
  let mut clips := 0
  let mut store : Std.HashMap Elem CircSt := {}
  let bds := if sym then [C.left] else [C.left, C.right]
  for p in bds do
    let st ← relNewCircle G WS p
    store := store.insert p { st with full := true }
  let mut work : Array (Elem × Option GArc) := bds.toArray.map fun p ↦ (p, none)
  G.stats.modify fun st ↦ { st with pieces := 2 }
  -- the window boundary arcs
  for cs in WS.centres do
    for i in [0:cs.size] do
      match ← G.windowBoundaryArc cs i with
      | none => pure ()
      | some A =>
        let (s, w, k) ← relInsertS G WS sym store work tang cs[i]! A.a.sym A.b.sym
        store := s
        work := w
        G.stats.modify fun st ↦ { st with pieces := st.pieces + k }
  let finish (status : RelStatus) (store : Std.HashMap Elem CircSt) (clips : Nat) :
      IO RelResult := do
    return { status, store, stats := ← G.stats.get, tangencies := ← tang.get,
             windowClips := clips, millis := (← IO.monoMsNow) - t0 }
  let mut processed : Nat := 0
  while !work.isEmpty do
    let (c, α) := work.back!
    work := work.pop
    processed := processed + 1
    if opts.progress > 0 && processed % opts.progress == 0 then
      IO.eprintln s!"  processed {processed}, circles {store.size}, work {work.size}, \
        pieces {(← G.stats.get).pieces}, {((← IO.monoMsNow) - t0) / 1000} s"
    if processed % 1000 == 0 && opts.maxSeconds > 0 &&
        (← IO.monoMsNow) - t0 > opts.maxSeconds * 1000 then
      return ← finish (.cap "time") store clips
    let stc := store.getD c {}
    if !((c != C.left && stc.meetL > 0) || (c != C.right && stc.meetR > 0)) then continue
    -- the open window arcs to remove from pieces of this circle
    let mut holes : Array GArc := #[]
    for k in stc.wins do
      if let some J ← G.windowArc c WS.centres[k]! then holes := holes.push J
    for (p, meet) in [(C.left, stc.meetL), (C.right, stc.meetR)] do
      if c == p || meet ≤ 0 then continue
      let Wp : GArc := { a := ← G.mkPt c ⟨p, false⟩, b := ← G.mkPt c ⟨p, true⟩ }
      let pieces ← match α with
        | none => pure #[Wp]
        | some X => G.clip c X Wp
      for piece in pieces do
        let rems ← if holes.isEmpty then pure #[piece] else G.uncovered c piece holes
        if !holes.isEmpty then clips := clips + 1
        for Z in rems do
          for k in [(-1 : Int), 1] do
            let c' := C.rot p k c
            G.stats.modify fun st ↦ { st with images := st.images + 1 }
            let (s, w, n) ← relInsertS G WS sym store work tang c' (C.rotSym p k Z.a.sym)
              (C.rotSym p k Z.b.sym)
            store := s
            work := w
            if n > 0 then G.stats.modify fun st ↦ { st with pieces := st.pieces + n }
            if (← G.stats.get).pieces > opts.maxPieces then
              return ← finish (.cap "pieces") store clips
            if store.size > opts.maxCircles then
              return ← finish (.cap "circles") store clips
  finish .closed store clips

/-- Where a coincidence (a point of three or more circles) lies. -/
structure CoincidenceClass where
  /-- Distinct `(centre, symbol, symbol)` records. -/
  records : Nat := 0
  /-- Distinct points among them (records naming the same lattice point counted once; non-lattice
  points are counted per record). -/
  latticePoints : Nat := 0
  /-- Records at a critical point. -/
  atCritical : Nat := 0
  /-- Records at a lattice point that is not critical. -/
  atOtherLattice : Nat := 0
  /-- Records at a non-lattice point. -/
  nonLattice : Nat := 0
  /-- Records in the interior of a window. -/
  inWindow : Nat := 0
  /-- Records on a window boundary. -/
  onWindowBoundary : Nat := 0
  /-- Records outside all windows. -/
  inBulk : Nat := 0
  /-- Up to ten records outside the windows, for the report. -/
  bulkExamples : Array (Elem × Sym × Sym) := #[]

/-- The lattice point named by `s` on the circle about `c`, if it is one: `c + w` with `|w| = r`,
on the circle about `s.e`, on side `s`. -/
def latticePointOf (C : CircleCtx) (norms : Array Elem) (c : Elem) (s : Sym) :
    Except String (Option Elem) := do
  let F := C.F
  let d := F.sub s.e c
  for w in norms do
    let y := F.add c w
    if F.smul (C.r2.den : Int) (F.normSq (F.sub y s.e)) != C.r2.num then continue
    -- side of `y` relative to `d`: the sign of `Im (w d̄)`
    let z := F.mul w (F.conj d)
    let t := F.neg (F.mul (F.sub z (F.conj z)) C.omega)
    match C.S.sign t with
    | some v => if (v > 0) == s.plus && v != 0 then return some y
    | none => throw "sign determination failed"
  return none

/-- Locate the logged coincidences exactly (see `CoincidenceClass`). -/
def classifyCoincidences (C : CircleCtx) (WS : WindowSet) (log : Array (Elem × Sym × Sym)) :
    Except String CoincidenceClass := do
  let F := C.F
  let norms ← latticeOfNorm F C.r2
  let key (c : Elem) (a b : Sym) : String :=
    let sa := s!"{elemToString a.e}{a.plus}"
    let sb := s!"{elemToString b.e}{b.plus}"
    let (lo, hi) := if decide (sa < sb) then (sa, sb) else (sb, sa)
    s!"{elemToString c}|{lo}|{hi}"
  let mut seen : Std.HashMap String Unit := {}
  let mut pts : Std.HashMap Elem Unit := {}
  let mut K : CoincidenceClass := {}
  for (c, a, b) in log do
    let k := key c a b
    if seen.contains k then continue
    seen := seen.insert k ()
    K := { K with records := K.records + 1 }
    match ← latticePointOf C norms c a with
    | some y =>
      if !pts.contains y then
        pts := pts.insert y ()
        K := { K with latticePoints := K.latticePoints + 1 }
      if WS.crit.contains y then K := { K with atCritical := K.atCritical + 1 }
      else K := { K with atOtherLattice := K.atOtherLattice + 1 }
    | none => K := { K with nonLattice := K.nonLattice + 1 }
    -- location relative to the windows
    let mut loc := 0  -- 0 bulk, 1 boundary, 2 interior
    for cs in WS.centres do
      let mut allPos := true
      let mut allNonneg := true
      for f in cs do
        let s ← if f == c then pure 0 else C.diskSign c a f C.r2
        if s ≤ 0 then allPos := false
        if s < 0 then allNonneg := false
      if allPos then loc := 2
      else if allNonneg && loc < 1 then loc := 1
    if loc == 2 then K := { K with inWindow := K.inWindow + 1 }
    else if loc == 1 then K := { K with onWindowBoundary := K.onWindowBoundary + 1 }
    else
      K := { K with inBulk := K.inBulk + 1,
                    bulkExamples := if K.bulkExamples.size < 10
                      then K.bulkExamples.push (c, a, b) else K.bulkExamples }
  return K

/-- The summary of a closed relative run. -/
structure RelSummary where
  /-- Circles. -/
  circles : Nat
  /-- Full circles. -/
  fullCircles : Nat
  /-- Maximal arcs (full circles included). -/
  arcs : Nat
  /-- Circles modulo the symmetries `±z, ±z̄` (one per orbit). -/
  canonCircles : Nat
  /-- Maximal arcs on one circle of each orbit. -/
  canonArcs : Nat
  /-- The largest `|σ_k(c)|` over the centres, per non-identity embedding. -/
  maxConj : Array (Nat × Float)

/-- Count a closed relative store. -/
def relSummarize (F : CycField) (store : Std.HashMap Elem CircSt) (sym : Bool) :
    RelSummary := Id.run do
  let ks := F.embeddings.filter (· != 1)
  let mut mx : Array Float := ks.map fun _ ↦ 0
  let mut arcs := 0
  let mut circles := 0
  let mut full := 0
  let mut cc := 0
  let mut ca := 0
  for (c, st) in store.toList do
    for i in [0:ks.size] do
      let (x, y) := F.evalConjF ks[i]! c
      mx := mx.set! i (max mx[i]! (Float.sqrt (x * x + y * y)))
    let k := if st.full then 1 else st.arcs.size
    -- the number of circles this stored circle stands for
    let orbit := if sym then 4 / ((List.range 4).filter fun h ↦ symApply F h c == c).length
      else 1
    if st.full then full := full + orbit
    circles := circles + orbit
    arcs := arcs + orbit * k
    if sym || symCanonical F c == c then
      cc := cc + 1
      ca := ca + k
  return { circles, fullCircles := full, arcs, canonCircles := cc, canonArcs := ca,
           maxConj := ks.zip mx }

/-- Condition (C4) of the cut-set certificate theorem on the stored maximal arcs: every endpoint
equal to `(p, -)` must start its arc and every endpoint equal to `(p, +)` must end it. Returns
`(endpoints on boundary circles, failures)`. Relevant without windows. -/
def relC4 (G : Gen) (store : Std.HashMap Elem CircSt) : IO (Nat × Nat) := do
  let C := G.C
  let mut onb := 0
  let mut bad := 0
  for (c, st) in store.toList do
    if st.full then continue
    for (p, meet) in [(C.left, st.meetL), (C.right, st.meetR)] do
      if c == p || meet ≤ 0 then continue
      let wm ← G.mkPt c ⟨p, false⟩
      let wp ← G.mkPt c ⟨p, true⟩
      for A in st.arcs do
        for (isStart, x) in [(true, A.a), (false, A.b)] do
          for (w, wantStart) in [(wm, true), (wp, false)] do
            if (← G.cmp c x w) == .eq then
              onb := onb + 1
              if isStart != wantStart then bad := bad + 1
  return (onb, bad)

/-- Write the relative certificate (format in `notes/relative-certificates.md`) line by line
through `emit`. In the symmetric mode the arcs are those of the stored canonical circles, and the
line `symmetric` says that `K'` is their union under `z ↦ ±z, ±z̄`. -/
def relWriteCertificate (G : Gen) (WS : WindowSet) (store : Std.HashMap Elem CircSt)
    (sym : Bool) (S : RelSummary) (comment : Array String) (emit : String → IO Unit) :
    IO Unit := do
  let C := G.C
  let symS (s : Sym) : String := s!"{elemToString s.e} {if s.plus then "+" else "-"}"
  emit "tdcsg-relative-certificate 1\n"
  for l in comment do emit s!"# {l}\n"
  emit s!"n {C.F.n}\n"
  emit s!"r2 {elemToString C.r2.num} / {C.r2.den}\n"
  emit s!"window {elemToString WS.w}\n"
  if sym then emit "symmetric\n"
  for P in WS.crit do emit s!"critical {elemToString P}\n"
  let centres := (store.toArray.map (·.1)).qsort elemLexLt
  let mut listed := 0
  let mut nArcs := 0
  for c in centres do
    let st := store.getD c {}
    listed := listed + 1
    if st.full then
      emit s!"full {elemToString c}\n"
      nArcs := nArcs + 1
      continue
    let arcs ← sortArcsM (fun x y ↦ G.cmp c x.a y.a) st.arcs
    nArcs := nArcs + arcs.size
    for A in arcs do
      emit s!"arc {elemToString c} {symS A.a.sym} {symS A.b.sym}\n"
  let _ := S
  emit s!"summary circles {listed} arcs {nArcs} windows {WS.crit.size}\n"
  emit "end\n"

/-- The outcome of `certifyRelative`. -/
structure RelOutcome where
  /-- The window set. -/
  WS : WindowSet
  /-- The closure run. -/
  result : RelResult
  /-- Counts (if closed). -/
  summary : Option RelSummary
  /-- The located coincidences (if closed). -/
  coinc : Option CoincidenceClass
  /-- Tangency points that are critical points. -/
  tangentAtCritical : Nat
  /-- Condition (C4) on the stored arcs: `(endpoints on boundary circles, failures)`. -/
  c4 : Nat × Nat := (0, 0)
  /-- The certificate text (if closed; empty if it was written to a file). -/
  text : Option String
  /-- Why there is no certificate (empty if there is one). -/
  reason : String

/-- Compute the restricted closure for `r² = r2` and the window shape `w`, and produce the
relative certificate if it closes. -/
def certifyRelative (F : CycField) (r2 : RadiusSq) (w : Elem) (opts : CloseOptions)
    (comment : Array String := #[]) (sym : Bool := false) (out : Option System.FilePath := none) :
    IO RelOutcome := do
  let G : Gen := { FC := FilterCtx.make (CircleCtx.make F r2), stats := ← IO.mkRef {} }
  let C := G.C
  let WS ← Gen.liftE (if F.isZero w then WindowSet.none C
    else WindowSet.make C w >>= WindowSet.withBound C)
  let (disj, _) ← if WS.active then Gen.liftE (windowsDisjoint C WS) else pure (true, 0)
  let empty : RelResult := { status := .cap "none", store := {}, stats := {}, tangencies := #[],
                             windowClips := 0, millis := 0 }
  if !disj then
    return { WS, result := empty, summary := none, coinc := none, tangentAtCritical := 0,
             text := none, reason := "the windows are not pairwise disjoint" }
  let res ← relClosure G WS opts sym
  -- tangency points: (c + p) / 2 must be a critical point
  let mut tc := 0
  for (c, p) in res.tangencies do
    let d := F.sub c p
    if d.all (· % 2 == 0) then
      if WS.crit.contains (F.add p (d.map (· / 2))) then tc := tc + 1
  match res.status with
  | .cap what =>
    return { WS, result := res, summary := none, coinc := none, tangentAtCritical := tc,
             text := none, reason := s!"cap reached ({what}); nothing is claimed (raise \
               --max-pieces, --max-circles or --max-seconds)" }
  | .closed =>
    let S := relSummarize F res.store sym
    let c4 ← relC4 G res.store
    let K ← Gen.liftE (classifyCoincidences C WS res.stats.coincLog)
    let text ← match out with
      | some path =>
        IO.FS.withFile path .write fun h ↦
          relWriteCertificate G WS res.store sym S comment h.putStr
        pure ""
      | none =>
        let buf ← IO.mkRef ""
        relWriteCertificate G WS res.store sym S comment fun t ↦ buf.modify (· ++ t)
        buf.get
    return { WS, result := res, summary := some S, coinc := some K, tangentAtCritical := tc,
             c4, text := some text, reason := "" }

end TDCSGCompute
