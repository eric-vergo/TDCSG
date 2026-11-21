/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Permutation groups: Schreier–Sims and orders of products of alternating groups

A permutation of `{0, …, D - 1}` is the array of its images. `Perm.mul p q` is `p ∘ q`
(first `q`, then `p`).

## Schreier–Sims

`BSGS.build` is the deterministic Schreier–Sims algorithm with explicit transversals
(Holt, Eick, O'Brien, *Handbook of Computational Group Theory*, §4.4.1). Every level `i` holds a
base point `β_i`, generators `S_i` fixing `β_1, …, β_{i-1}`, the orbit `β_i^{⟨S_i⟩}` and, for each
orbit point `γ`, a group element `u_γ` with `u_γ β_i = γ`. A level is *complete* when every
Schreier generator `u_{sγ}⁻¹ s u_γ` (`γ` in the orbit, `s ∈ S_i`) sifts to the identity through the
levels below it. The algorithm completes the levels from the bottom up, adding every non-trivial
sift residue as a new strong generator; when all levels are complete, `⟨S_{i+1}⟩` is the stabiliser
of `β_i` in `⟨S_i⟩` (Schreier's lemma), so the group order is the product of the orbit lengths.
Sifting only multiplies by group elements, so every strong generator lies in the group.

## Products of alternating groups

`structuralOrder` computes the order of a group `G = ⟨g_1, …, g_k⟩` that acts on a union of
orbits `O_1, …, O_m` without building a stabiliser chain on the large orbits. It uses these facts.

1. **Equivalent constituents.** If the actions of `G` on `O_i` and `O_j` are equivalent (a
   bijection `O_i → O_j` commutes with every generator; checked explicitly), then an element acts
   trivially on `O_j` iff it does on `O_i`, so `O_j` can be dropped without changing `G`.
2. **Alternating constituents** (Jordan). If `G` is transitive on `O` (`|O| = d`) and some element
   has a cycle of prime length `p` with `d / 2 < p ≤ d - 3`, then a power of it is a `p`-cycle, the
   action is primitive (a block system would have to be fixed blockwise by the `p`-cycle, forcing a
   block of size `≥ p > d / 2`), and a primitive group containing a `p`-cycle with `p ≤ d - 3`
   contains `Alt(O)` (Jordan; Wielandt, *Finite Permutation Groups*, Thm. 13.9). Such an `O`, with
   `d ≥ 9`, is called *big*; let `B` be the big orbits and `R` the others.
3. **Kernel witnesses.** Suppose that for every big `O_i` some element `w` has a cycle on `O_i`
   whose length does not divide `m = ` the order of `w` on `⋃_R O_j`. Then `w^m` is trivial on the
   `R`-orbits and non-trivial on `O_i`, so the kernel `K` of the action on `⋃_R O_j` has a
   non-trivial normal projection to `O_i`, which therefore contains `Alt(O_i)`. The derived group
   `K'` is then a subdirect product of the simple groups `Alt(O_i)`, `i ∈ B`, hence a product of
   diagonals; a diagonal linking `O_i` and `O_j` is normalised by `G`, which (the centraliser of
   `Alt(d)` in `Sym(d)` being trivial, and every automorphism of `Alt(d)` for `d ≠ 6` being induced
   by a bijection) makes the two actions equivalent. After step 1 there are none, so
   `K' = ∏_B Alt(O_i)` and `N = G ∩ ∏_B Alt(O_i) = ∏_B Alt(O_i)`.
4. **The quotient.** `G / N` is the image of `G` under `g ↦ (g|_R, sgn(g|_{O_i}))_{i ∈ B}`, a
   permutation group on `⋃_R O_j` plus two points per big orbit (a sign is a transposition of its
   two points); its order is computed with Schreier–Sims. Then
   `|G| = |G / N| · ∏_B |O_i|! / 2`.

When a witness is missing, or the quotient is too large for Schreier–Sims within the work limit,
the order is reported as undetermined (with the lower bound `|G/N|` replaced by `1` and the big
orbits that were certified).
-/

namespace TDCSGCompute

/-- A permutation of `{0, …, D - 1}` as its array of images. -/
abbrev Perm := Array Nat

namespace Perm

/-- The identity of degree `n`. -/
def one (n : Nat) : Perm := Array.range n

/-- `p ∘ q`: first `q`, then `p`. -/
def mul (p q : Perm) : Perm := q.map fun x ↦ p[x]!

/-- The inverse. -/
def inv (p : Perm) : Perm := Id.run do
  let mut r : Array Nat := Array.replicate p.size 0
  for i in [0:p.size] do
    r := r.set! p[i]! i
  return r

/-- Whether `p` is the identity. -/
def isOne (p : Perm) : Bool := Id.run do
  for i in [0:p.size] do
    if p[i]! != i then return false
  return true

/-- The first point moved by `p`, if any. -/
def firstMoved (p : Perm) : Option Nat := Id.run do
  for i in [0:p.size] do
    if p[i]! != i then return some i
  return none

/-- Whether `p` is a permutation of `{0, …, size - 1}`. -/
def isValid (p : Perm) : Bool := Id.run do
  let mut seen : Array Bool := Array.replicate p.size false
  for x in p do
    if x ≥ p.size || seen[x]! then return false
    seen := seen.set! x true
  return true

/-- The lengths of the cycles of `p` on the points `pts` (a `p`-invariant set, listed without
repetition), including fixed points. -/
def cycleLengthsOn (p : Perm) (pts : Array Nat) : Array Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array Nat := #[]
  for x in pts do
    if !seen.contains x then
      let mut len := 0
      let mut y := x
      while !seen.contains y do
        seen := seen.insert y
        y := p[y]!
        len := len + 1
      out := out.push len
  return out

/-- The lengths of all cycles of `p`, including fixed points. -/
def cycleLengths (p : Perm) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate p.size false
  let mut out : Array Nat := #[]
  for x in [0:p.size] do
    if !seen[x]! then
      let mut len := 0
      let mut y := x
      while !seen[y]! do
        seen := seen.set! y true
        y := p[y]!
        len := len + 1
      out := out.push len
  return out

/-- The order of a permutation with the given cycle lengths. -/
def orderOfLengths (ls : Array Nat) : Nat := ls.foldl Nat.lcm 1

/-- The order of `p`. -/
def order (p : Perm) : Nat := orderOfLengths p.cycleLengths

/-- `0` for even and `1` for odd cycle lengths `ls` (the sign as an element of `ℤ/2`). -/
def parityOfLengths (ls : Array Nat) : Nat := (ls.foldl (fun s l ↦ s + (l - 1)) 0) % 2

/-- The permutation of `{0, …, D - 1}` with the given cycles (points not listed are fixed). -/
def ofCycles (D : Nat) (cycles : List (List Nat)) : Perm := Id.run do
  let mut p := one D
  for c in cycles do
    let arr := c.toArray
    for i in [0:arr.size] do
      p := p.set! arr[i]! arr[(i + 1) % arr.size]!
  return p

/-- The restriction of `p` to the invariant set `pts`, relabelled by positions in `pts`. -/
def restrict (p : Perm) (pts : Array Nat) (pos : Std.HashMap Nat Nat) : Perm :=
  pts.map fun x ↦ pos.getD p[x]! 0

end Perm

/-- Whether `p` is prime (trial division; used for cycle lengths). -/
def isPrimeNat (p : Nat) : Bool := Id.run do
  if p < 2 then return false
  let mut q := 2
  while q * q ≤ p do
    if p % q == 0 then return false
    q := q + 1
  return true

/-- `n!`. -/
def factorial (n : Nat) : Nat := (List.range n).foldl (fun a k ↦ a * (k + 1)) 1

/-- One level of a stabiliser chain. -/
structure SSLevel where
  /-- The base point. -/
  base : Nat
  /-- Strong generators fixing the earlier base points. -/
  gens : Array Perm
  /-- The orbit of the base point under `gens`, in discovery order. -/
  orbit : Array Nat
  /-- `trans[γ] = some (u, u⁻¹)` with `u base = γ`, for `γ` in the orbit. -/
  trans : Array (Option (Perm × Perm))
  /-- For each orbit position, how many generators have had their Schreier generator sifted. -/
  checked : Array Nat
  deriving Inhabited

/-- A base and strong generating set, built by `BSGS.build`. -/
structure BSGS where
  /-- The degree. -/
  deg : Nat
  /-- The levels. -/
  levels : Array SSLevel
  /-- Work counter (number of sifts), for the work limit. -/
  work : Nat := 0
  /-- Work limit; `build` gives up (returns `none`) beyond it. -/
  limit : Nat
  deriving Inhabited

namespace BSGS

/-- A new level with base point `β` and no generators. -/
def newLevel (D β : Nat) : SSLevel :=
  { base := β, gens := #[], orbit := #[β],
    trans := (Array.replicate D none).set! β (some (Perm.one D, Perm.one D)), checked := #[0] }

/-- Add the generator `s` to level `l`, extending its orbit and transversal. -/
def addGen (B : BSGS) (l : Nat) (s : Perm) : BSGS := Id.run do
  let L := B.levels[l]!
  let gens := L.gens.push s
  let mut orbit := L.orbit
  let mut trans := L.trans
  let mut checked := L.checked
  -- images of the old orbit under `s`, then closure of new points under all generators
  let mut head := 0
  let oldSize := orbit.size
  for i in [0:oldSize] do
    let γ := orbit[i]!
    let δ := s[γ]!
    if trans[δ]!.isNone then
      let (u, _) := trans[γ]!.get!
      let v := Perm.mul s u
      trans := trans.set! δ (some (v, Perm.inv v))
      orbit := orbit.push δ
      checked := checked.push 0
  head := oldSize
  while head < orbit.size do
    let γ := orbit[head]!
    for g in gens do
      let δ := g[γ]!
      if trans[δ]!.isNone then
        let (u, _) := trans[γ]!.get!
        let v := Perm.mul g u
        trans := trans.set! δ (some (v, Perm.inv v))
        orbit := orbit.push δ
        checked := checked.push 0
    head := head + 1
  return { B with levels := B.levels.set! l { L with gens, orbit, trans, checked } }

/-- Sift `g` through the levels from `l` on: the residue and the level at which it stopped
(`levels.size` if it passed all levels). -/
def sift (B : BSGS) (g : Perm) (l : Nat) : Perm × Nat := Id.run do
  let mut h := g
  for j in [l:B.levels.size] do
    let L := B.levels[j]!
    let γ := h[L.base]!
    match L.trans[γ]! with
    | none => return (h, j)
    | some (_, ui) => h := Perm.mul ui h
  return (h, B.levels.size)

/-- Insert a non-trivial residue `h` that stopped at level `j`, into the levels `l .. j` (creating
level `j` if needed). -/
def insertResidue (B : BSGS) (h : Perm) (l j : Nat) : BSGS := Id.run do
  let mut B := B
  if j == B.levels.size then
    let β := (Perm.firstMoved h).getD 0
    B := { B with levels := B.levels.push (newLevel B.deg β) }
  for m in [l:j + 1] do
    B := B.addGen m h
  return B

/-- Make level `l` complete, assuming the levels below it are complete; completes lower levels
again whenever they receive new generators. Returns `none` beyond the work limit. -/
partial def complete (B : BSGS) (l : Nat) : Option BSGS := Id.run do
  let mut B := B
  let mut pos := 0
  while pos < B.levels[l]!.orbit.size do
    let L := B.levels[l]!
    if L.checked[pos]! ≥ L.gens.size then
      pos := pos + 1
    else
      let gi := L.checked[pos]!
      B := { B with levels := B.levels.set! l { L with checked := L.checked.set! pos (gi + 1) } }
      let γ := L.orbit[pos]!
      let s := L.gens[gi]!
      let δ := s[γ]!
      let (u, _) := L.trans[γ]!.get!
      let (_, vi) := L.trans[δ]!.get!
      let sch := Perm.mul vi (Perm.mul s u)
      B := { B with work := B.work + 1 }
      if B.work > B.limit then return none
      let (h, j) := B.sift sch (l + 1)
      if !h.isOne then
        B := B.insertResidue h (l + 1) j
        -- complete the levels that received the residue, deepest first
        let mut m := j
        while m > l do
          match B.complete m with
          | none => return none
          | some B' => B := B'
          m := m - 1
  return some B

/-- Build a base and strong generating set of `⟨gens⟩` on `D` points; `none` beyond `limit`
sifts. -/
def build (D : Nat) (gens : Array Perm) (limit : Nat := 10000000) : Option BSGS := Id.run do
  let mut B : BSGS := { deg := D, levels := #[], limit }
  for g in gens do
    let (h, j) := B.sift g 0
    if !h.isOne then
      B := B.insertResidue h 0 j
      let mut m := j + 1
      while m > 0 do
        m := m - 1
        match B.complete m with
        | none => return none
        | some B' => B := B'
  return some B

/-- The group order `∏ |orbit_i|`. -/
def order (B : BSGS) : Nat := B.levels.foldl (fun a L ↦ a * L.orbit.size) 1

/-- Membership test (valid once `build` has returned). -/
def contains (B : BSGS) (g : Perm) : Bool := (B.sift g 0).1.isOne

end BSGS

/-- The order of `⟨gens⟩` on `D` points by Schreier–Sims, or `none` beyond the work limit. -/
def schreierSimsOrder (D : Nat) (gens : Array Perm) (limit : Nat := 10000000) : Option Nat :=
  (BSGS.build D gens limit).map BSGS.order

/-! ### Orbits, equivalence and the structural order -/

/-- The orbits of `⟨gens⟩` on `{0, …, D - 1}`, each in discovery order. -/
def orbitsOf (D : Nat) (gens : Array Perm) : Array (Array Nat) := Id.run do
  let mut seen : Array Bool := Array.replicate D false
  let mut out : Array (Array Nat) := #[]
  for x in [0:D] do
    if !seen[x]! then
      seen := seen.set! x true
      let mut orb : Array Nat := #[x]
      let mut head := 0
      while head < orb.size do
        let y := orb[head]!
        for g in gens do
          let z := g[y]!
          if !seen[z]! then
            seen := seen.set! z true
            orb := orb.push z
        head := head + 1
      out := out.push orb
  return out

/-- For each point, the length of the cycle of `p` through it. -/
def cycleLenArray (p : Perm) : Array Nat := Id.run do
  let mut out : Array Nat := Array.replicate p.size 0
  for x in [0:p.size] do
    if out[x]! == 0 then
      let mut len := 1
      let mut y := p[x]!
      while y != x do
        y := p[y]!
        len := len + 1
      out := out.set! x len
      y := p[x]!
      while y != x do
        out := out.set! y len
        y := p[y]!
  return out

/-- A transitive action of the generators on `{0, …, d - 1}` (a constituent), with invariants used
to test equivalence quickly. -/
structure Constituent where
  /-- The generators, restricted and relabelled. -/
  gens : Array Perm
  /-- Sorted cycle lengths of each generator and of the product of the first two. -/
  key : Array (Array Nat)
  /-- `sig[k][x]`: the length of the cycle through `x` of the `k`-th permutation of `key`. -/
  sig : Array (Array Nat)
  deriving Inhabited

namespace Constituent

/-- The constituent with the given generators. -/
def make (gens : Array Perm) : Constituent :=
  let ps := if gens.size ≥ 2 then gens.push (Perm.mul gens[0]! gens[1]!) else gens
  { gens, key := ps.map fun p ↦ p.cycleLengths.qsort (· < ·), sig := ps.map cycleLenArray }

/-- The degree. -/
def deg (C : Constituent) : Nat := (C.gens[0]?.map (·.size)).getD 0

/-- Try to extend `0 ↦ y` to a bijection commuting with the generators of `C` and `C'`. -/
def tryMap (C C' : Constituent) (y : Nat) : Bool := Id.run do
  let d := C.deg
  let mut f : Array Nat := Array.replicate d d
  let mut used : Array Bool := Array.replicate d false
  f := f.set! 0 y
  used := used.set! y true
  let mut queue : Array Nat := #[0]
  let mut head := 0
  while head < queue.size do
    let x := queue[head]!
    head := head + 1
    for k in [0:C.gens.size] do
      let x' := C.gens[k]![x]!
      let y' := C'.gens[k]![f[x]!]!
      if f[x']! == d then
        if used[y']! then return false
        f := f.set! x' y'
        used := used.set! y' true
        queue := queue.push x'
      else if f[x']! != y' then return false
  return queue.size == d

/-- Whether the actions `C` and `C'` are equivalent, decided by an explicit bijection commuting
with the generators (the invariants only select the candidates for the image of `0`). -/
def equivalent (C C' : Constituent) : Bool := Id.run do
  if C.deg != C'.deg || C.gens.size != C'.gens.size || C.key != C'.key then return false
  let d := C.deg
  if d == 0 then return true
  let s0 := C.sig.map (·[0]!)
  for y in [0:d] do
    if C'.sig.map (·[y]!) == s0 then
      if tryMap C C' y then return true
  return false

end Constituent

/-- The size of the smallest block of imprimitivity containing `0` and another point (Atkinson's
algorithm: the finest block system in which `0` and `β` are together, for every `β`). Equals the
degree when the action is primitive. -/
def Constituent.minBlockSize (C : Constituent) : Nat := Id.run do
  let d := C.deg
  if d ≤ 2 then return d
  let mut best := d
  for β in [1:d] do
    let mut parent : Array Nat := Array.range d
    let find (par : Array Nat) (x : Nat) : Nat := Id.run do
      let mut y := x
      let mut fuel := d
      while par[y]! != y && fuel > 0 do
        y := par[y]!
        fuel := fuel - 1
      return y
    parent := parent.set! β 0
    let mut queue : Array (Nat × Nat) := #[(0, β)]
    let mut head := 0
    while head < queue.size do
      let (x, y) := queue[head]!
      head := head + 1
      for g in C.gens do
        let u := find parent g[x]!
        let v := find parent g[y]!
        if u != v then
          parent := parent.set! (max u v) (min u v)
          queue := queue.push (u, v)
    let r0 := find parent 0
    let size := (List.range d).foldl (fun c x ↦ if find parent x == r0 then c + 1 else c) 0
    if size < best then best := size
  return best

/-- Constituents up to equivalence, bucketed by their invariants. -/
structure ConstituentSet where
  /-- The pairwise inequivalent constituents. -/
  items : Array Constituent := #[]
  /-- Indices of `items` by invariant key. -/
  byKey : Std.HashMap (Array (Array Nat)) (Array Nat) := {}
  /-- Number of constituents rejected as equivalent to a stored one. -/
  duplicates : Nat := 0

namespace ConstituentSet

/-- Insert `C` unless it is equivalent to a stored constituent; returns whether it was new. -/
def insert (S : ConstituentSet) (C : Constituent) : ConstituentSet × Bool :=
  let bucket := S.byKey.getD C.key #[]
  if bucket.any (fun i ↦ S.items[i]!.equivalent C) then
    ({ S with duplicates := S.duplicates + 1 }, false)
  else
    ({ S with items := S.items.push C, byKey := S.byKey.insert C.key (bucket.push S.items.size) },
     true)

end ConstituentSet

/-- A small deterministic pseudo-random generator (SplitMix64). -/
structure Rng where
  /-- The state. -/
  s : UInt64

namespace Rng

/-- The next output and state. -/
def next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A number in `[0, k)`, `k > 0`. -/
def below (r : Rng) (k : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (x.toNat % k, r)

end Rng

/-- Product-replacement random elements of `⟨gens⟩` (Celler et al.); `count` elements after a
burn-in of `burn` steps. Only the multiplication of group elements is used, so every output lies in
the group. -/
def randomElements (D : Nat) (gens : Array Perm) (count burn : Nat) (seed : UInt64 := 1) :
    Array Perm := Id.run do
  if gens.isEmpty then return #[]
  let k := max 10 gens.size
  let mut xs : Array Perm := (Array.range k).map fun i ↦ gens[i % gens.size]!
  let mut acc := Perm.one D
  let mut rng : Rng := ⟨seed⟩
  let mut out : Array Perm := #[]
  for t in [0:burn + count] do
    let (i, r1) := rng.below k
    let (j0, r2) := r1.below (k - 1)
    rng := r2
    let j := if j0 ≥ i then j0 + 1 else j0
    xs := xs.set! i (Perm.mul xs[i]! xs[j]!)
    acc := Perm.mul acc xs[i]!
    if t ≥ burn then out := out.push acc
  return out

/-- The type of a constituent found by `structuralOrder`. -/
inductive ConstituentKind where
  /-- Contains the alternating group (Jordan witness found); `sym` if it has an odd element. -/
  | alt (sym : Bool)
  /-- Not certified alternating; handled in the quotient by Schreier–Sims. -/
  | other
  deriving Inhabited, BEq, Repr

/-- Result of `structuralOrder`. -/
structure StructuralResult where
  /-- Degrees and kinds of the pairwise inequivalent non-trivial constituents. -/
  constituents : Array (Nat × ConstituentKind)
  /-- Number of constituents dropped as equivalent to an earlier one. -/
  duplicates : Nat
  /-- Order of the quotient `G / N` (if computed). -/
  quotientOrder : Option Nat
  /-- Degrees of the big (alternating) constituents: `|G| = |G / N| · ∏ d! / 2`. -/
  bigDegrees : Array Nat := #[]
  /-- Whether every kernel witness was found, so that `|G| = |G / N| · ∏ d! / 2` holds. -/
  certified : Bool := false
  /-- The exact order of `G`, if certified and not too large to write out. -/
  order : Option Nat
  /-- For each constituent not certified alternating: degree, smallest block size (the degree if
  primitive), and its order by Schreier–Sims (if within the work limit). -/
  others : Array (Nat × Nat × Option Nat) := #[]
  /-- Why the order is undetermined, if it is. -/
  note : String
  deriving Inhabited

/-- The order of the group generated by `gens` on the disjoint union of the constituents `cs`
(each given by the restricted generators), by the method in the module docstring. -/
def structuralOrder (cs : Array Constituent) (tries : Nat := 400) (ssLimit : Nat := 20000000)
    (seed : UInt64 := 7) : StructuralResult := Id.run do
  -- 1. drop trivial and equivalent constituents
  let mut S : ConstituentSet := {}
  for C in cs do
    if C.deg ≤ 1 then continue
    S := (S.insert C).1
  let kept := S.items
  let dups := S.duplicates
  if kept.isEmpty then
    return { constituents := #[], duplicates := dups, quotientOrder := some 1, order := some 1,
             certified := true, note := "" }
  -- global labelling of the kept constituents
  let offs : Array Nat := kept.foldl (fun a C ↦ a.push (a.back! + C.deg)) #[0]
  let D := offs.back!
  let ngen := kept[0]!.gens.size
  let gens : Array Perm := (Array.range ngen).map fun k ↦ Id.run do
    let mut p : Perm := Array.emptyWithCapacity D
    for i in [0:kept.size] do
      for x in kept[i]!.gens[k]! do
        p := p.push (x + offs[i]!)
    return p
  let ptsOf (i : Nat) : Array Nat := (Array.range kept[i]!.deg).map (· + offs[i]!)
  let rand := randomElements D gens tries 30 seed
  -- 2. Jordan witnesses for the constituents of degree ≥ 9
  let mut big : Array Bool := Array.replicate kept.size false
  for i in [0:kept.size] do
    let d := kept[i]!.deg
    if d ≥ 9 then
      let mut found := false
      for w in gens ++ rand do
        if !found then
          let ls := w.cycleLengthsOn (ptsOf i)
          if ls.any (fun l ↦ 2 * l > d && l + 3 ≤ d && isPrimeNat l) then found := true
      big := big.set! i found
  -- 3. kernel witnesses
  let rPts : Array Nat := (Array.range kept.size).foldl
    (fun a i ↦ if big[i]! then a else a ++ ptsOf i) #[]
  let mut allWitnessed := true
  let mut missing : Array Nat := #[]
  for i in [0:kept.size] do
    if big[i]! then
      let mut found := false
      for w in gens ++ rand do
        if !found then
          let m := Perm.orderOfLengths (w.cycleLengthsOn rPts)
          let ls := w.cycleLengthsOn (ptsOf i)
          if ls.any (fun l ↦ m % l != 0) then found := true
      if !found then
        allWitnessed := false
        missing := missing.push kept[i]!.deg
  -- 4. the quotient G/N on the R-points plus two sign points per big constituent
  let bigIdx := (Array.range kept.size).filter (big[·]!)
  let rPos : Std.HashMap Nat Nat := (Array.range rPts.size).foldl
    (fun m j ↦ m.insert rPts[j]! j) {}
  let QD := rPts.size + 2 * bigIdx.size
  let qgens : Array Perm := gens.map fun g ↦ Id.run do
    let mut q : Perm := (g.restrict rPts rPos) ++ (Array.range (2 * bigIdx.size)).map
      (· + rPts.size)
    for t in [0:bigIdx.size] do
      if Perm.parityOfLengths (g.cycleLengthsOn (ptsOf bigIdx[t]!)) == 1 then
        let u := rPts.size + 2 * t
        q := (q.set! u (u + 1)).set! (u + 1) u
    return q
  let kinds : Array (Nat × ConstituentKind) := (Array.range kept.size).map fun i ↦
    if big[i]! then
      let odd := (gens ++ rand).any fun w ↦
        Perm.parityOfLengths (w.cycleLengthsOn (ptsOf i)) == 1
      (kept[i]!.deg, .alt odd)
    else (kept[i]!.deg, .other)
  let qo := schreierSimsOrder QD qgens ssLimit
  let bigDegrees := bigIdx.map (kept[·]!.deg)
  let order := if allWitnessed && bigDegrees.foldl (· + ·) 0 ≤ 5000 then
      qo.map (· * bigDegrees.foldl (fun a d ↦ a * (factorial d / 2)) 1)
    else none
  let note :=
    if !allWitnessed then s!"no kernel witness for big constituents of degree {missing}"
    else if qo.isNone then s!"quotient of degree {QD} beyond the Schreier–Sims work limit"
    else ""
  let others := (Array.range kept.size).filterMap fun i ↦
    if big[i]! then none else
    let C := kept[i]!
    some (C.deg, (if C.deg ≤ 3000 then C.minBlockSize else 0),
      schreierSimsOrder C.deg C.gens (ssLimit / 4))
  return { constituents := kinds, duplicates := dups, quotientOrder := qo, bigDegrees,
           certified := allWitnessed && qo.isSome, order, others, note }

/-- `log₁₀ (d! / 2)`. -/
def log10HalfFactorial (d : Nat) : Float :=
  (List.range d).foldl (fun s k ↦ s + Float.log10 (k + 1).toFloat) 0 - Float.log10 2

/-- `log₁₀` of a natural number (via its binary length for large values). -/
def log10Nat (x : Nat) : Float :=
  if x < 2 ^ 60 then Float.log10 x.toFloat
  else
    let sh := x.log2 - 52
    Float.log10 (x >>> sh).toFloat + sh.toFloat * Float.log10 2

/-- `log₁₀ |G|` for a certified result. -/
def StructuralResult.log10Order (R : StructuralResult) : Option Float :=
  if !R.certified then none else
  R.quotientOrder.map fun q ↦
    log10Nat q + R.bigDegrees.foldl (fun s d ↦ s + log10HalfFactorial d) 0

end TDCSGCompute
