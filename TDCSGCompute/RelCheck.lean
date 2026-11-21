/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.CertCheck

/-!
# Independent checker of relative certificates

`checkRelative` reads a relative certificate (format in `notes/relative-certificates.md`) and
verifies from scratch the hypotheses of the relative-certificate theorem (Theorem 4.2 of
`notes/proofs/sharp-lower-bound-combined.md`, as restated in `notes/relative-certificates.md`)
for the union `K'` of the listed arcs, all of radius `r`, `r² = R / q`:

* **the critical points**: the listed points are exactly the lattice points on `∂D_L ∪ ∂D_R`,
  recomputed here (`critPoints`) from the trace-form bound;
* **the windows**: the shape `w` is non-zero with `|w| < r` (exact), and the windows
  `W_P = P + ⋂_{v ∈ {±w, ±w̄}} D(v, r)` about distinct critical points are pairwise disjoint,
  by the exact corner bound `|P - Q|² > 4 |x|²` for every corner `x` of `W₀` (`cornersOf`);
* **the arcs**: every symbol names a point of its circle; on each circle the arcs are
  non-degenerate, pairwise disjoint and do not touch; a circle is listed as full or by arcs;
* **(K1)** the circles about `-1` and `1` are full;
* **(K2)** every boundary arc of every window (on `C(P + v)`, the part inside the other disks
  `D(P + v')`) lies inside one listed arc, or its circle is full;
* **(K3)** for every listed arc `α` (or full circle) on `C(c)`, every `p = ±1` with `c ≠ p` and
  `C(c)` crossing `∂D_p`, and `k = ±1`: `α ∩ D_p` minus the open arcs `C(c) ∩ int W_P` splits
  into closed arcs; each non-degenerate one, rotated by `ζ^k` about `p`, lies inside one listed
  arc of the image circle (or the image circle is full). If `C(c)` is tangent to `∂D_p`, then
  `α ∩ D_p` is at most one point, so there is nothing to map; if `c = p`, the images lie on
  `∂D_p`, which is full;
* the summary line agrees with the recomputed counts.

These are conditions (R1), (R2) of the theorem: (K1) and (K2) are (R1); (K3) is (R2), because a
component of `α ∩ D_S ∖ int W` is a union of the closed arcs above, and `D_S` is `D_p` for
`S = A^{±1}` (`p = -1`) and `S = B^{±1}` (`p = 1`).

## What is shared

With the generator, only the exact layer: `CycField`, `Tower`, and `CircleCtx` of
`TDCSGCompute.CirclePoint` (symbols, exact order, tangency signs, `diskSign`, rotations). With
the ordinary checker, the parsing of vectors and symbols and the arc primitives of `CertChecker`
(`clip`, `covered`, `posCmp`). No floating-point number enters any decision.
-/

namespace TDCSGCompute

/-- A parsed relative certificate. -/
structure ParsedRel where
  /-- The order `n`. -/
  n : Nat
  /-- The squared radius. -/
  r2 : RadiusSq
  /-- The window shape vector. -/
  w : Elem
  /-- The listed critical points. -/
  crit : Array Elem
  /-- Full circles. -/
  full : Array Elem
  /-- The arcs, grouped by circle, in file order. -/
  arcs : Std.HashMap Elem (Array (Sym × Sym))
  /-- The summary `(circles, arcs, windows)`. -/
  summary : Option (Nat × Nat × Nat)
  /-- The optional face count. -/
  faces : Option Nat
  /-- Whether the arcs are listed on one circle per orbit of `z ↦ ±z, ±z̄` only. -/
  symmetric : Bool

/-- Parse a relative certificate from a source of lines. -/
def parseRelLines {m : Type → Type} [Monad m] (next : m (Option String)) :
    m (Except String ParsedRel) := do
  let mut header := false
  let mut n : Option Nat := none
  let mut r2 : Option RadiusSq := none
  let mut w : Option Elem := none
  let mut crit : Array Elem := #[]
  let mut full : Array Elem := #[]
  let mut arcs : Std.HashMap Elem (Array (Sym × Sym)) := {}
  let mut summary : Option (Nat × Nat × Nat) := none
  let mut faces : Option Nat := none
  let mut symmetric := false
  let mut ended := false
  repeat
    let some l ← next | break
    let t := l.trimAscii.toString
    if t.isEmpty || t.startsWith "#" then continue
    if ended then return .error "text after 'end'"
    let ws := (t.splitOn " ").filter (!·.isEmpty)
    if !header then
      if ws != ["tdcsg-relative-certificate", "1"] then
        return .error "missing header 'tdcsg-relative-certificate 1'"
      header := true
      continue
    let dim : Except String Nat := match n with
      | some k => .ok (totient k)
      | none => .error "record before n"
    match ws with
    | ["tdcsg-relative-certificate", _] => return .error "duplicate header"
    | ["n", v] =>
      if n.isSome then return .error "duplicate n"
      match v.toNat? with
      | some k => if k < 3 then return .error "n must be at least 3" else n := some k
      | none => return .error "bad n"
    | ["r2", v, "/", q] =>
      if r2.isSome then return .error "duplicate r2"
      match dim >>= fun d ↦ parseVec d v, q.toNat? with
      | .ok num, some qq =>
        if qq == 0 then return .error "zero denominator"
        r2 := some ⟨num, qq⟩
      | .error e, _ => return .error e
      | _, none => return .error "bad denominator"
    | ["window", v] =>
      if w.isSome then return .error "duplicate window"
      match dim >>= fun d ↦ parseVec d v with
      | .ok x => w := some x
      | .error e => return .error e
    | ["critical", v] =>
      match dim >>= fun d ↦ parseVec d v with
      | .ok x => crit := crit.push x
      | .error e => return .error e
    | ["full", v] =>
      match dim >>= fun d ↦ parseVec d v with
      | .ok x => full := full.push x
      | .error e => return .error e
    | ["arc", v, e1, s1, e2, s2] =>
      let r : Except String CertArcRec := do
        let d ← dim
        return { c := ← parseVec d v, a := ← parseSym d e1 s1, b := ← parseSym d e2 s2 }
      match r with
      | .ok A => arcs := arcs.alter A.c fun o ↦ some ((o.getD #[]).push (A.a, A.b))
      | .error e => return .error e
    | ["summary", "circles", c, "arcs", a, "windows", k] =>
      if summary.isSome then return .error "duplicate summary"
      match c.toNat?, a.toNat?, k.toNat? with
      | some c, some a, some k => summary := some (c, a, k)
      | _, _, _ => return .error "bad summary line"
    | ["faces", f] =>
      if faces.isSome then return .error "duplicate faces"
      match f.toNat? with
      | some f => faces := some f
      | none => return .error "bad faces line"
    | ["symmetric"] =>
      if symmetric then return .error "duplicate symmetric line"
      symmetric := true
    | ["end"] => ended := true
    | _ => return .error s!"cannot parse the line: {t}"
  if !header then return .error "empty file"
  if !ended then return .error "missing 'end' (truncated file?)"
  let some k := n | return .error "missing n"
  let some r := r2 | return .error "missing r2"
  let some ww := w | return .error "missing window"
  return .ok { n := k, r2 := r, w := ww, crit, full, arcs, summary, faces, symmetric }

/-- Parse a relative certificate given as text. -/
def parseRelative (text : String) : Except String ParsedRel :=
  let ls := (text.splitOn "\n").toArray
  let next : StateM Nat (Option String) := do
    let i ← get
    set (i + 1)
    return ls[i]?
  (parseRelLines next).run' 0

/-- Parse a relative certificate file, line by line. -/
def parseRelativeFile (path : System.FilePath) : IO (Except String ParsedRel) := do
  let h ← IO.FS.Handle.mk path .read
  parseRelLines do
    let l ← h.getLine
    return if l.isEmpty then none else some l

/-- Counts recomputed by the relative checker. -/
structure RelReport where
  /-- Circles. -/
  circles : Nat
  /-- Full circles. -/
  fullCircles : Nat
  /-- Maximal arcs (full circles included). -/
  arcs : Nat
  /-- Circles modulo `±z, ±z̄`. -/
  canonCircles : Nat
  /-- Arcs on one circle per orbit. -/
  canonArcs : Nat
  /-- Critical points (= windows). -/
  windows : Nat
  /-- Window boundary arcs verified in (K2). -/
  boundaryArcs : Nat
  /-- Image arcs verified in (K3). -/
  images : Nat
  /-- Circles tangent to a boundary circle. -/
  tangentCircles : Nat
  /-- Pairs of windows shown disjoint. -/
  windowPairs : Nat
  /-- Listed arc endpoints equal to a clip point `(p, ±)` of their circle. -/
  c4Endpoints : Nat
  /-- Those that violate (C4) (an arc leaving `D_p` at its endpoint on `∂D_p`). -/
  c4Failures : Nat

/-- The listed part of `K'` on one circle, kept compact: the arcs as symbol pairs sorted by
the angle of their initial points; exact points are recomputed when needed. -/
structure RelCircle where
  /-- Full circle. -/
  full : Bool
  /-- Sorted arcs. -/
  arcs : Array (Sym × Sym)
  /-- Signs of `4ρ - |c ∓ 1|²` (left, right). -/
  meet : Int × Int

namespace RelChecker

variable (C : CircleCtx)

/-- The four symmetries of the system as maps of `ℤ[ζ_n]`: `0` the identity, `1` `z ↦ -z`,
`2` `z ↦ z̄`, `3` `z ↦ -z̄`. -/
def sym (g : Nat) (x : Elem) : Elem :=
  match g with
  | 1 => C.F.neg x
  | 2 => C.F.conj x
  | 3 => C.F.neg (C.F.conj x)
  | _ => x

/-- The image under the symmetry `g` of the arc of the circle about `c` from `a` counterclockwise
to `b`: centre and partner centres are mapped; the reflections `2`, `3` reverse orientation, so
they exchange the endpoints and the sides. -/
def symArcOf (g : Nat) (c : Elem) (a b : Sym) : Elem × Sym × Sym :=
  let a' : Sym := ⟨sym C g a.e, a.plus⟩
  let b' : Sym := ⟨sym C g b.e, b.plus⟩
  if g ≥ 2 then (sym C g c, ⟨b'.e, !b'.plus⟩, ⟨a'.e, !a'.plus⟩) else (sym C g c, a', b')

/-- The lexicographically least image of `c` and a symmetry achieving it. -/
def canonOf (c : Elem) : Elem × Nat := Id.run do
  let mut best := (c, 0)
  for g in [1, 2, 3] do
    let y := sym C g c
    if elemLexLt y best.1 then best := (y, g)
  return best

/-- Whether the arc of the circle about `c` from `a` to `b` lies inside `K'` as listed: inside one
listed arc of its circle, or its circle is full. In the symmetric mode the arc is first moved to
the canonical circle of its orbit. -/
def coveredArc (circles : Std.HashMap Elem RelCircle) (symmetric : Bool) (c : Elem)
    (a b : Sym) : Except String Bool := do
  let (c0, a0, b0) := if symmetric then symArcOf C (canonOf C c).2 c a b else (c, a, b)
  match circles.get? c0 with
  | none => return false
  | some tc =>
    if tc.full then return true
    let arcs := tc.arcs
    if arcs.isEmpty then return false
    let u ← CertChecker.mkPt C c0 a0
    let v ← CertChecker.mkPt C c0 b0
    let pt (s : Sym) := CertChecker.mkPt C c0 s
    -- the last arc whose initial point is at or before `u` (by angle), else the last arc
    let mut lo := 0
    let mut hi := arcs.size
    while lo < hi do
      let mid := (lo + hi) / 2
      if (← CertChecker.cmp C (← pt arcs[mid]!.1) u) != .gt then lo := mid + 1 else hi := mid
    let cand := if lo == 0 then arcs.size - 1 else lo - 1
    if ← CertChecker.inside C u v (← pt arcs[cand]!.1) (← pt arcs[cand]!.2) then return true
    for (s, e) in arcs do
      if ← CertChecker.inside C u v (← pt s) (← pt e) then return true
    return false

/-- The trace of an element, as the constant coefficient of the sum of its conjugates. -/
def trace (x : Elem) : Int := Id.run do
  let F := C.F
  let mut acc := F.zero
  for k in [1:F.n] do
    if Nat.gcd k F.n == 1 then acc := F.add acc (F.galois k x)
  return acc[0]!

/-- The lattice points on `∂D_L ∪ ∂D_R`: `p + w` with `q |w|² = R`. The coefficient box comes
from `x_i² ≤ Tr(r²) (G⁻¹)_ii` for the Gram matrix `G_ij = Tr(ζ^{i-j})` of the trace form; the
diagonal of `G⁻¹` is computed by Cramer's rule with rational determinants. -/
def critPoints : Except String (Array Elem) := do
  let F := C.F
  let d := F.deg
  let T : Rat := (trace C C.r2.num : Rat) / (C.r2.den : Rat)
  let G : Array (Array Rat) := (Array.range d).map fun (i : Nat) ↦ (Array.range d).map
    fun (j : Nat) ↦ ((trace C (F.zetaPow (Int.ofNat i - Int.ofNat j)) : Int) : Rat)
  -- determinant by elimination
  let det (M : Array (Array Rat)) : Rat := Id.run do
    let m := M.size
    let mut A := M
    let mut D : Rat := 1
    for col in [0:m] do
      let mut piv : Option Nat := none
      for i in [col:m] do
        if piv.isNone && A[i]![col]! != 0 then piv := some i
      let some pr := piv | return 0
      if pr != col then
        let t := A[pr]!
        A := (A.set! pr A[col]!).set! col t
        D := -D
      let pv := A[col]![col]!
      D := D * pv
      for i in [col + 1:m] do
        let f := A[i]![col]! / pv
        if f != 0 then
          let ac := A[col]!
          A := A.set! i ((Array.range m).map fun j ↦ A[i]![j]! - f * ac[j]!)
    return D
  let dG := det G
  if dG ≤ 0 then throw "the trace form is not positive definite"
  let minor (k : Nat) : Array (Array Rat) :=
    ((G.extract 0 k) ++ (G.extract (k + 1) d)).map fun row ↦ (row.extract 0 k) ++ (row.extract (k + 1) d)
  let mut bounds : Array Int := #[]
  for k in [0:d] do
    let b2 := T * det (minor k) / dG
    let mut b : Int := 0
    while ((b + 1) * (b + 1) : Int) ≤ (b2.num / b2.den) do b := b + 1
    bounds := bounds.push b
  let total := bounds.foldl (fun acc b ↦ acc * (2 * b.toNat + 1)) 1
  if total > 100000000 then throw "critical-point search box too large"
  -- enumerate the box, coefficient by coefficient (index `t` in mixed radix)
  let mut out : Array Elem := #[]
  for t in [0:total] do
    let mut x : Array Int := #[]
    let mut rest := t
    for k in [0:d] do
      let m := 2 * bounds[k]!.toNat + 1
      x := x.push ((rest % m : Nat) - bounds[k]!)
      rest := rest / m
    if F.smul (C.r2.den : Int) (F.normSq x) == C.r2.num then
      for p in [(-1 : Int), 1] do
        let P := F.addInt x p
        if !out.contains P then out := out.push P
  return out

/-- The corners of `W₀ = ⋂ D(v, r)`: intersection points of two of the circles `C(v)` that lie in
every closed disk. -/
def cornersOf (shape : Array Elem) : Except String (Array (Elem × Sym)) := do
  let mut out := #[]
  for i in [0:shape.size] do
    for j in [0:shape.size] do
      if i == j then continue
      let v := shape[i]!
      let v' := shape[j]!
      if (← C.gapSign v v') ≤ 0 then throw "two disks of a window do not cross"
      for side in [false, true] do
        let s : Sym := ⟨v', side⟩
        let mut ok := true
        for k in [0:shape.size] do
          if k == i || k == j then continue
          if (← C.diskSign v s shape[k]! C.r2) < 0 then ok := false
        if ok then out := out.push (v, s)
  return out

/-- The least dyadic bound `m / 2¹⁶` (doubling, then bisection) exceeding `|x|` for every
corner `x`, each comparison an exact `diskSign`. -/
def radiusBound (corners : Array (Elem × Sym)) : Except String Nat := do
  let within (m : Nat) : Except String Bool := do
    let t : RadiusSq := { num := C.F.ofInt ((m * m : Nat) : Int), den := 2 ^ 32 }
    for (v, s) in corners do
      if (← C.diskSign v s C.F.zero t) ≤ 0 then return false
    return true
  let mut hi := 2 ^ 16
  while !(← within hi) do hi := 2 * hi
  let mut lo := 0
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if ← within mid then hi := mid else lo := mid
  return hi

/-- Whether `| |c - P| - r | > m / 2¹⁶`, decided by integer ball arithmetic (`false` if the balls
do not decide). Then the circle about `c` misses the window about `P`, whose points lie within
`m / 2¹⁶` of `P`. -/
def farFrom (c P : Elem) (m : Nat) : Bool :=
  let p := C.ballPrec
  let F := C.F
  match (F.realBallWith C.cosBall (F.normSq (F.sub c P))).sqrt? p,
      ((F.realBallWith C.cosBall C.r2.num).divNat C.r2.den).sqrt? p with
  | some bd, some br =>
    let t := bd.sub br
    let ρ : Ball := ⟨(m : Int) * ((2 ^ (p - 16) : Nat) : Int), 0⟩
    (t.sub ρ).sign > 0 || (t.add ρ).sign < 0
  | _, _ => false

/-- The closed arc of `C(c)` common to the closed arcs `arcs` (each shorter than `π`), or `none`
if that intersection has no interior. -/
def meetArcs (arcs : Array (CPt × CPt)) : Except String (Option (CPt × CPt)) := do
  let some (a0, b0) := arcs[0]? | return none
  let mut cur := (a0, b0)
  for i in [1:arcs.size] do
    let (a, b) := arcs[i]!
    let parts ← CertChecker.clip C cur.1 cur.2 a b
    if parts.isEmpty then return none
    if parts.size > 1 then throw "intersection of short arcs is not connected"
    cur := parts[0]!
  return some cur

/-- The closed arc `C(c) ∩ W_P` for a window with disk centres `cs`, or `none` if
`C(c) ∩ int W_P` is empty. -/
def windowPart (c : Elem) (cs : Array Elem) : Except String (Option (CPt × CPt)) := do
  let mut arcs := #[]
  for f in cs do
    if f == c then return none
    if (← C.gapSign c f) ≤ 0 then return none
    arcs := arcs.push (← CertChecker.mkPt C c ⟨f, false⟩, ← CertChecker.mkPt C c ⟨f, true⟩)
  meetArcs C arcs

/-- The closed arcs that remain of the arc `[u, v]` (shorter than `2π`) when the interiors of the
closed arcs `holes` are removed; single points are dropped. -/
def minusHoles (u v : CPt) (holes : Array (CPt × CPt)) : Except String (Array (CPt × CPt)) := do
  let mut parts : Array (CPt × CPt) := #[]
  for (a, b) in holes do
    parts := parts ++ (← CertChecker.clip C u v a b)
  -- sort by start, measured counterclockwise from `u`
  let sorted ← CertChecker.msort (fun x y ↦ do
    return (← CertChecker.posCmp C u x.1 y.1) == .lt) parts
  -- sweep: positions are measured counterclockwise from `u`, all within `[u, v]`
  let mut out := #[]
  let mut cur := u
  for (a, b) in sorted do
    if (← CertChecker.posCmp C u cur a) == .lt then out := out.push (cur, a)
    if (← CertChecker.posCmp C u cur b) == .lt then cur := b
  if (← CertChecker.posCmp C u cur v) == .lt then out := out.push (cur, v)
  return out

/-- Condition (K3) for the listed arcs (or full circle) `ck` on the circle about `c`; returns the
number of image arcs verified. -/
def checkImages (circles : Std.HashMap Elem RelCircle) (symmetric : Bool)
    (centres : Array (Array Elem)) (crit : Array Elem) (rhoNum : Nat) (c : Elem)
    (ck : RelCircle) : Except String Nat := do
  if !((c != C.left && ck.meet.1 > 0) || (c != C.right && ck.meet.2 > 0)) then return 0
  let mut own : Array (CPt × CPt) := #[]
  for (a, b) in ck.arcs do
    own := own.push (← CertChecker.mkPt C c a, ← CertChecker.mkPt C c b)
  let mut nImg := 0
  let mut holes := #[]
  for k in [0:centres.size] do
    if farFrom C c crit[k]! rhoNum then continue
    if let some h ← windowPart C c centres[k]! then holes := holes.push h
  for (p, meet) in [(C.left, ck.meet.1), (C.right, ck.meet.2)] do
    if c == p || meet ≤ 0 then continue
    let wm ← CertChecker.mkPt C c ⟨p, false⟩
    let wp ← CertChecker.mkPt C c ⟨p, true⟩
    let pieces ← if ck.full then pure #[(wm, wp)] else do
      let mut ps := #[]
      for (x, y) in own do
        ps := ps ++ (← CertChecker.clip C x y wm wp)
      pure ps
    for (u, v) in pieces do
      let rems ← if holes.isEmpty then pure #[(u, v)] else minusHoles C u v holes
      for (u1, v1) in rems do
        for k in [(-1 : Int), 1] do
          let c' := C.rot p k c
          nImg := nImg + 1
          if !(← coveredArc C circles symmetric c' (C.rotSym p k u1.sym) (C.rotSym p k v1.sym))
          then
            throw s!"(K3) fails: the image of a part of an arc on {elemToString c} under \
              the rotation by ζ^{k} about {elemToString p} is not inside one arc of the \
              circle about {elemToString c'}"
  return nImg

end RelChecker

/-- Verify a parsed relative certificate; returns the recomputed counts or the first failure. -/
def checkRelative (P : ParsedRel) (threads : Nat := 1) : Except String RelReport := do
  let F := CycField.make P.n
  if !F.isReal P.r2.num then throw "r² is not real"
  let C := CircleCtx.make F P.r2
  -- critical points
  let crit ← RelChecker.critPoints C
  for x in P.crit do
    if !crit.contains x then throw s!"{elemToString x} is listed as critical but is not a \
      lattice point on a boundary circle"
  for x in crit do
    if !P.crit.contains x then throw s!"the critical point {elemToString x} is not listed"
  if P.crit.size != crit.size then throw "a critical point is listed twice"
  -- the window shape (`w = 0`: no windows, `W = ∅`)
  let active := !F.isZero P.w
  let mut shape : Array Elem := #[]
  let mut pairs := 0
  let mut rhoNum := 0
  if active then
    match C.S.sign (F.sub C.r2.num (F.smul (C.r2.den : Int) (F.normSq P.w))) with
    | some s => if s ≤ 0 then throw "the window shape needs |w| < r"
    | none => throw "sign determination failed"
    let wc := F.conj P.w
    for v in [P.w, F.neg P.w, wc, F.neg wc] do
      if !shape.contains v then shape := shape.push v
    let corners ← RelChecker.cornersOf C shape
    if corners.isEmpty then throw "the window has no corners"
    for i in [0:crit.size] do
      for j in [i + 1:crit.size] do
        pairs := pairs + 1
        let t : RadiusSq := { num := F.normSq (F.sub crit[i]! crit[j]!), den := 4 }
        for (v, s) in corners do
          if (← C.diskSign v s F.zero t) ≤ 0 then
            throw s!"the windows about {elemToString crit[i]!} and {elemToString crit[j]!} \
              are not shown to be disjoint"
    rhoNum ← RelChecker.radiusBound C corners
  let centres : Array (Array Elem) := if active then crit.map fun Q ↦ shape.map (F.add Q ·)
    else #[]
  -- group the records by circle
  let mut raw : Std.HashMap Elem (Bool × Array (Sym × Sym)) := {}
  for c in P.full do
    if raw.contains c then throw s!"circle {elemToString c} listed twice"
    raw := raw.insert c (true, #[])
  for (c, xs) in P.arcs.toList do
    if raw.contains c then throw s!"circle {elemToString c} is listed as full and with arcs"
    raw := raw.insert c (false, xs)
  -- (K1); in the symmetric mode only canonical circles may be listed, and `-1` stands for `±1`
  for p in (if P.symmetric then [C.left] else [C.left, C.right]) do
    match raw.get? p with
    | some (true, _) => pure ()
    | _ => throw s!"(K1) fails: the boundary circle about {elemToString p} is not full"
  if P.symmetric then
    for (c, _) in raw.toList do
      if (RelChecker.canonOf C c).1 != c then
        throw s!"the circle about {elemToString c} is not the canonical one of its orbit"
  -- symbols, sorting, disjointness
  let mut circles : Std.HashMap Elem RelCircle := {}
  let mut nArcs := 0
  let mut nC4 := 0
  let mut nC4bad := 0
  let mut nCirc := 0
  let mut nListedArcs := 0
  let mut nTan := 0
  let mut cc := 0
  let mut ca := 0
  for (c, (isFull, recs)) in raw.toList do
    let mL ← if c == C.left then pure 0 else C.gapSign c C.left
    let mR ← if c == C.right then pure 0 else C.gapSign c C.right
    if (c != C.left && mL == 0) || (c != C.right && mR == 0) then nTan := nTan + 1
    let cw := F.conj c
    let canon := [c, F.neg c, cw, F.neg cw].all fun y ↦ y == c || !elemLexLt y c
    -- the number of circles of `K'` this record stands for
    let stab := ([0, 1, 2, 3].filter fun g ↦ RelChecker.sym C g c == c).length
    let orbit := if P.symmetric then 4 / stab else 1
    nCirc := nCirc + orbit
    if isFull then
      circles := circles.insert c { full := true, arcs := #[], meet := (mL, mR) }
      nArcs := nArcs + orbit
      if canon then
        cc := cc + 1
        ca := ca + 1
      continue
    let mut pts : Array (CPt × CPt) := #[]
    for (sa, sb) in recs do
      let a ← CertChecker.mkPt C c sa
      let b ← CertChecker.mkPt C c sb
      if (← CertChecker.cmp C a b) == .eq then
        throw s!"degenerate arc (initial point = final point) on {elemToString c}"
      pts := pts.push (a, b)
    let sorted ← CertChecker.msort (fun x y ↦ do return (← CertChecker.cmp C x.1 y.1) == .lt) pts
    if sorted.size ≥ 2 then
      for i in [0:sorted.size] do
        let (s, e) := sorted[i]!
        let s' := sorted[(i + 1) % sorted.size]!.1
        if (← CertChecker.posCmp C s e s') != .lt then
          throw s!"arcs overlap or touch on the circle about {elemToString c}"
    circles := circles.insert c
      { full := false, arcs := sorted.map fun (a, b) ↦ (a.sym, b.sym), meet := (mL, mR) }
    -- in the symmetric mode, the arcs listed on a circle are invariant under its stabiliser
    if P.symmetric then
      for g in [1, 2, 3] do
        if RelChecker.sym C g c != c then continue
        for (u, v) in sorted do
          let (_, a', b') := RelChecker.symArcOf C g c u.sym v.sym
          if !(← CertChecker.covered C sorted (← CertChecker.mkPt C c a')
              (← CertChecker.mkPt C c b')) then
            throw s!"the arcs on {elemToString c} are not invariant under its stabiliser"
    -- (C4) counts: an endpoint equal to `(p, -)` must start its arc, one equal to `(p, +)` end it
    for (p, meet) in [(C.left, mL), (C.right, mR)] do
      if c == p || meet ≤ 0 then continue
      let wm ← CertChecker.mkPt C c ⟨p, false⟩
      let wp ← CertChecker.mkPt C c ⟨p, true⟩
      for (a, b) in sorted do
        if (← CertChecker.cmp C a wm) == .eq then nC4 := nC4 + 1
        if (← CertChecker.cmp C b wp) == .eq then nC4 := nC4 + 1
        if (← CertChecker.cmp C a wp) == .eq then nC4bad := nC4bad + 1
        if (← CertChecker.cmp C b wm) == .eq then nC4bad := nC4bad + 1
    nArcs := nArcs + orbit * sorted.size
    nListedArcs := nListedArcs + sorted.size
    if canon then
      cc := cc + 1
      ca := ca + sorted.size
  -- (K2): the window boundary arcs
  let mut nBd := 0
  for cs in centres do
    for i in [0:cs.size] do
      let f := cs[i]!
      let mut arcs := #[]
      for j in [0:cs.size] do
        if j != i then
          arcs := arcs.push (← CertChecker.mkPt C f ⟨cs[j]!, false⟩,
            ← CertChecker.mkPt C f ⟨cs[j]!, true⟩)
      match ← RelChecker.meetArcs C arcs with
      | none => pure ()
      | some (u, v) =>
        nBd := nBd + 1
        if !(← RelChecker.coveredArc C circles P.symmetric f u.sym v.sym) then
          throw s!"(K2) fails: a boundary arc of the window on {elemToString f} is not covered"
  -- (K3), circle by circle, in `threads` parallel tasks over a shared immutable store
  let items := circles.toArray
  let k3 (lo hi : Nat) : Except String Nat := do
    let mut nImg := 0
    for i in [lo:hi] do
      let some (c, ck) := items[i]? | throw "index out of range"
      nImg := nImg + (← RelChecker.checkImages C circles P.symmetric centres crit rhoNum c ck)
    return nImg
  let mut nImg := 0
  if threads ≤ 1 || items.size < 1000 then
    nImg ← k3 0 items.size
  else
    let tasks := (List.range threads).map fun t ↦
      Task.spawn fun _ ↦ k3 (t * items.size / threads) ((t + 1) * items.size / threads)
    for t in tasks do nImg := nImg + (← t.get)
  let rep : RelReport :=
    { circles := nCirc, fullCircles := P.full.size, arcs := nArcs, canonCircles := cc,
      canonArcs := ca, windows := crit.size, boundaryArcs := nBd, images := nImg,
      tangentCircles := nTan, windowPairs := pairs, c4Endpoints := nC4, c4Failures := nC4bad }
  match P.summary with
  | none => throw "missing summary line"
  | some (cs, as, ws) =>
    let listedArcs := nListedArcs + P.full.size
    if cs != circles.size || as != listedArcs || ws != rep.windows then
      throw s!"summary line ({cs}, {as}, {ws}) disagrees with the recomputed counts \
        ({circles.size}, {listedArcs}, {rep.windows})"
  return rep

end TDCSGCompute
