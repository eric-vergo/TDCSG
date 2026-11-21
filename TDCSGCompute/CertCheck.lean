/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import Std.Data.HashMap
import TDCSGCompute.CirclePoint

/-!
# Independent checker of cut-set certificates

`checkCertificate` reads a certificate file (format in `notes/certificates.md`) and verifies from
scratch the hypotheses of the cut-set certificate theorem (Theorem 4.2 of
`notes/proofs/critical-radius-n5.md`; `TDCSG.Certificate` in
`TDCSG/CriticalRadius/Certificate.lean`) for the union `K` of the listed arcs:

* the radius: `r² = R / q` is real and `r > 1`;
* the arcs: every endpoint symbol names a point of its circle; on each circle the listed arcs are
  non-degenerate, pairwise disjoint and do not touch (so they are the maximal arcs of `K` on that
  circle); a circle is listed either as full or by arcs, not both;
* **(C1)** the circles about `-1` and `1` are listed as full;
* **(C2)** for every listed arc `α` on a circle `C(c)`, every disk centre `p ≠ c` with
  `C(c)` meeting the interior of `D_p`, and `k = ±1`: each non-degenerate part of `α ∩ D_p`
  (`α` clipped to the arc from `(p, -1)` to `(p, +1)`), rotated by `ζ^k` about `p`, lies inside a
  single listed arc of the image circle, or the image circle is full. Single-point parts of
  `α ∩ D_p` are window endpoints, on `∂D_p`, and their images lie on `∂D_p ⊆ K` by (C1). For
  `c = p` the images lie on `∂D_p`. If `C(c)` misses `D_p` there is nothing to map;
* **(C3)** `4ρ - |c - p|² ≠ 0` for every listed centre `c ≠ p`, `p = ±1`;
* **(C4)** every arc endpoint equal to `(p, -1)` is the initial point of its arc and every
  endpoint equal to `(p, +1)` is its final point, so the arc runs into `D_p` there;
* the summary line agrees with the recomputed counts.

## What is shared with the generator

Only the exact layer: `CycField` (arithmetic in `ℤ[ζ_n]` and exact signs of real elements),
`Tower` (exact signs in quadratic towers) and `CircleCtx` of `TDCSGCompute.CirclePoint` (validity
of symbols, the exact order of points on a circle, tangency signs, the rotations). Parsing,
clipping, containment and the (C1)–(C4) logic are written separately here, and **no
floating-point number enters any decision**: the generator's float filter is not used.

## Relation to the Lean statement

Each `arc` record on centre `c` corresponds to `TDCSG.Arc` with `center` the complex value of `c`,
`θ₁` the angle of the initial point about `c` and `θ₂ = θ₁ + ` the counterclockwise angle to the
final point (in `(0, 2π)`); a `full` record has `θ₂ = θ₁ + 2π`. With `r = √ρ` the checks above
are the conjuncts of `TDCSG.Certificate n r arcs`: non-degeneracy, (C1), (C2) for `permA`,
`permA⁻¹`, `permB`, `permB⁻¹` (which act as the rotations by `ζ^{∓1}` on the closed disks and as
the identity elsewhere), (C3) as `dist c p ≠ 2r`, and (C4) in the local form stated there. This
correspondence is by inspection of the definitions; it is not a formal proof.
-/

namespace TDCSGCompute

/-- One `arc` record. -/
structure CertArcRec where
  /-- The centre. -/
  c : Elem
  /-- The initial point. -/
  a : Sym
  /-- The final point. -/
  b : Sym

/-- A parsed certificate file. -/
structure ParsedCert where
  /-- The order `n`. -/
  n : Nat
  /-- The squared radius. -/
  r2 : RadiusSq
  /-- The centres of the full circles. -/
  full : Array Elem
  /-- The arcs. -/
  arcs : Array CertArcRec
  /-- The summary line `(circles, arcs, c4-endpoints)`. -/
  summary : Option (Nat × Nat × Nat)

/-- Parse a comma-separated integer vector of length `d`. -/
def parseVec (d : Nat) (s : String) : Except String Elem := do
  let parts := s.splitOn ","
  if parts.length != d then throw s!"vector {s} has length {parts.length}, expected {d}"
  let v ← parts.toArray.mapM fun t ↦
    match t.toInt? with
    | some x => pure x
    | none => throw s!"cannot parse the integer {t}"
  return v

/-- Parse a symbol from a vector and a sign word. -/
def parseSym (d : Nat) (v s : String) : Except String Sym := do
  let e ← parseVec d v
  match s with
  | "+" => return ⟨e, true⟩
  | "-" => return ⟨e, false⟩
  | _ => throw s!"bad side {s}"

/-- One line of a certificate file. -/
inductive CertLine where
  /-- A blank or comment line. -/
  | skip
  /-- `tdcsg-certificate 1`. -/
  | header
  /-- `n N`. -/
  | n (k : Nat)
  /-- `r2 v / q`. -/
  | r2 (x : RadiusSq)
  /-- `full c`. -/
  | full (c : Elem)
  /-- `arc c e₁ s₁ e₂ s₂`. -/
  | arc (A : CertArcRec)
  /-- `summary circles C arcs A c4-endpoints E`. -/
  | summary (c a e : Nat)
  /-- `end`. -/
  | stop

/-- Parse one line, given `n` if it has been read. -/
def parseLine (n : Option Nat) (line : String) : Except String CertLine := do
  let t := line.trimAscii.toString
  if t.isEmpty || t.startsWith "#" then return .skip
  let w := (t.splitOn " ").filter (!·.isEmpty)
  let dim : Except String Nat := match n with
    | some k => pure (totient k)
    | none => throw "record before n"
  match w with
  | ["tdcsg-certificate", "1"] => return .header
  | ["n", v] =>
    match v.toNat? with
    | some k => if k < 3 then throw "n must be at least 3" else return .n k
    | none => throw "bad n"
  | ["r2", v, "/", q] =>
    let num ← parseVec (← dim) v
    match q.toNat? with
    | some qq => if qq == 0 then throw "zero denominator" else return .r2 ⟨num, qq⟩
    | none => throw "bad denominator"
  | ["full", v] => return .full (← parseVec (← dim) v)
  | ["arc", v, e1, s1, e2, s2] =>
    let d ← dim
    return .arc { c := ← parseVec d v, a := ← parseSym d e1 s1, b := ← parseSym d e2 s2 }
  | ["summary", "circles", c, "arcs", a, "c4-endpoints", e] =>
    match c.toNat?, a.toNat?, e.toNat? with
    | some c, some a, some e => return .summary c a e
    | _, _, _ => throw "bad summary line"
  | ["end"] => return .stop
  | _ => throw s!"cannot parse the line: {t}"

/-- Parse a certificate from a source of lines (`next` returns `none` at the end). -/
def parseLines {m : Type → Type} [Monad m] (next : m (Option String)) :
    m (Except String ParsedCert) := do
  let mut header := false
  let mut n : Option Nat := none
  let mut r2 : Option RadiusSq := none
  let mut full : Array Elem := #[]
  let mut arcs : Array CertArcRec := #[]
  let mut summary : Option (Nat × Nat × Nat) := none
  let mut ended := false
  repeat
    let some l ← next | break
    match parseLine n l with
    | .error e => return .error e
    | .ok .skip => pure ()
    | .ok rec =>
      if ended then return .error "text after 'end'"
      match header, rec with
      | false, .header => header := true
      | false, _ => return .error "missing header 'tdcsg-certificate 1'"
      | true, .header => return .error "duplicate header"
      | true, .n k => if n.isSome then return .error "duplicate n" else n := some k
      | true, .r2 x => if r2.isSome then return .error "duplicate r2" else r2 := some x
      | true, .full c => full := full.push c
      | true, .arc A => arcs := arcs.push A
      | true, .summary c a e =>
        if summary.isSome then return .error "duplicate summary"
        summary := some (c, a, e)
      | true, .stop => ended := true
      | true, .skip => pure ()
  if !header then return .error "empty file"
  if !ended then return .error "missing 'end' (truncated file?)"
  let some k := n | return .error "missing n"
  let some r := r2 | return .error "missing r2"
  return .ok { n := k, r2 := r, full, arcs, summary }

/-- Parse a certificate given as text. -/
def parseCertificate (text : String) : Except String ParsedCert :=
  let ls := (text.splitOn "\n").toArray
  let next : StateM Nat (Option String) := do
    let i ← get
    set (i + 1)
    return ls[i]?
  (parseLines next).run' 0

/-- Parse a certificate file, line by line. -/
def parseCertificateFile (path : System.FilePath) : IO (Except String ParsedCert) := do
  let h ← IO.FS.Handle.mk path .read
  parseLines do
    let l ← h.getLine
    return if l.isEmpty then none else some l

/-- A point with its exact data. -/
structure CPt where
  /-- The symbol. -/
  sym : Sym
  /-- Exact direction data. -/
  x : CircleCtx.ExactPt
  deriving Inhabited

/-- The listed part of `K` on one circle, arcs sorted by the angle of their initial points. -/
structure CheckCircle where
  /-- Full circle. -/
  full : Bool
  /-- Sorted arcs `(initial, final)`. -/
  arcs : Array (CPt × CPt)
  /-- Signs of `4ρ - |c ∓ 1|²` (left, right). -/
  meet : Int × Int

/-- Counts recomputed by the checker. -/
structure CheckReport where
  /-- Circles. -/
  circles : Nat
  /-- Full circles. -/
  fullCircles : Nat
  /-- Maximal arcs (full circles included). -/
  arcs : Nat
  /-- Image arcs verified in (C2). -/
  c2Images : Nat
  /-- Arc endpoints on boundary circles, all passing (C4). -/
  c4Endpoints : Nat

namespace CertChecker

/-- Merge sort with a fallible comparison. -/
partial def msort {α : Type} [Inhabited α] (lt : α → α → Except String Bool) (xs : Array α) :
    Except String (Array α) := do
  if xs.size ≤ 1 then return xs
  let m := xs.size / 2
  let l ← msort lt (xs.extract 0 m)
  let r ← msort lt (xs.extract m xs.size)
  let mut out := Array.emptyWithCapacity xs.size
  let mut i := 0
  let mut j := 0
  while i < l.size || j < r.size do
    if j ≥ r.size then
      out := out.push l[i]!; i := i + 1
    else if i ≥ l.size then
      out := out.push r[j]!; j := j + 1
    else if ← lt r[j]! l[i]! then
      out := out.push r[j]!; j := j + 1
    else
      out := out.push l[i]!; i := i + 1
  return out

variable (C : CircleCtx)

/-- Order by angle (`.eq`: the same point). -/
def cmp (x y : CPt) : Except String Ordering :=
  if x.sym == y.sym then pure .eq else C.cmpExact x.x y.x

/-- Order of the counterclockwise positions of `x` and `y` measured from `s`, in `[0, 2π)`. -/
def posCmp (s x y : CPt) : Except String Ordering := do
  let wx := (← cmp C x s) == .lt
  let wy := (← cmp C y s) == .lt
  if wx != wy then return (if wx then .gt else .lt)
  cmp C x y

/-- The point named by `s` on the circle about `c`, with its exact data (validates `s`). -/
def mkPt (c : Elem) (s : Sym) : Except String CPt := do
  return { sym := s, x := ← C.exactPt c s }

/-- The non-degenerate parts of the arc `[x, y]` inside the arc `[w0, w1]` of the same circle. -/
def clip (x y w0 w1 : CPt) : Except String (Array (CPt × CPt)) := do
  -- `minEnd a` is the earlier of `a` and `y` measured from `x` (both after `x`)
  let minEnd (a : CPt) : Except String CPt := do
    return if (← posCmp C x a y) == .gt then y else a
  if (← cmp C w0 x) == .eq then
    return #[(x, ← minEnd w1)]
  if (← cmp C w1 x) == .eq then
    if (← posCmp C x w0 y) == .lt then return #[(w0, y)] else return #[]
  let mut out := #[]
  let wraps := (← posCmp C x w1 w0) == .lt
  if wraps then out := out.push (x, ← minEnd w1)
  if (← posCmp C x w0 y) == .lt then
    let e ← if wraps then pure y else minEnd w1
    out := out.push (w0, e)
  return out

/-- Whether the arc `[u, v]` lies inside the arc `[s, e]` of the same circle. -/
def inside (u v s e : CPt) : Except String Bool := do
  return (← posCmp C s u v) == .lt && (← posCmp C s v e) != .gt

/-- Whether the arc `[u, v]` lies inside one of the sorted disjoint arcs `arcs`. -/
def covered (arcs : Array (CPt × CPt)) (u v : CPt) : Except String Bool := do
  if arcs.isEmpty then return false
  -- the last arc whose initial point is at or before `u` (by angle), else the last arc
  let mut lo := 0
  let mut hi := arcs.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if (← cmp C arcs[mid]!.1 u) != .gt then lo := mid + 1 else hi := mid
  let cand := if lo == 0 then arcs.size - 1 else lo - 1
  if ← inside C u v arcs[cand]!.1 arcs[cand]!.2 then return true
  for (s, e) in arcs do
    if ← inside C u v s e then return true
  return false

end CertChecker

/-- Verify a parsed certificate; returns the recomputed counts, or the first failure. -/
def checkCertificate (P : ParsedCert) : Except String CheckReport := do
  let F := CycField.make P.n
  if !F.isReal P.r2.num then throw "r² is not real"
  let C := CircleCtx.make F P.r2
  if !(← C.radiusAboveOne) then throw "r ≤ 1: the certificate theorem needs r > 1"
  -- group the records by circle
  let mut raw : Std.HashMap Elem (Bool × Array CertArcRec) := {}
  for c in P.full do
    if raw.contains c then throw s!"circle {elemToString c} listed twice"
    raw := raw.insert c (true, #[])
  for A in P.arcs do
    match raw.get? A.c with
    | some (true, _) => throw s!"circle {elemToString A.c} is listed as full and with arcs"
    | some (false, xs) => raw := raw.insert A.c (false, xs.push A)
    | none => raw := raw.insert A.c (false, #[A])
  -- (C1)
  for p in [C.left, C.right] do
    match raw.get? p with
    | some (true, _) => pure ()
    | _ => throw s!"(C1) fails: the boundary circle about {elemToString p} is not listed as full"
  -- (C3), symbols, sorting, disjointness
  let mut circles : Std.HashMap Elem CheckCircle := {}
  let mut nArcs := 0
  for (c, (isFull, recs)) in raw.toList do
    let mL ← if c == C.left then pure 0 else C.gapSign c C.left
    let mR ← if c == C.right then pure 0 else C.gapSign c C.right
    if (c != C.left && mL == 0) || (c != C.right && mR == 0) then
      throw s!"(C3) fails: the circle about {elemToString c} is tangent to a boundary circle"
    if isFull then
      circles := circles.insert c { full := true, arcs := #[], meet := (mL, mR) }
      nArcs := nArcs + 1
      continue
    let mut pts : Array (CPt × CPt) := #[]
    for A in recs do
      let a ← CertChecker.mkPt C c A.a
      let b ← CertChecker.mkPt C c A.b
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
    circles := circles.insert c { full := false, arcs := sorted, meet := (mL, mR) }
    nArcs := nArcs + sorted.size
  -- (C2) and (C4)
  let mut nImg := 0
  let mut nC4 := 0
  for (c, cc) in circles.toList do
    for (p, meet) in [(C.left, cc.meet.1), (C.right, cc.meet.2)] do
      if c == p || meet ≤ 0 then continue
      let wm ← CertChecker.mkPt C c ⟨p, false⟩
      let wp ← CertChecker.mkPt C c ⟨p, true⟩
      let pieces ← if cc.full then pure #[(wm, wp)] else do
        let mut ps := #[]
        for (x, y) in cc.arcs do
          ps := ps ++ (← CertChecker.clip C x y wm wp)
        pure ps
      for (u, v) in pieces do
        for k in [(-1 : Int), 1] do
          let c' := C.rot p k c
          nImg := nImg + 1
          match circles.get? c' with
          | none =>
            throw s!"(C2) fails: an image lies on the circle about {elemToString c'}, \
              which carries no arc"
          | some tc =>
            if tc.full then continue
            let u' ← CertChecker.mkPt C c' (C.rotSym p k u.sym)
            let v' ← CertChecker.mkPt C c' (C.rotSym p k v.sym)
            if !(← CertChecker.covered C tc.arcs u' v') then
              throw s!"(C2) fails: the image of a part of an arc on {elemToString c} under the \
                rotation by ζ^{k} about {elemToString p} is not inside one arc of the circle \
                about {elemToString c'}"
      -- (C4)
      for (a, b) in cc.arcs do
        if (← CertChecker.cmp C a wm) == .eq then nC4 := nC4 + 1
        if (← CertChecker.cmp C b wp) == .eq then nC4 := nC4 + 1
        if (← CertChecker.cmp C a wp) == .eq || (← CertChecker.cmp C b wm) == .eq then
          throw s!"(C4) fails: an arc on {elemToString c} leaves D at its endpoint on the \
            boundary circle about {elemToString p}"
  let rep : CheckReport :=
    { circles := circles.size, fullCircles := P.full.size, arcs := nArcs, c2Images := nImg,
      c4Endpoints := nC4 }
  match P.summary with
  | none => throw "missing summary line"
  | some (cs, as, es) =>
    if cs != rep.circles || as != rep.arcs || es != rep.c4Endpoints then
      throw s!"summary line ({cs}, {as}, {es}) disagrees with the recomputed counts \
        ({rep.circles}, {rep.arcs}, {rep.c4Endpoints})"
  return rep

end TDCSGCompute
