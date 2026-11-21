/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.CertCheck

/-!
# The interval of validity of a cut-set certificate

A certificate (`TDCSGCompute.CertCheck`) names its arcs by symbols `(e, ±)`, which make sense at
every radius at which the named circles cross. `validityInterval` computes, for a certificate
accepted at `r₀² = ρ₀`, an exact `ρ₁ > ρ₀` such that the same symbolic arc set is accepted by the
checker at every `ρ ∈ [ρ₀, ρ₁)`. With the certificate theorem and group monotonicity this gives
finiteness of `GG_n(r)` for every `r² < ρ₁` from the one closure at `ρ₀`.

## Why the verdict is constant up to the first event

Every decision of `checkCertificate` is one of:

* the sign of `4ρ - |x - y|²` for two centres: whether a symbol is valid (two circles cross),
  whether a circle meets the interior of `D_p` ((C2)), tangency ((C3));
* the cyclic order, including equality, of points of one circle named by symbols: the arc
  endpoints on that circle, the clip points `(p, ±)`, and the endpoints of the images of clipped
  pieces of other circles that land on it (arcs, disjointness, clipping, containment, (C4)).

As `ρ` grows, `4ρ - |x - y|²` only grows, so a crossing pair stays crossing, and a sign changes
only at a *disk event* `ρ = |c - p|² / 4` for a circle `C(c)` of the certificate missing `D_p` at
`ρ₀`. The named points move continuously, so the cyclic order on a circle changes only when two of
its points coincide; two points `(e₁, s₁)`, `(e₂, s₂)` of `C(c)` with `e₁ ≠ e₂` coincide only at
the common point of three circles, the circumcentre `O` of `c, e₁, e₂`, at
`ρ = R² = |a|² |b|² |a - b|² / (4 (Im ā b)²)`, `a = e₁ - c`, `b = e₂ - c` (*triple event*), and
only if the sides match: `s₁ = sign(|b|² - Re ā b) · sign(Im ā b)` and
`s₂ = sign(Re ā b - |a|²) · sign(Im ā b)` (the position of `O` relative to the chords). Two
points with the same partner and opposite sides coincide only at tangency, below `ρ₀`. At the
first moment `ρ* > ρ₀` at which two points of a circle coincide, some coinciding pair is adjacent
in the cyclic order valid on `[ρ₀, ρ*)` (a point strictly between two converging points converges
with them). So it suffices to examine cyclically adjacent pairs of the order at `ρ₀`.

`ρ₁` is the least disk event and the least matching triple event of adjacent pairs that exceed
`ρ₀` (capped at nothing else: the certificate theorem is not used beyond `ρ₁`). If two adjacent
points coincide already at `ρ₀`, the interval is reported empty.
-/

namespace TDCSGCompute

/-- An event `num / den` (`den > 0` real) with its kind. -/
structure VEvent where
  /-- Numerator (real element). -/
  num : Elem
  /-- Denominator (positive real element). -/
  den : Elem
  /-- `"disk"` or `"triple"`. -/
  kind : String
  /-- The circle on which it was found. -/
  circle : Elem
  deriving Inhabited

/-- The result of the computation. -/
structure ValidityReport where
  /-- The least event above `ρ₀` (`none`: no event found). -/
  least : Option VEvent
  /-- Adjacent pairs examined. -/
  pairs : Nat
  /-- Disk events examined. -/
  diskEvents : Nat
  /-- Adjacent pairs of distinct symbols naming the same point at `ρ₀`. -/
  coincidentAtStart : Nat

namespace Validity

variable (C : CircleCtx)

/-- The exact sign of a real element. -/
def sgn (x : Elem) : Except String Int :=
  match C.S.sign x with
  | some s => .ok s
  | none => .error "sign determination failed"

/-- `x / y < x' / y'` for positive denominators. -/
def lessEv (e e' : VEvent) : Except String Bool := do
  let F := C.F
  return (← sgn C (F.sub (F.mul e.num e'.den) (F.mul e'.num e.den))) < 0

/-- `e > ρ₀`. -/
def aboveStart (e : VEvent) : Except String Bool := do
  let F := C.F
  -- num / den > R / q  ⟺  q num - R den > 0
  return (← sgn C (F.sub (F.smul (C.r2.den : Int) e.num) (F.mul C.r2.num e.den))) > 0

/-- The triple event of two points of `C(c)` with different partners, if the sides match (`none`
for collinear centres or non-matching sides). -/
def tripleEvent (c : Elem) (x y : Sym) : Except String (Option VEvent) := do
  let F := C.F
  let a := F.sub x.e c
  let b := F.sub y.e c
  let z := F.mul (F.conj a) b
  let Az := F.add z (F.conj z)
  let Tz := F.neg (F.mul (F.sub z (F.conj z)) C.omega)
  let D := F.neg (F.mul (F.sub z (F.conj z)) (F.sub z (F.conj z)))
  let sT ← sgn C Tz
  if sT == 0 then return none
  let s1 := (← sgn C (F.sub (F.smul 2 (F.normSq b)) Az)) * sT
  let s2 := (← sgn C (F.sub Az (F.smul 2 (F.normSq a)))) * sT
  if (s1 != 0 && (s1 > 0) != x.plus) || (s2 != 0 && (s2 > 0) != y.plus) then return none
  let N := F.mul (F.mul (F.normSq a) (F.normSq b)) (F.normSq (F.sub a b))
  return some { num := N, den := D, kind := "triple", circle := c }

/-- The points of `C(c)` that the checker compares: arc endpoints, clip points and the endpoints
of the images of clipped pieces of the circles mapped onto `C(c)`. -/
def symbolsOn (circles : Std.HashMap Elem CheckCircle) (c : Elem) (ck : CheckCircle) :
    Except String (Array Sym) := do
  let mut out : Array Sym := #[]
  for (a, b) in ck.arcs do
    out := (out.push a.sym).push b.sym
  for (p, meet) in [(C.left, ck.meet.1), (C.right, ck.meet.2)] do
    if c != p && meet > 0 then out := (out.push ⟨p, false⟩).push ⟨p, true⟩
  -- sources: `c = rot p k s` for `s = rot p (-k) c`
  for p in [C.left, C.right] do
    for k in [(-1 : Int), 1] do
      let s := C.rot p (-k) c
      if s == p then continue
      let some sk := circles.get? s | continue
      let meet := if p == C.left then sk.meet.1 else sk.meet.2
      if meet ≤ 0 then continue
      let wm ← CertChecker.mkPt C s ⟨p, false⟩
      let wp ← CertChecker.mkPt C s ⟨p, true⟩
      let pieces ← if sk.full then pure #[(wm, wp)] else do
        let mut ps := #[]
        for (x, y) in sk.arcs do
          ps := ps ++ (← CertChecker.clip C x y wm wp)
        pure ps
      for (u, v) in pieces do
        out := (out.push (C.rotSym p k u.sym)).push (C.rotSym p k v.sym)
  return out

/-- Examine one circle: the least matching triple event of adjacent pairs above `ρ₀`, the least
disk event, and counts. -/
def circleEvents (circles : Std.HashMap Elem CheckCircle) (c : Elem) (ck : CheckCircle) :
    Except String (Option VEvent × Nat × Nat × Nat) := do
  let F := C.F
  let mut best : Option VEvent := none
  let mut nDisk := 0
  -- disk events
  for (p, meet) in [(C.left, ck.meet.1), (C.right, ck.meet.2)] do
    if c != p && meet < 0 then
      nDisk := nDisk + 1
      let e : VEvent := { num := F.normSq (F.sub c p), den := F.ofInt 4, kind := "disk",
                          circle := c }
      if ← aboveStart C e then
        best := match best with
          | none => some e
          | some b => if (lessEv C e b).toOption == some true then some e else some b
  -- the cyclic order of the compared points
  let syms ← symbolsOn C circles c ck
  let mut uniq : Array Sym := #[]
  let mut seen : Std.HashMap Sym Unit := {}
  for s in syms do
    if !seen.contains s then
      seen := seen.insert s ()
      uniq := uniq.push s
  if uniq.size < 2 then return (best, 0, nDisk, 0)
  let mut pts : Array CPt := #[]
  for s in uniq do pts := pts.push (← CertChecker.mkPt C c s)
  let sorted ← CertChecker.msort (fun x y ↦ do return (← CertChecker.cmp C x y) == .lt) pts
  let mut nPairs := 0
  let mut nCoinc := 0
  for i in [0:sorted.size] do
    let x := sorted[i]!
    let y := sorted[(i + 1) % sorted.size]!
    if x.sym.e == y.sym.e then continue
    nPairs := nPairs + 1
    if (← CertChecker.cmp C x y) == .eq then
      nCoinc := nCoinc + 1
      continue
    if let some e ← tripleEvent C c x.sym y.sym then
      if ← aboveStart C e then
        best := match best with
          | none => some e
          | some b => if (lessEv C e b).toOption == some true then some e else some b
  return (best, nPairs, nDisk, nCoinc)

end Validity

/-- The least event above the certificate's radius (module docstring), in `threads` parallel
tasks. The certificate should first be accepted by `checkCertificate`. -/
def validityInterval (P : ParsedCert) (threads : Nat := 1) : Except String ValidityReport := do
  let F := CycField.make P.n
  let C := CircleCtx.make F P.r2
  let mut raw : Std.HashMap Elem (Bool × Array CertArcRec) := {}
  for c in P.full do raw := raw.insert c (true, #[])
  for A in P.arcs do
    match raw.get? A.c with
    | some (_, xs) => raw := raw.insert A.c (false, xs.push A)
    | none => raw := raw.insert A.c (false, #[A])
  let mut circles : Std.HashMap Elem CheckCircle := {}
  for (c, (isFull, recs)) in raw.toList do
    let mL ← if c == C.left then pure 0 else C.gapSign c C.left
    let mR ← if c == C.right then pure 0 else C.gapSign c C.right
    let mut pts : Array (CPt × CPt) := #[]
    for A in recs do
      pts := pts.push (← CertChecker.mkPt C c A.a, ← CertChecker.mkPt C c A.b)
    circles := circles.insert c { full := isFull, arcs := pts, meet := (mL, mR) }
  let items := circles.toArray
  let run (lo hi : Nat) : Except String (Option VEvent × Nat × Nat × Nat) := do
    let mut best : Option VEvent := none
    let mut np := 0
    let mut nd := 0
    let mut nc := 0
    for i in [lo:hi] do
      let some (c, ck) := items[i]? | throw "index out of range"
      let (b, p, d, k) ← Validity.circleEvents C circles c ck
      np := np + p
      nd := nd + d
      nc := nc + k
      if let some e := b then
        best := match best with
          | none => some e
          | some b0 => if (Validity.lessEv C e b0).toOption == some true then some e else some b0
    return (best, np, nd, nc)
  let parts ← if threads ≤ 1 || items.size < 1000 then pure [← run 0 items.size] else do
    let tasks := (List.range threads).map fun t ↦
      Task.spawn fun _ ↦ run (t * items.size / threads) ((t + 1) * items.size / threads)
    tasks.mapM (·.get)
  let mut best : Option VEvent := none
  let mut np := 0
  let mut nd := 0
  let mut nc := 0
  for (b, p, d, k) in parts do
    np := np + p
    nd := nd + d
    nc := nc + k
    if let some e := b then
      match best with
      | none => best := some e
      | some b0 => if ← Validity.lessEv C e b0 then best := some e
  return { least := best, pairs := np, diskEvents := nd, coincidentAtStart := nc }

end TDCSGCompute
