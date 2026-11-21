/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import Std.Data.HashMap
import TDCSGCompute.CircleFilter

/-!
# The cut set `K(r)` and its export as a finiteness certificate

`closure` computes the *cut set* `K(r)`: the smallest union of circular arcs that contains the two
boundary circles `∂D_L`, `∂D_R` (centres `-1`, `1`, radius `r`) and is mapped into itself by
`A^{±1}` on `D_L` and `B^{±1}` on `D_R`, where `A`, `B` are the rotations by `ζ` about `-1` and
`1`. When it terminates and the hypotheses hold, the resulting finite union of arcs is a
certificate for the finiteness of `GG_n(r)`: conditions (C1)–(C4) of Theorem 4.2 of
`notes/proofs/critical-radius-n5.md` (the Lean statement is `TDCSG.Certificate` in
`TDCSG/CriticalRadius/Certificate.lean`). The certificate is checked again, independently, by
`TDCSGCompute.CertCheck`.

## Algorithm

All circles have radius `r`; a circle is its centre `c ∈ ℤ[ζ_n]`. An arc is a pair of endpoint
symbols (`TDCSGCompute.CirclePoint`), run through counterclockwise; the boundary circles are
*full*. The store holds, for every circle met, either *full* or a list of pairwise disjoint,
non-touching arcs (the maximal arcs found so far).

1. Start with the two full boundary circles and put them on the work list.
2. Take a piece `α` on circle `c` from the work list. For `p ∈ {-1, 1}`, `p ≠ c`: decide exactly
   whether `C(c)` meets the interior of `D_p` (`4ρ - |c - p|² > 0`); stop with *tangency* if it is
   `0`. If it does, clip `α` (or, if `α` is full, the whole circle) to the window arc from
   `(p, -1)` to `(p, +1)`, which is `C(c) ∩ D_p`. Single-point intersections are dropped: they lie
   on `∂D_p`, whose image is `∂D_p ⊆ K`. Rotate each piece by `ζ` and by `ζ⁻¹` about `p`.
   (For `c = p` nothing is to be done: the image of a part of `∂D_p` lies on `∂D_p`.)
3. Insert each image arc into the store: compute the parts not yet covered by the arcs on its
   circle, put them on the work list, and merge them with the arcs they touch (a circle covered
   completely becomes full).
4. Stop when the work list is empty (*closed*), or when a cap on pieces, circles or time is
   reached (*cap*: nothing is claimed).

When the run closes, every stored arc has had its four clipped images inserted, so the stored set
`K` satisfies (C1) and (C2) by construction; tangency was excluded for every circle carrying an
arc, which is (C3); (C4) is then checked on the maximal arcs: an endpoint equal to `(p, -1)` must
be the start of its arc and one equal to `(p, +1)` its end, so that the arc runs into `D_p`.

## Decisions

Every order and equality decision between points of a circle is certified: first the
floating-point filter of `TDCSGCompute.CircleFilter` (rigorous error bounds), and the exact
comparison `CircleCtx.cmpExact` whenever the filter cannot decide. Two points are equal only when
the exact comparison says so, or when their symbols are identical. Equal points named by different
symbols (a triple point) are handled like any other equality and counted in `Stats.coincidences`.
Positions along an arc are compared relative to its start point, as explained at `LPos`.
-/

namespace TDCSGCompute

/-- A point of a circle with its certified half and filter data. -/
structure GPt where
  /-- The symbol. -/
  sym : Sym
  /-- The filtered direction vector. -/
  pf : PointF
  /-- Whether the point is in the lower half (certified). -/
  lower : Bool
  deriving Inhabited

/-- An arc from `a` counterclockwise to `b` (distinct points). -/
structure GArc where
  /-- The initial point. -/
  a : GPt
  /-- The final point. -/
  b : GPt
  deriving Inhabited

/-- The stored part of `K` on one circle. -/
structure CircSt where
  /-- Whether the whole circle is in `K`. -/
  full : Bool := false
  /-- The maximal arcs (if not full). -/
  arcs : Array GArc := #[]
  /-- Sign of `4ρ - |c + 1|²` (whether the circle meets the interior of `D_L`). -/
  meetL : Int := 0
  /-- Sign of `4ρ - |c - 1|²`. -/
  meetR : Int := 0
  deriving Inhabited

/-- Counters of a run. -/
structure Stats where
  /-- Halves decided exactly. -/
  exactHalves : Nat := 0
  /-- Cross products decided exactly. -/
  exactCross : Nat := 0
  /-- Equalities of points named by different symbols. -/
  coincidences : Nat := 0
  /-- Pieces put on the work list (including the two boundary circles). -/
  pieces : Nat := 0
  /-- Image arcs inserted. -/
  images : Nat := 0
  deriving Inhabited

/-- The generator's context. -/
structure Gen where
  /-- The filter (and exact) data of the radius. -/
  FC : FilterCtx
  /-- The counters. -/
  stats : IO.Ref Stats

namespace Gen

variable (G : Gen)

/-- The exact data of the radius. -/
def C : CircleCtx := G.FC.C

/-- Lift an exact computation into `IO`. -/
def liftE {α : Type} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError e

/-- The point named by `s` on the circle about `c`, with its certified half. -/
def mkPt (c : Elem) (s : Sym) : IO GPt := do
  let pf := G.FC.point c s
  match pf.lower? with
  | some l => return { sym := s, pf, lower := l }
  | none =>
    G.stats.modify fun st ↦ { st with exactHalves := st.exactHalves + 1 }
    let ep ← liftE (G.C.exactPt c s)
    return { sym := s, pf, lower := ep.lower }

/-- Certified order by angle of two points of the circle about `c`; `.eq` means the same point. -/
def cmp (c : Elem) (x y : GPt) : IO Ordering := do
  if x.sym == y.sym then return .eq
  if x.lower != y.lower then return (if x.lower then .gt else .lt)
  match x.pf.cross? y.pf with
  | some s => return (if s > 0 then .lt else .gt)
  | none =>
    let ex ← liftE (G.C.exactPt c x.sym)
    let ey ← liftE (G.C.exactPt c y.sym)
    let o ← liftE (G.C.cmpExact ex ey)
    G.stats.modify fun st ↦
      { st with exactCross := st.exactCross + 1,
                coincidences := st.coincidences + (if o == .eq then 1 else 0) }
    return o

end Gen

/-- A position on an arc of the circle about `c`, measured counterclockwise from a base point
`s` and *lifted* to `[0, 2π]`: `zero` is `s` itself at the start, `top` is `s` reached again after
a full turn, and `pt p w` is a point `p ≠ s`, with `w` telling whether its angle is below that of
`s` (so that its lifted position is its angle minus that of `s`, plus `2π` if `w`). Lifted
positions of points `≠ s` are ordered by `w` first and then by angle. -/
inductive LPos where
  /-- The base point, at the start. -/
  | zero
  /-- A point other than the base point. -/
  | pt (p : GPt) (w : Bool)
  /-- The base point after a full turn. -/
  | top
  deriving Inhabited

namespace Gen

variable (G : Gen)

/-- The lifted position of `p` relative to the base `s`, as a start (`zero` if `p = s`) or as an
end (`top` if `p = s`). -/
def lift (c : Elem) (s p : GPt) (asEnd : Bool) : IO LPos := do
  let o ← G.cmp c p s
  if o == .eq then return (if asEnd then .top else .zero)
  return .pt p (o == .lt)

/-- Compare lifted positions. -/
def cmpL (c : Elem) : LPos → LPos → IO Ordering
  | .zero, .zero => pure .eq
  | .zero, _ => pure .lt
  | _, .zero => pure .gt
  | .top, .top => pure .eq
  | .top, _ => pure .gt
  | _, .top => pure .lt
  | .pt p w, .pt q w' =>
    if w != w' then pure (if w then .gt else .lt) else G.cmp c p q

/-- The point at a lifted position (`zero` and `top` are the base point). -/
def LPos.point (s : GPt) : LPos → GPt
  | .pt p _ => p
  | _ => s

/-- The lifted intervals of the arc `B` relative to the base `s` (one, or two if `B` passes
through `s` in its interior). -/
def liftArc (c : Elem) (s : GPt) (B : GArc) : IO (Array (LPos × LPos)) := do
  let lo ← G.lift c s B.a false
  let hi ← G.lift c s B.b true
  match lo, hi with
  | .pt _ _, .pt _ _ =>
    if (← G.cmpL c hi lo) == .lt then return #[(.zero, hi), (lo, .top)]
    return #[(lo, hi)]
  | _, _ => return #[(lo, hi)]

/-- The non-degenerate parts of the lifted interval `[0, E]` covered by `B`, relative to `s`. -/
def coverBy (c : Elem) (s : GPt) (E : LPos) (B : GArc) : IO (Array (LPos × LPos)) := do
  let mut out := #[]
  for (lo, hi) in ← G.liftArc c s B do
    let hi' := if (← G.cmpL c hi E) == .gt then E else hi
    if (← G.cmpL c lo hi') == .lt then out := out.push (lo, hi')
  return out

/-- Insertion sort of lifted intervals by their lower ends. -/
def sortIntervals (c : Elem) (xs : Array (LPos × LPos)) : IO (Array (LPos × LPos)) := do
  let mut out : Array (LPos × LPos) := #[]
  for x in xs do
    let mut i := out.size
    while i > 0 do
      if (← G.cmpL c x.1 out[i - 1]!.1) != .lt then break
      i := i - 1
    out := out.insertIdxIfInBounds i x
  return out

/-- The parts of the arc `X` on the circle about `c` that lie in the closed arc `W`, as arcs;
single points are dropped. -/
def clip (c : Elem) (X W : GArc) : IO (Array GArc) := do
  let s := X.a
  let E ← G.lift c s X.b true
  let parts ← G.coverBy c s E W
  return parts.map fun (lo, hi) ↦ { a := LPos.point s lo, b := LPos.point s hi }

/-- The parts of the (non-full) arc `X` not covered by the arcs `arcs` of the same circle. -/
def uncovered (c : Elem) (X : GArc) (arcs : Array GArc) : IO (Array GArc) := do
  let s := X.a
  let E ← G.lift c s X.b true
  let mut cov := #[]
  for B in arcs do
    cov := cov ++ (← G.coverBy c s E B)
  cov ← G.sortIntervals c cov
  let mut gaps : Array GArc := #[]
  let mut pos : LPos := .zero
  for (lo, hi) in cov do
    if (← G.cmpL c pos lo) == .lt then
      gaps := gaps.push { a := LPos.point s pos, b := LPos.point s lo }
    if (← G.cmpL c pos hi) == .lt then pos := hi
  if (← G.cmpL c pos E) == .lt then
    gaps := gaps.push { a := LPos.point s pos, b := LPos.point s E }
  return gaps

/-- Merge a new arc, disjoint from the stored ones except at its endpoints, into a circle's
arcs; returns the new state (full if the circle is now covered). -/
def mergeArc (c : Elem) (st : CircSt) (g : GArc) : IO CircSt := do
  let mut before : Option Nat := none
  let mut after : Option Nat := none
  for i in [0:st.arcs.size] do
    let B := st.arcs[i]!
    if before.isNone then
      if (← G.cmp c B.b g.a) == .eq then before := some i
    if after.isNone then
      if (← G.cmp c B.a g.b) == .eq then after := some i
  match before, after with
  | some i, some j =>
    if i == j then return { st with full := true, arcs := #[] }
    let na : GArc := { a := st.arcs[i]!.a, b := st.arcs[j]!.b }
    let mut rest : Array GArc := #[]
    for k in [0:st.arcs.size] do
      if k != i && k != j then rest := rest.push st.arcs[k]!
    if (← G.cmp c na.a na.b) == .eq then return { st with full := true, arcs := #[] }
    return { st with arcs := rest.push na }
  | some i, none =>
    let na : GArc := { a := st.arcs[i]!.a, b := g.b }
    if (← G.cmp c na.a na.b) == .eq then return { st with full := true, arcs := #[] }
    return { st with arcs := st.arcs.set! i na }
  | none, some j =>
    let na : GArc := { a := g.a, b := st.arcs[j]!.b }
    if (← G.cmp c na.a na.b) == .eq then return { st with full := true, arcs := #[] }
    return { st with arcs := st.arcs.set! j na }
  | none, none => return { st with arcs := st.arcs.push g }

end Gen

/-- Limits of a run. -/
structure CloseOptions where
  /-- Maximal number of pieces. -/
  maxPieces : Nat := 10000000
  /-- Maximal number of circles. -/
  maxCircles : Nat := 5000000
  /-- Maximal run time in seconds (`0`: none). -/
  maxSeconds : Nat := 0
  /-- Print progress every this many processed pieces (`0`: never). -/
  progress : Nat := 0

/-- How a run ended. -/
inductive CloseStatus where
  /-- The closure terminated. -/
  | closed
  /-- A cap was reached; nothing is claimed. -/
  | cap (what : String)
  /-- A carrying circle is tangent to a boundary circle: (C3) fails, no certificate. -/
  | tangency (c p : Elem)
  /-- The radius violates `r > 1`. -/
  | smallRadius
  deriving Inhabited

/-- The result of a run. -/
structure CloseResult where
  /-- How it ended. -/
  status : CloseStatus
  /-- The store (the cut set if closed). -/
  store : Std.HashMap Elem CircSt
  /-- Counters. -/
  stats : Stats
  /-- Run time in milliseconds. -/
  millis : Nat

namespace Gen

variable (G : Gen)

/-- The state of a circle seen for the first time (its relation to the two disks decided
exactly), or `none` if it is tangent to a boundary circle (then `p` is reported). -/
def newCircle (c : Elem) : IO (Except Elem CircSt) := do
  let C := G.C
  let mL ← if c == C.left then pure 0 else liftE (C.gapSign c C.left)
  if c != C.left && mL == 0 then return .error C.left
  let mR ← if c == C.right then pure 0 else liftE (C.gapSign c C.right)
  if c != C.right && mR == 0 then return .error C.right
  return .ok { meetL := mL, meetR := mR }

end Gen

/-- Compute the cut set `K(r)` for the field and radius of `G` (see the module docstring). -/
def closure (G : Gen) (opts : CloseOptions) : IO CloseResult := do
  let t0 ← IO.monoMsNow
  let C := G.C
  let finish (status : CloseStatus) (store : Std.HashMap Elem CircSt) : IO CloseResult := do
    return { status, store, stats := ← G.stats.get, millis := (← IO.monoMsNow) - t0 }
  if !(← Gen.liftE C.radiusAboveOne) then return ← finish .smallRadius {}
  let mut store : Std.HashMap Elem CircSt := {}
  for p in [C.left, C.right] do
    match ← G.newCircle p with
    | .ok st => store := store.insert p { st with full := true }
    | .error q => return ← finish (.tangency p q) store
  -- the work list holds pieces; `none` is a full circle
  let mut work : Array (Elem × Option GArc) := #[(C.left, none), (C.right, none)]
  G.stats.modify fun st ↦ { st with pieces := 2 }
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
      return ← finish (.cap "time") store
    let stc := store.getD c {}
    for (p, meet) in [(C.left, stc.meetL), (C.right, stc.meetR)] do
      if c == p || meet ≤ 0 then continue
      let W : GArc := { a := ← G.mkPt c ⟨p, false⟩, b := ← G.mkPt c ⟨p, true⟩ }
      let pieces ← match α with
        | none => pure #[W]
        | some X => G.clip c X W
      for piece in pieces do
        for k in [(-1 : Int), 1] do
          let c' := C.rot p k c
          let sa := C.rotSym p k piece.a.sym
          let sb := C.rotSym p k piece.b.sym
          G.stats.modify fun st ↦ { st with images := st.images + 1 }
          let st ← match store.get? c' with
            | some st => pure st
            | none =>
              match ← G.newCircle c' with
              | .ok st => pure st
              | .error q => return ← finish (.tangency c' q) store
          if st.full then
            if !store.contains c' then store := store.insert c' st
            continue
          let X : GArc := { a := ← G.mkPt c' sa, b := ← G.mkPt c' sb }
          let gaps ← G.uncovered c' X st.arcs
          let mut st := st
          for g in gaps do
            st ← G.mergeArc c' st g
            work := work.push (c', some g)
          store := store.insert c' st
          if !gaps.isEmpty then
            G.stats.modify fun s ↦ { s with pieces := s.pieces + gaps.size }
          if (← G.stats.get).pieces > opts.maxPieces then
            return ← finish (.cap "pieces") store
          if store.size > opts.maxCircles then
            return ← finish (.cap "circles") store
  finish .closed store

/-- The summary of a closed run, from the generator's own post-check. -/
structure CertSummary where
  /-- Number of circles. -/
  circles : Nat
  /-- Number of full circles. -/
  fullCircles : Nat
  /-- Number of maximal arcs (full circles included). -/
  arcs : Nat
  /-- Maximal-arc endpoints lying on a boundary circle. -/
  c4Endpoints : Nat
  /-- Those violating (C4). -/
  c4Failures : Nat
  /-- The largest `|σ_k(c)|` over the circle centres, for each non-identity embedding `k`. -/
  maxConj : Array (Nat × Float)

/-- Check (C4) on the stored maximal arcs and collect the counts. -/
def summarize (G : Gen) (store : Std.HashMap Elem CircSt) : IO CertSummary := do
  let C := G.C
  let F := C.F
  let mut arcs := 0
  let mut full := 0
  let mut onb := 0
  let mut bad := 0
  let ks := F.embeddings.filter (· != 1)
  let mut mx : Array Float := ks.map fun _ ↦ 0
  for (c, st) in store.toList do
    for i in [0:ks.size] do
      let (x, y) := F.evalConjF ks[i]! c
      mx := mx.set! i (max mx[i]! (Float.sqrt (x * x + y * y)))
    if st.full then
      full := full + 1
      arcs := arcs + 1
      continue
    arcs := arcs + st.arcs.size
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
  return { circles := store.size, fullCircles := full, arcs, c4Endpoints := onb,
           c4Failures := bad, maxConj := ks.zip mx }

/-- Insertion sort in `IO` with a three-way comparison (lists per circle are short). -/
def sortArcsM (cmp : GArc → GArc → IO Ordering) (xs : Array GArc) : IO (Array GArc) := do
  let mut out : Array GArc := #[]
  for x in xs do
    let mut i := out.size
    while i > 0 do
      if (← cmp x out[i - 1]!) != .lt then break
      i := i - 1
    out := out.insertIdxIfInBounds i x
  return out

/-- The certificate file (format in `notes/certificates.md`): header, one line per maximal arc
(circles in lexicographic order of their centres, arcs by angle of their initial point), and the
summary line. -/
def certificateText (G : Gen) (store : Std.HashMap Elem CircSt) (S : CertSummary)
    (comment : Array String := #[]) : IO String := do
  let C := G.C
  let sym (s : Sym) : String := s!"{elemToString s.e} {if s.plus then "+" else "-"}"
  let mut out := "tdcsg-certificate 1\n"
  for l in comment do out := out ++ s!"# {l}\n"
  out := out ++ s!"n {C.F.n}\n"
  out := out ++ s!"r2 {elemToString C.r2.num} / {C.r2.den}\n"
  let centres := (store.toList.map (·.1)).toArray.qsort elemLexLt
  for c in centres do
    let st := store.getD c {}
    if st.full then
      out := out ++ s!"full {elemToString c}\n"
      continue
    let arcs ← sortArcsM (fun x y ↦ G.cmp c x.a y.a) st.arcs
    for A in arcs do
      out := out ++ s!"arc {elemToString c} {sym A.a.sym} {sym A.b.sym}\n"
  out := out ++ s!"summary circles {S.circles} arcs {S.arcs} c4-endpoints {S.c4Endpoints}\n"
  out := out ++ "end\n"
  return out

/-- The outcome of `certify`. -/
structure CertifyOutcome where
  /-- The closure run. -/
  result : CloseResult
  /-- The post-check counts (if the run closed). -/
  summary : Option CertSummary
  /-- The certificate text (if certified). -/
  text : Option String
  /-- Why there is no certificate (empty if certified). -/
  reason : String

/-- Whether a certificate was produced. -/
def CertifyOutcome.certified (o : CertifyOutcome) : Bool := o.text.isSome

/-- Compute the cut set at `r² = r2` and, if the run closes without tangency and (C4) holds,
produce the certificate text. -/
def certify (F : CycField) (r2 : RadiusSq) (opts : CloseOptions)
    (comment : Array String := #[]) : IO CertifyOutcome := do
  let G : Gen := { FC := FilterCtx.make (CircleCtx.make F r2), stats := ← IO.mkRef {} }
  let res ← closure G opts
  let pr (x : Elem) := elemToString x
  match res.status with
  | .smallRadius => return { result := res, summary := none, text := none,
                             reason := "r ≤ 1 (the certificate theorem needs r > 1)" }
  | .cap what => return { result := res, summary := none, text := none,
                          reason := s!"cap reached ({what}); nothing is claimed" }
  | .tangency c p =>
    let reason := s!"tangency: the circle about {pr c} is tangent to the boundary circle \
      about {pr p}, so (C3) fails"
    return { result := res, summary := none, text := none, reason }
  | .closed =>
    let S ← summarize G res.store
    if S.c4Failures > 0 then
      return { result := res, summary := some S, text := none,
               reason := s!"(C4) fails at {S.c4Failures} endpoints" }
    let text ← certificateText G res.store S comment
    return { result := res, summary := some S, text := some text, reason := "" }

end TDCSGCompute
