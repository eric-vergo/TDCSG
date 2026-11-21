/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.SelfTest

/-!
# `tdcsg-orbit`: command-line interface of the exact orbit engine

```
tdcsg-orbit orbit -n N (--r2 SPEC | --r Q) [--start P] [--cap C] [--threads T] [--no-conj]
                       [--width W] [--format text|lines]
tdcsg-orbit thresholds -n N [--start P] [--cap C] [--upto SPEC] [--from SPEC] [--rc SPEC]
                       [--unit SPEC] [--max-steps K] [--format text|lines]
tdcsg-orbit info -n N
tdcsg-orbit --selftest
```

The grammar of `SPEC` (exact elements of `ℚ(ζ_n)⁺`) and `P` (points of `ℤ[ζ_n]`) is in
`TDCSGCompute.Spec`. With `--format lines` every output line is a tab-separated record whose first
field names its kind.
-/

open TDCSGCompute

/-- Parsed command line: positional words and `--key value` options. -/
structure Args where
  /-- Positional arguments. -/
  pos : Array String := #[]
  /-- Options with values. -/
  opts : Array (String × String) := #[]
  /-- Flags without values. -/
  flags : Array String := #[]

/-- Options that take no value. -/
def flagNames : List String := ["--no-conj", "--selftest", "--help"]

/-- Split the command line. -/
def parseArgs (xs : List String) : Args := Id.run do
  let mut a : Args := {}
  let mut rest := xs
  while !rest.isEmpty do
    match rest with
    | x :: tl =>
      if flagNames.contains x then
        a := { a with flags := a.flags.push x }; rest := tl
      else if x.startsWith "-" && !(parseRat x).isSome then
        match tl with
        | v :: tl' => a := { a with opts := a.opts.push (x, v) }; rest := tl'
        | [] => a := { a with flags := a.flags.push x }; rest := []
      else
        a := { a with pos := a.pos.push x }; rest := tl
    | [] => rest := []
  return a

/-- The value of an option. -/
def Args.get? (a : Args) (k : String) : Option String :=
  (a.opts.find? (·.1 == k)).map (·.2)

/-- A natural-number option with a default. -/
def Args.nat (a : Args) (k : String) (dflt : Nat) : IO Nat :=
  match a.get? k with
  | none => pure dflt
  | some v =>
    match (v.replace "_" "").toNat? with
    | some x => pure x
    | none =>
      match parseRat v with
      | some q => if q.den == 1 && q.num ≥ 0 then pure q.num.toNat
                  else throw <| IO.userError s!"{k} expects a natural number"
      | none => throw <| IO.userError s!"{k} expects a natural number"

/-- Unwrap a parse result. -/
def orThrow {α : Type} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError e

/-- Usage text. -/
def usage : String :=
  "usage:\n" ++
  "  tdcsg-orbit orbit -n N (--r2 SPEC | --r Q) [--start P] [--cap C] [--threads T]\n" ++
  "                    [--no-conj] [--width W] [--format text|lines]\n" ++
  "  tdcsg-orbit thresholds -n N [--start P] [--cap C] [--upto SPEC] [--from SPEC]\n" ++
  "                    [--rc SPEC] [--unit SPEC] [--max-steps K] [--format text|lines]\n" ++
  "  tdcsg-orbit info -n N\n" ++
  "  tdcsg-orbit --selftest\n" ++
  "SPEC: touch | closed | r1 | fund, optionally followed by +q or -q; re:b0,b1,...;\n" ++
  "      pow:c0,c1,...; or a rational q (7, -3/4, 1.0362, 2.5e-7)\n" ++
  "P:    0 | a0 | b0 | zeta:k | pow:c0,c1,...\n"

/-- Set up the ring for `-n`. -/
def getField (a : Args) : IO CycField := do
  let n ← a.nat "-n" 0
  let n ← if n == 0 then a.nat "--n" 0 else pure n
  if n < 3 then throw <| IO.userError "need -n N with N ≥ 3"
  return CycField.make n

/-- Elapsed seconds since `t0` (nanoseconds). -/
def secondsSince (t0 : Nat) : IO Float := do
  let t ← IO.monoNanosNow
  return (t - t0).toFloat / 1e9

/-- The `orbit` command. -/
def cmdOrbit (a : Args) : IO Unit := do
  let F ← getField a
  let r2 ← orThrow (parseRadiusSq F (a.get? "--r2") (a.get? "--r"))
  if !F.isReal r2.num then throw <| IO.userError "the squared radius is not real"
  let start ← orThrow (parsePoint F ((a.get? "--start").getD "0"))
  let cap ← a.nat "--cap" 1000000
  let threads ← a.nat "--threads" 1
  let width ← a.nat "--width" 2
  let lines := (a.get? "--format").getD "text" == "lines"
  let conj := !a.flags.contains "--no-conj"
  let T := DiskTest.make F r2
  let t0 ← IO.monoNanosNow
  let res ← orbit T start { cap, conj, threads, width }
  let secs ← secondsSince t0
  let rate := res.size.toFloat / (if secs > 0 then secs else 1e-9)
  let mem := res.points.memoryBytes
  let r2s := showReal F r2
  let r2v := F.realToSci r2.num r2.den 17
  if lines then
    IO.println s!"param\tn\t{F.n}"
    IO.println s!"param\tr2\t{r2s}"
    IO.println s!"param\tr2_value\t{r2v}"
    IO.println s!"param\tstart\t{start}"
    IO.println s!"param\tcap\t{cap}"
    for i in [0:res.generations.size] do
      IO.println s!"gen\t{i}\t{res.generations[i]!}"
    for (k, m) in res.maxConj do
      IO.println s!"conj\t{k}\t{fmtFloat m 8}"
    IO.println s!"stat\tfilter\t{res.stats.filter}"
    IO.println s!"stat\texact\t{res.stats.exact}"
    IO.println s!"stat\tboundary\t{res.stats.boundary}"
    IO.println s!"stat\twidth\t{res.points.width}"
    IO.println s!"stat\tbytes\t{mem}"
    IO.println s!"stat\tseconds\t{fmtFloat secs 4}"
    IO.println s!"result\t{if res.complete then "finite" else "cap"}\t{res.size}"
  else
    IO.println s!"n = {F.n}, r² = {r2s} ≈ {r2v}, start = {start}"
    if res.complete then
      IO.println s!"orbit is finite: exactly {res.size} points"
    else
      IO.println s!"cap reached: at least {res.size} points (no claim about finiteness)"
    IO.println s!"generations: {res.generations.size}; new points per generation: {res.generations.toList.take 40}{if res.generations.size > 40 then " ..." else ""}"
    if conj then
      let cs := res.maxConj.toList.map fun (k, m) ↦ s!"σ_{k}: {fmtFloat m 6}"
      IO.println s!"max |σ_k z| over expanded points: {cs}"
    IO.println s!"decisions: {res.stats.filter} by float filter, {res.stats.exact} exact, {res.stats.boundary} on a boundary circle"
    IO.println s!"storage: {res.points.width} bytes/coefficient, {mem} bytes ({fmtFloat (mem.toFloat / res.size.toFloat) 3} per point)"
    IO.println s!"time: {fmtFloat secs 4} s ({fmtFloat rate 4} points/s, {threads} thread(s))"

/-- The `thresholds` command. -/
def cmdThresholds (a : Args) : IO Unit := do
  let F ← getField a
  let start ← orThrow (parsePoint F ((a.get? "--start").getD "0"))
  let cap ← a.nat "--cap" 100000
  let maxSteps ← a.nat "--max-steps" 1000000000
  let lines := (a.get? "--format").getD "text" == "lines"
  let upto ← match a.get? "--upto" with
    | some s => some <$> orThrow (parseReal F s)
    | none => pure none
  let start2 ← match a.get? "--from" with
    | some s => some <$> orThrow (parseReal F s)
    | none => pure none
  let rc ← match a.get? "--rc" with
    | some s => some <$> orThrow (parseReal F s)
    | none => pure none
  let unit ← match a.get? "--unit" with
    | some s => some <$> orThrow (parseReal F s)
    | none => pure none
  -- powers u^1 .. u^6 of the unit, for exact self-similarity checks of the gaps
  let unitPows : Array Elem := match unit with
    | none => #[]
    | some u => Id.run do
      let mut ps : Array Elem := #[]
      let mut p := u.num
      for _ in [0:6] do
        ps := ps.push p
        p := F.mul p u.num
      return ps
  let gaps ← IO.mkRef (#[] : Array Elem)
  let prevGap ← IO.mkRef (none : Option Float)
  let counter ← IO.mkRef 0
  let t0 ← IO.monoNanosNow
  if lines then
    IO.println s!"param\tn\t{F.n}"
    IO.println s!"param\tstart\t{start}"
    IO.println s!"param\tcap\t{cap}"
    if let some rc := rc then IO.println s!"param\trc2\t{showReal F rc}"
  let report (th : Threshold) : IO Unit := do
    let k ← counter.modifyGet fun k ↦ (k, k + 1)
    let tS := showReal F (RealQ.ofElem th.value)
    let tV := F.realToSci th.value 1 17
    let mut extra := ""
    if let some rc := rc then
      let gap := F.sub rc.num (F.smul rc.den th.value)
      let gS := F.realToSci gap rc.den 12
      let gF := (F.realBall gap (4 * F.basePrec)).divNat rc.den
      let gFl := (Ball.toFloatCert (4 * F.basePrec) gF).1
      let ratio := match (← prevGap.get) with
        | some g => fmtFloat (g / gFl) 8
        | none => "-"
      prevGap.set (some gFl)
      let mut hits : Array String := #[]
      let gs ← gaps.get
      for e in [0:unitPows.size] do
        let target := F.mul unitPows[e]! gap
        for j in [0:gs.size] do
          if gs[j]! == target then hits := hits.push s!"u^{e + 1}*gap{k}=gap{j}"
      gaps.modify (·.push gap)
      extra := if lines then s!"\t{gS}\t{ratio}\t{",".intercalate hits.toList}"
        else s!"  gap = {gS}  ratio = {ratio}{if hits.isEmpty then "" else s!"  {hits}"}"
    if lines then
      IO.println s!"threshold\t{k}\t{tS}\t{tV}\t{th.entering}\t{th.size}{extra}"
    else
      IO.println s!"t{k} = {tS} ≈ {tV}  entering {th.entering}  size {th.size}{extra}"
  let res ← sweep F start { cap, upto, start2, maxSteps } (report := report)
  let secs ← secondsSince t0
  if lines then
    IO.println s!"stat\tinitial\t{res.initialSize}"
    IO.println s!"stat\tfilter\t{res.stats.filter}"
    IO.println s!"stat\texact\t{res.stats.exact}"
    IO.println s!"stat\tboundary\t{res.stats.boundary}"
    IO.println s!"stat\tseconds\t{fmtFloat secs 4}"
    IO.println s!"result\t{res.stopReason}\t{res.thresholds.size}"
  else
    IO.println s!"initial orbit size {res.initialSize}; {res.thresholds.size} thresholds; stopped: {res.stopReason}; {fmtFloat secs 4} s"
    IO.println s!"decisions: {res.stats.filter} by float filter, {res.stats.exact} exact, {res.stats.boundary} on a boundary circle"

/-- The `info` command. -/
def cmdInfo (a : Args) : IO Unit := do
  let F ← getField a
  IO.println s!"n = {F.n}, φ(n) = {F.deg}, Φ_n = {F.phi}"
  IO.println s!"embeddings k (σ_k : ζ ↦ ζ^k, 1 ≤ k < n/2): {F.embeddings}"
  IO.println s!"certified float table error: {fmtFloat F.trigErr 3}"
  for name in ["touch", "closed", "r1", "fund"] do
    match namedReal F name with
    | .ok x => IO.println s!"{name} = {showReal F x} ≈ {F.realToSci x.num x.den 17}"
    | .error _ => pure ()

/-- Entry point. -/
def main (argv : List String) : IO UInt32 := do
  let a := parseArgs argv
  try
    if a.flags.contains "--selftest" then
      return (← runSelfTests)
    match a.pos[0]? with
    | some "orbit" => cmdOrbit a
    | some "thresholds" => cmdThresholds a
    | some "info" => cmdInfo a
    | _ => IO.print usage
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
