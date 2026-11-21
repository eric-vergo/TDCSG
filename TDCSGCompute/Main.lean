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
tdcsg-orbit group -n N (--r2 SPEC | --r Q) [--grid P] [--lens-B B --cloud-p P2 --cloud-k K]
                       [--orbit-cap C] [--total-cap T] [--format text|lines]
tdcsg-orbit events -n N --lens-B B --lo SPEC --upto SPEC [--cap C] [--format text|lines]
tdcsg-orbit gap -n N --lens-B B --lo SPEC --hi SPEC [--cap C] [--grid P] [--cloud-p P2]
                       [--cloud-k K] [--orbit-cap C] [--max-intervals K]
tdcsg-orbit scan -n N (--r2 SPEC | --r Q) [--terms K] [--cap C] [--top T] [--total-cap T]
                       [--near P --scale M --spread k]
tdcsg-orbit walk -n N --lo SPEC --hi SPEC [sampling options] [--eps Q] [--max-steps K]
tdcsg-orbit arrangement -n N (--r2 SPEC | --r Q) --lo SPEC --hi SPEC [sampling options]
                       [--confirm --eps Q]
tdcsg-orbit certify -n N (--r2 SPEC | --r Q) [--out FILE] [--max-pieces P] [--max-circles C]
                       [--max-seconds S] [--progress K]
tdcsg-orbit check-certificate FILE
tdcsg-orbit critical-points -n N (--r2 SPEC | --r Q) [--window w0,w1,…] [--search B]
tdcsg-orbit certify-relative -n N (--r2 SPEC | --r Q) --window w0,w1,… [--symmetric] [--out FILE]
                       [--max-pieces P] [--max-circles C] [--max-seconds S] [--progress K]
tdcsg-orbit check-relative-certificate FILE [--threads T]
tdcsg-orbit validity-interval FILE [--threads T] [--no-check] [--out FILE]
tdcsg-orbit info -n N
tdcsg-orbit --selftest
```

`orbit` and `thresholds` also take `--scale M`: the starting point is then `P / M`. The sampling
options of `group`, `gap`, `walk` and `arrangement` are `--grid P`, `--center P;Q;…` (with
`--center-p`, `--center-k`), `--lens-B`, `--cloud-p`, `--cloud-k`, `--rim K` (with `--rim-delta`,
`--rim-p`) and `--fix` (rim-vertex sampling to a fixpoint; `--fix-delta`, `--fix-p`,
`--fix-iter`); see `notes/engine.md`.

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
def flagNames : List String :=
  ["--no-conj", "--selftest", "--help", "--confirm", "--reps", "--fix", "--symmetric",
   "--no-check"]

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
  "  tdcsg-orbit group -n N (--r2 SPEC | --r Q) [--grid P] [--lens-B B --cloud-p P2\n" ++
  "                    --cloud-k K] [--orbit-cap C] [--total-cap T] [--format text|lines]\n" ++
  "  tdcsg-orbit events -n N --lens-B B --lo SPEC --upto SPEC [--cap C] [--format ...]\n" ++
  "  tdcsg-orbit gap -n N --lens-B B --lo SPEC --hi SPEC [--cap C] [--grid P] [--cloud-p P2]\n" ++
  "                    [--cloud-k K] [--orbit-cap C] [--max-intervals K]\n" ++
  "  tdcsg-orbit scan -n N (--r2 SPEC | --r Q) [--terms K] [--cap C] [--top T]\n" ++
  "                    [--total-cap T] [--near P --scale M --spread k]\n" ++
  "  tdcsg-orbit walk -n N --lo SPEC --hi SPEC [sampling options] [--eps Q]\n" ++
  "  tdcsg-orbit arrangement -n N --r2 SPEC --lo SPEC --hi SPEC [sampling options]\n" ++
  "  tdcsg-orbit certify -n N --r2 SPEC [--out FILE] [--max-pieces P] [--max-circles C]\n" ++
  "                    [--max-seconds S] [--progress K]\n" ++
  "  tdcsg-orbit check-certificate FILE\n" ++
  "  tdcsg-orbit critical-points -n N --r2 SPEC [--window w0,w1,…] [--search B]\n" ++
  "  tdcsg-orbit certify-relative -n N --r2 SPEC --window w0,w1,… [--symmetric]\n" ++
  "                    [--out FILE] [caps]\n" ++
  "  tdcsg-orbit check-relative-certificate FILE [--threads T]\n" ++
  "  tdcsg-orbit validity-interval FILE [--threads T] [--no-check] [--out FILE]\n" ++
  "  tdcsg-orbit info -n N\n" ++
  "  tdcsg-orbit --selftest\n" ++
  "SPEC: touch | closed | r1 | fund, optionally followed by +q or -q; re:b0,b1,...;\n" ++
  "      pow:c0,c1,...; or a rational q (7, -3/4, 1.0362, 2.5e-7)\n" ++
  "P:    0 | a0 | b0 | zeta:k | pow:c0,c1,...   (orbit and thresholds: --scale M for P / M)\n"

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
  let scale ← a.nat "--scale" 1
  if scale == 0 then throw <| IO.userError "--scale must be positive"
  let T := DiskTest.makeScaled F r2 scale
  let t0 ← IO.monoNanosNow
  let res ← orbit T start { cap, conj, threads, width, scale }
  let res := { res with maxConj := res.maxConj.map fun (k, m) ↦ (k, m / scale.toFloat) }
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
    IO.println s!"param\tscale\t{scale}"
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
    IO.println s!"n = {F.n}, r² = {r2s} ≈ {r2v}, start = {start}{if scale == 1 then "" else s!" / {scale}"}"
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
  let scale ← a.nat "--scale" 1
  if scale == 0 then throw <| IO.userError "--scale must be positive"
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
    IO.println s!"param\tscale\t{scale}"
    IO.println s!"param\tcap\t{cap}"
    if let some rc := rc then IO.println s!"param\trc2\t{showReal F rc}"
  let report (th : Threshold) : IO Unit := do
    let k ← counter.modifyGet fun k ↦ (k, k + 1)
    let tS := showReal F (RealQ.normalize { num := th.value, den := th.den })
    let tV := F.realToSci th.value th.den 17
    let mut extra := ""
    if let some rc := rc then
      -- gap = rc - t, over the common denominator rc.den * th.den (the same for every threshold)
      let gap := F.sub (F.smul th.den rc.num) (F.smul rc.den th.value)
      let gS := F.realToSci gap (rc.den * th.den) 12
      let gF := (F.realBall gap (4 * F.basePrec)).divNat (rc.den * th.den)
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
  let res ← sweep F start { cap, upto, start2, maxSteps, scale } (report := report)
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

/-- Parse an optional real-element option. -/
def optReal (F : CycField) (a : Args) (k : String) : IO (Option RadiusSq) :=
  match a.get? k with
  | some s => some <$> orThrow (parseReal F s)
  | none => pure none

/-- A required real-element option. -/
def reqReal (F : CycField) (a : Args) (k : String) : IO RadiusSq := do
  match ← optReal F a k with
  | some x => pure x
  | none => throw <| IO.userError s!"missing {k}"

/-- One-line summary of a group computation: status, `log₁₀ |G|`, the quotient order, the big
degrees, and the sample statistics. -/
def groupSummary (rep : GroupReport) (lines : Bool) : String :=
  let R := rep.result
  let status := if rep.capped > 0 then "orbit-cap"
    else if R.certified then "certified" else "undetermined"
  let lg := match R.log10Order with
    | some x => fmtFloat x 8
    | none => "-"
  let q := match R.quotientOrder with
    | some q => toString q
    | none => "-"
  let big := ",".intercalate (R.bigDegrees.toList.map toString)
  let small := ",".intercalate (R.others.toList.map fun (d, bl, o) ↦
    s!"{d}" ++ (if bl < d && bl > 0 then s!"[blocks {bl}]" else "") ++
      (match o with | some o => s!"(order {o})" | none => ""))
  let exact := match R.order with
    | some o => if o < 10 ^ 60 then toString o else "-"
    | none => "-"
  let wo := ",".intercalate (rep.wordOrders.toList.map toString)
  if lines then
    s!"{status}\t{lg}\t{exact}\t{q}\t{big}\t{small}\t{wo}\t{rep.samples}\t{rep.orbits}\t" ++
    s!"{R.constituents.size}\t{R.duplicates}\t{rep.nongeneric}\t{rep.capped}\t" ++
    s!"{rep.maxOrbit}\t{R.note}"
  else
    s!"{status}: log10|G| = {lg}" ++ (if exact == "-" then "" else s!", |G| = {exact}") ++
    s!"\n  |G| = {q} · ∏ d!/2 over big alternating constituents of degrees [{big}]" ++
    s!"\n  other constituents (in the quotient): [{small}]" ++
    s!"\n  orders of a, b, ab, [a,b]: {wo}" ++
    s!"\n  samples {rep.samples}: {rep.orbits} generic orbits ({rep.points} points, largest " ++
    s!"{rep.maxOrbit}), {rep.seen} already seen, {rep.fixed} fixed, " ++
    s!"{rep.nongeneric} non-generic, " ++
    s!"{rep.capped} capped; {R.constituents.size} inequivalent constituents, {R.duplicates} " ++
    s!"equivalent ones dropped" ++ (if R.note.isEmpty then "" else s!"\n  note: {R.note}")

/-- The sample set of `group` and `gap`: a grid at scale `--grid`, and clouds at scale
`--cloud-p` around the lens family with coefficient bound `--lens-B` at the squared radius
`hi`. -/
def groupSamples (F : CycField) (a : Args) (hi : RadiusSq) : IO (Array (Nat × Elem)) := do
  let p ← a.nat "--grid" 23
  let hiF := (Ball.toFloatCert F.basePrec ((F.realBall hi.num F.basePrec).divNat hi.den)).1
  let grid := if p == 0 then #[] else gridSamples F p hiF
  let cp ← a.nat "--cloud-p" 0
  let ck ← a.nat "--cloud-k" 1
  let B ← a.nat "--lens-B" 1
  let cloud ← if cp == 0 then pure #[] else do
    let fam ← lensFamily F B hi
    pure (cloudSamples F cp ck fam)
  -- clouds around given points of ℚ(ζ_n) (`--center P` or `P/Q`, repeatable via `;`)
  let centers := match a.get? "--center" with
    | some cs => cs.splitOn ";"
    | none => []
  let cp2 ← a.nat "--center-p" 1000003
  let ck2 ← a.nat "--center-k" 2
  let mut extra : Array (Nat × Elem) := #[]
  for c in centers do
    let (u, D) ← orThrow (parsePointQ F c)
    if D % cp2 == 0 || F.n % cp2 == 0 then throw <| IO.userError "--center-p must not divide n or D"
    extra := extra ++ cloudAround F cp2 ck2 u D
    -- the mirror images under z ↦ z̄ and z ↦ -z
    extra := extra ++ cloudAround F cp2 ck2 (F.conj u) D ++ cloudAround F cp2 ck2 (F.neg u) D
  -- points at depths `--rim-delta` (comma-separated) inside the boundary circles
  let rimK ← a.nat "--rim" 0
  let rim ← if rimK == 0 then pure #[] else do
    let ds ← orThrow (parseRatList ((a.get? "--rim-delta").getD "1e-3,1e-4,1e-5"))
    let rp ← a.nat "--rim-p" 100000000003
    pure (rimSamples F hiF rimK rp (ds.map fun q ↦ (Float.ofInt q.num) / q.den.toFloat))
  return grid ++ cloud ++ extra ++ rim

/-- Options of `group` and `gap`. -/
def groupOpts (a : Args) : IO GroupOptions := do
  return { orbitCap := ← a.nat "--orbit-cap" 200000, totalCap := ← a.nat "--total-cap" 5000000,
           tries := ← a.nat "--tries" 400 }

/-- The group at `r2` on the samples, with rim-vertex sampling to a fixpoint when `--fix` is
given (depth `--fix-delta`, scale `--fix-p`, at most `--fix-iter` rounds). Returns the report
and a description of the rounds. -/
def computeGroup (F : CycField) (a : Args) (r2 : RadiusSq) (samples : Array (Nat × Elem)) :
    IO (GroupReport × String) := do
  let opts ← groupOpts a
  if a.flags.contains "--fix" then
    let δq := (parseRat ((a.get? "--fix-delta").getD "1e-11")).getD (1 / 10 ^ 11)
    let δ := Float.ofInt δq.num / δq.den.toFloat
    let p ← a.nat "--fix-p" 10000000000037
    let it ← a.nat "--fix-iter" 12
    let (rep, rounds, conv, _) ← groupFixpoint F r2 samples opts δ p it
    return (rep, s!"{if conv then "fixpoint" else "no-fixpoint"}:{rounds.toList}")
  else
    return (← groupOn F r2 samples opts, "samples-only")

/-- The `group` command. -/
def cmdGroup (a : Args) : IO Unit := do
  let F ← getField a
  let r2 ← orThrow (parseRadiusSq F (a.get? "--r2") (a.get? "--r"))
  let lines := (a.get? "--format").getD "text" == "lines"
  let samples ← groupSamples F a r2
  let t0 ← IO.monoNanosNow
  let (rep, how) ← computeGroup F a r2 samples
  let secs ← secondsSince t0
  let r2s := showReal F r2
  if lines then
    IO.println (s!"group\t{F.n}\t{r2s}\t{F.realToSci r2.num r2.den 17}\t" ++
      s!"{groupSummary rep true}\t{how}\t{fmtFloat secs 4}")
  else
    IO.println s!"n = {F.n}, r² = {r2s} ≈ {F.realToSci r2.num r2.den 17}"
    IO.println (groupSummary rep false)
    IO.println s!"  sampling: {how}"
    let more := if rep.sizes.size > 60 then " ..." else ""
    IO.println s!"  constituent sizes: {rep.sizes.toList.take 60}{more}"
    IO.println s!"  time: {fmtFloat secs 4} s"
    if a.flags.contains "--reps" then
      for (d, M, w) in rep.reps do
        IO.println s!"  rep\t{d}\tpow:{",".intercalate (w.toList.map toString)}\t{M}"
      for (M, w) in rep.cappedSamples do
        IO.println s!"  capped\tpow:{",".intercalate (w.toList.map toString)}\t{M}"

/-- The `events` command: merged thresholds of the lens family. -/
def cmdEvents (a : Args) : IO Unit := do
  let F ← getField a
  let lo ← reqReal F a "--lo"
  let upto ← reqReal F a "--upto"
  let B ← a.nat "--lens-B" 1
  let cap ← a.nat "--cap" 100000
  let fam ← lensFamily F B upto
  let m ← mergedThresholds F fam lo upto cap
  IO.println s!"param\tn\t{F.n}"
  IO.println s!"param\tfamily\t{fam.size}"
  IO.println s!"param\tcapped\t{m.cappedStarts}"
  match m.completeUpTo with
  | some c =>
    IO.println s!"param\tcomplete_up_to\t{showReal F (RealQ.ofElem c)}\t{F.realToSci c 1 17}"
  | none => IO.println s!"param\tcomplete_up_to\tupto"
  for i in [0:m.values.size] do
    let (v, c) := m.values[i]!
    IO.println s!"event\t{i}\t{showReal F (RealQ.ofElem v)}\t{F.realToSci v 1 20}\t{c}"

/-- The `gap` command: merged thresholds of the lens family in `[lo, hi)`, and the group at a
rational squared radius in each interval between consecutive thresholds. -/
def cmdGap (a : Args) : IO Unit := do
  let F ← getField a
  let lo ← reqReal F a "--lo"
  let hi ← reqReal F a "--hi"
  let B ← a.nat "--lens-B" 1
  let cap ← a.nat "--cap" 100000
  let maxI ← a.nat "--max-intervals" 1000000
  let fam ← lensFamily F B hi
  let m ← mergedThresholds F fam lo hi cap
  let mut top := hi
  if let some c := m.completeUpTo then
    if RealQ.compare F (RealQ.ofElem c) hi == some .lt then top := RealQ.ofElem c
  let evs := m.values.filter fun (v, _) ↦ RealQ.compare F (RealQ.ofElem v) top == some .lt
  IO.println s!"param\tn\t{F.n}\tfamily\t{fam.size}\tcapped\t{m.cappedStarts}"
  IO.println s!"param\ttop\t{showReal F top}\t{F.realToSci top.num top.den 17}"
  for i in [0:evs.size] do
    let (v, c) := evs[i]!
    IO.println s!"event\t{i + 1}\t{showReal F (RealQ.ofElem v)}\t{F.realToSci v 1 20}\t{c}"
  let samples ← groupSamples F a hi
  IO.println s!"param\tsamples\t{samples.size}"
  let bounds : Array RadiusSq := #[lo] ++ evs.map (fun e ↦ RealQ.ofElem e.1) ++ #[top]
  for k in [0:min maxI (bounds.size - 1)] do
    match rationalBetween F bounds[k]! bounds[k + 1]! with
    | none => IO.println s!"interval\t{k}\tno-rational"
    | some q =>
      let t0 ← IO.monoNanosNow
      let (rep, how) ← computeGroup F a (RealQ.ofRat F q) samples
      let secs ← secondsSince t0
      IO.println s!"interval\t{k}\t{q}\t{groupSummary rep true}\t{how}\t{fmtFloat secs 4}"
      if rep.capped > 0 then break

/-- The `scan` command: orbits of many starting points at one radius. -/
def cmdScan (a : Args) : IO Unit := do
  let F ← getField a
  let r2 ← orThrow (parseRadiusSq F (a.get? "--r2") (a.get? "--r"))
  let K ← a.nat "--terms" 3
  let cap ← a.nat "--cap" 1000000
  let top ← a.nat "--top" 20
  let totalCap ← a.nat "--total-cap" 30000000
  let T1 := DiskTest.make F r2
  -- candidates
  let mut cands : Array (Nat × Elem) := #[]
  match a.get? "--near" with
  | some ps =>
    let M ← a.nat "--scale" 1000003
    let k ← a.nat "--spread" 1
    -- several centres separated by `;`: points `P`, `P/Q`, `necklace`, or plane points `xy:x,y`
    for c in ps.splitOn ";" do
      if c.startsWith "xy:" then
        match (c.drop 3).toString.splitOn "," with
        | [xs, ys] =>
          let x ← orThrow (match parseRat xs with | some q => .ok q | none => .error "bad x")
          let y ← orThrow (match parseRat ys with | some q => .ok q | none => .error "bad y")
          let toF (q : Rat) : Float := Float.ofInt q.num / q.den.toFloat
          match roundedSample F M (toF x) (toF y) with
          | some (_, w0) => cands := cands ++ (cloudAround F M k w0 1).map fun (_, w) ↦
              (M, F.sub w (F.smul ((M : Int) - 1) w0))
          | none => pure ()
        | _ => throw <| IO.userError s!"cannot parse {c}"
      else
        let (u, D) ← orThrow (parsePointQ F c)
        cands := cands ++ cloudAround F M k u D
  | none =>
    let mut canon : Std.HashSet Elem := {}
    for t in signedSums F.n K do
      let z := t.foldl (fun acc (e, sg) ↦ F.add acc (F.smul sg (F.zetaPow e))) F.zero
      let (x, y) := approxPoint F z 1
      let r2f := T1.r2F
      if (x + 1) * (x + 1) + y * y > r2f + 1e-9 || (x - 1) * (x - 1) + y * y > r2f + 1e-9 then
        continue
      if !(← inLens T1 z) then continue
      let c := F.canonical z
      if canon.contains c then continue
      canon := canon.insert c
      cands := cands.push (1, c)
  IO.println s!"param\tn\t{F.n}\tr2\t{showReal F r2}\t{F.realToSci r2.num r2.den 17}"
  IO.println s!"param\tcandidates\t{cands.size}"
  let mut seen : Std.HashSet (Nat × Elem) := {}
  let mut stored := 0
  let mut results : Array (Nat × Bool × Nat × Elem) := #[]
  let mut skipped := 0
  let mut tests : Std.HashMap Nat DiskTest := {}
  let t0 ← IO.monoNanosNow
  for (M, w) in cands do
    if seen.contains (M, w) then
      skipped := skipped + 1
      continue
    let T ← match tests[M]? with
      | some T => pure T
      | none =>
        let T := DiskTest.makeScaled F r2 M
        tests := tests.insert M T
        pure T
    let res ← orbit T w { cap, conj := false, scale := M }
    results := results.push (res.size, res.complete, M, w)
    if stored + res.size ≤ totalCap then
      for i in [0:res.points.size] do
        seen := seen.insert (M, res.points.get i)
      stored := stored + res.size
  let secs ← secondsSince t0
  -- histogram of finite sizes
  let mut hist : Std.HashMap Nat Nat := {}
  let mut nCap := 0
  for (sz, c, _, _) in results do
    if c then hist := hist.insert sz (hist.getD sz 0 + 1) else nCap := nCap + 1
  IO.println (s!"param\torbits\t{results.size}\tskipped\t{skipped}\tcapped\t{nCap}\t" ++
    s!"seconds\t{fmtFloat secs 4}")
  for (sz, c) in hist.toArray.qsort (fun x y ↦ x.1 < y.1) do
    IO.println s!"size\t{sz}\t{c}"
  let sorted := results.qsort fun x y ↦ x.1 > y.1 || (x.1 == y.1 && !x.2.1 && y.2.1)
  for i in [0:min top sorted.size] do
    let (sz, c, M, w) := sorted[i]!
    let ws := ",".intercalate (w.toList.map toString)
    IO.println s!"top\t{i}\t{if c then "finite" else "cap"}\t{sz}\tpow:{ws}\t{M}"

/-- The `arrangement` command: candidate events (tangencies and triple points of the circles about
the centres of the germs seen at `--r2`) in the window `(--lo, --hi)`; with `--confirm`, the group
at `t - ε` and `t + ε` (`--eps`) for each candidate `t`, with a cloud of generic points around its
vertex. -/
def cmdArrangement (a : Args) : IO Unit := do
  let F ← getField a
  let r2 ← orThrow (parseRadiusSq F (a.get? "--r2") (a.get? "--r"))
  let lo ← reqReal F a "--lo"
  let hi ← reqReal F a "--hi"
  let samples ← groupSamples F a hi
  let germs ← germsOf F r2 samples (← a.nat "--orbit-cap" 200000)
  let cands ← eventCandidates F germs lo hi
  IO.println s!"param\tn\t{F.n}\tgerms\t{germs.size}\tcandidates\t{cands.size}"
  let confirm := a.flags.contains "--confirm"
  let eps : Rat := (parseRat ((a.get? "--eps").getD "1e-9")).getD (1 / 10 ^ 9)
  let cp ← a.nat "--center-p" 1000000000039
  let ck ← a.nat "--center-k" 4
  let opts ← groupOpts a
  for i in [0:cands.size] do
    let c := cands[i]!
    let base := s!"cand\t{i}\t{if c.tangency then "tangent" else "triple"}\t{showReal F c.r2}\t" ++
      s!"{F.realToSci c.r2.num c.r2.den 20}\tpow:{",".intercalate (c.u.toList.map toString)}/{c.D}"
    if !confirm then
      IO.println base
    else
      let cl := cloudAround F cp ck c.u c.D ++ cloudAround F cp ck (F.conj c.u) c.D ++
        cloudAround F cp ck (F.neg c.u) c.D ++ cloudAround F cp ck (F.neg (F.conj c.u)) c.D
      let below ← groupOn F (RealQ.addRat F c.r2 (-eps)) (samples ++ cl) opts
      let above ← groupOn F (RealQ.addRat F c.r2 eps) (samples ++ cl) opts
      let changed := below.signature != above.signature
      IO.println (base ++ s!"\t{if changed then "CHANGE" else "same"}\t" ++
        s!"{(below.result.log10Order.map (fmtFloat · 8)).getD "-"}\t" ++
        s!"{(above.result.log10Order.map (fmtFloat · 8)).getD "-"}\t" ++
        s!"{below.signature}\t{above.signature}")

/-- The `walk` command: from `--lo` (an event value) up to `--hi`, alternately compute the group
just above the current event (`+ --eps`) with rim-vertex sampling to a fixpoint, derive the next
candidate event from the centres of its germs, and recompute the group at a rational inside the
interval as a consistency check. -/
def cmdWalk (a : Args) : IO Unit := do
  let F ← getField a
  let lo ← reqReal F a "--lo"
  let hi ← reqReal F a "--hi"
  let maxSteps ← a.nat "--max-steps" 1000
  let eps : Rat := (parseRat ((a.get? "--eps").getD "1e-9")).getD (1 / 10 ^ 9)
  let δq := (parseRat ((a.get? "--fix-delta").getD "1e-11")).getD (1 / 10 ^ 11)
  let δ := Float.ofInt δq.num / δq.den.toFloat
  let p ← a.nat "--fix-p" 10000000000037
  let it ← a.nat "--fix-iter" 12
  let opts ← groupOpts a
  let samples ← groupSamples F a hi
  let mut cur := lo
  let mut prevSig := ""
  IO.println s!"param\tn\t{F.n}\tlo\t{showReal F lo}\thi\t{showReal F hi}\teps\t{eps}"
  for k in [0:maxSteps] do
    let qa := RealQ.addRat F cur eps
    let t0 ← IO.monoNanosNow
    let (ra, rda, ca, cen) ← groupFixpoint F qa samples opts δ p it
    let cands ← eventCandidatesOfCentres F (cen.push (F.ofInt 1) |>.push (F.ofInt (-1))) qa hi
    let (next, kind, vtx) := match cands[0]? with
      | some c => (c.r2, if c.tangency then "tangent" else "triple",
          s!"pow:{",".intercalate (c.u.toList.map toString)}/{c.D}")
      | none => (hi, "hi", "-")
    let qb := (rationalBetween F qa next).getD 0
    let (rb, rdb, cb, _) ← groupFixpoint F (RealQ.ofRat F qb) samples opts δ p it
    let secs ← secondsSince t0
    let sigA := ra.signature
    let sigB := rb.signature
    let lg (r : GroupReport) := (r.result.log10Order.map (fmtFloat · 10)).getD "-"
    IO.println (s!"step\t{k}\t{showReal F cur}\t{F.realToSci cur.num cur.den 20}\t" ++
      s!"{if sigA == prevSig then "same" else "CHANGE"}\t{lg ra}\t" ++
      s!"{if sigA == sigB then "consistent" else "INCONSISTENT"}\t{lg rb}\t{qb}\t" ++
      s!"{if ca && cb then "fixpoint" else "no-fixpoint"}:" ++
      s!"{rda.back?.getD 0}:{rdb.back?.getD 0}\t" ++
      s!"{cen.size}\t{cands.size}\t{kind}\t{showReal F next}\t" ++
      s!"{F.realToSci next.num next.den 20}\t{vtx}\t" ++
      s!"{fmtFloat secs 4}\t{sigA}")
    if ra.capped > 0 || rb.capped > 0 then
      IO.println "stop\torbit-cap"
      break
    prevSig := sigA
    if kind == "hi" then break
    cur := next

/-- The `certify` command: compute the cut set and write the certificate. -/
def cmdCertify (a : Args) : IO UInt32 := do
  let F ← getField a
  let spec := (a.get? "--r2").getD ""
  let r2 ← orThrow (parseRadiusSq F (a.get? "--r2") (a.get? "--r"))
  if !F.isReal r2.num then throw <| IO.userError "the squared radius is not real"
  let opts : CloseOptions :=
    { maxPieces := ← a.nat "--max-pieces" 10000000, maxCircles := ← a.nat "--max-circles" 5000000,
      maxSeconds := ← a.nat "--max-seconds" 0, progress := ← a.nat "--progress" 0 }
  let r2s := showReal F r2
  let r2v := F.realToSci r2.num r2.den 17
  let specS := if spec.isEmpty then "" else s!" ({spec})"
  let comment := #[s!"n = {F.n}, r² = {r2s} ≈ {r2v}{specS}",
    "arcs run counterclockwise; symbol (e, ±) on the circle about c is the intersection point",
    "c + (d/2)(1 ± i h), d = e - c, h = sqrt(4 r²/|d|² - 1); coefficients in 1, ζ, …, ζ^(φ(n)-1)"]
  IO.println s!"certify: n = {F.n}, r² = {r2s} ≈ {r2v}"
  let o ← certify F r2 opts comment
  let res := o.result
  let st := res.stats
  IO.println s!"pieces {st.pieces}, image arcs {st.images}, circles {res.store.size}"
  IO.println s!"decisions made exactly: {st.exactHalves} halves, {st.exactCross} orders; \
    {st.coincidences} equalities of points with different symbols"
  IO.println s!"time {fmtFloat (res.millis.toFloat / 1000) 4} s"
  if let some S := o.summary then
    IO.println s!"circles {S.circles} (full {S.fullCircles}), maximal arcs {S.arcs}"
    IO.println s!"(C4) endpoints on boundary circles {S.c4Endpoints}, failures {S.c4Failures}"
    let cs := S.maxConj.toList.map fun (k, m) ↦ s!"σ_{k}: {fmtFloat m 5}"
    IO.println s!"max |σ_k(c)| over centres: {cs}"
  match o.text with
  | some text =>
    match a.get? "--out" with
    | some path =>
      IO.FS.writeFile path text
      IO.println s!"certificate written to {path} ({text.utf8ByteSize} bytes)"
    | none => pure ()
    IO.println "result CERTIFIED (generator); check with `check-certificate`"
    return 0
  | none =>
    IO.println s!"result NOT CERTIFIED: {o.reason}"
    return 3

/-- The `check-certificate` command. -/
def cmdCheck (a : Args) : IO UInt32 := do
  let some (path : String) := a.pos[1]? | throw <| IO.userError "usage: check-certificate FILE"
  let t0 ← IO.monoNanosNow
  match (← parseCertificateFile path) >>= checkCertificate with
  | .ok rep =>
    IO.println s!"certificate VALID: circles {rep.circles} (full {rep.fullCircles}), \
      maximal arcs {rep.arcs}, (C2) image arcs {rep.c2Images}, (C4) endpoints {rep.c4Endpoints}"
    IO.println s!"time {fmtFloat (← secondsSince t0) 4} s"
    return 0
  | .error e =>
    IO.println s!"certificate REJECTED: {e}"
    return 2

/-- Parse a window shape vector `w0,w1,…` (power-basis coefficients). -/
def parseWindow (F : CycField) (a : Args) : IO Elem := do
  let some s := a.get? "--window" | throw <| IO.userError "--window w0,w1,… is required"
  orThrow (parsePoint F s!"pow:{s}")

/-- The `critical-points` command: the lattice points on the boundary circles, their symmetry
classes, and (with `--window`) the window geometry. -/
def cmdCritical (a : Args) : IO UInt32 := do
  let F ← getField a
  let r2 ← orThrow (parseRadiusSq F (a.get? "--r2") (a.get? "--r"))
  let C := CircleCtx.make F r2
  let crit ← orThrow (criticalPoints F r2)
  let norms ← orThrow (latticeOfNorm F r2)
  IO.println s!"n = {F.n}, r² = {showReal F r2}: {norms.size} lattice elements of norm r², \
    {crit.size} critical points"
  let classes := sortDedup (crit.map (symCanonical F))
  IO.println s!"{classes.size} classes under z ↦ ±z, ±z̄"
  for P in classes do
    let members := crit.filter fun x ↦ symCanonical F x == P
    let (x, y) := F.evalConjF 1 P
    let onL := F.smul (r2.den : Int) (F.normSq (F.addInt P 1)) == r2.num
    let onR := F.smul (r2.den : Int) (F.normSq (F.addInt P (-1))) == r2.num
    let other := if onL && onR then "on both circles" else
      let q : Int := if onL then -1 else 1
      match C.S.sign (F.sub r2.num (F.smul (r2.den : Int) (F.normSq (F.addInt P (-q))))) with
      | some v => if v > 0 then "inside the other disk" else "outside the other disk"
      | none => "?"
    IO.println s!"  class {elemToString P} ({fmtFloat x 5}, {fmtFloat y 5}): {members.size} \
      points, {other}"
  if let some bs := a.get? "--search" then
    -- window shapes with coefficients in [-B, B], one per symmetry orbit, whose windows are
    -- disjoint (decided exactly), with their circumradius bound ρ̄
    let B : Nat := bs.toNat?.getD 3
    let d := F.deg
    let m := 2 * B + 1
    let mut found : Array (Float × Elem) := #[]
    for t in [0:m ^ d] do
      let mut x : Array Int := #[]
      let mut rest := t
      for _ in [0:d] do
        x := x.push ((rest % m : Nat) - (B : Int))
        rest := rest / m
      if F.isZero x || symCanonical F x != x then continue
      match WindowSet.make C x >>= WindowSet.withBound C with
      | .error _ => pure ()
      | .ok WS =>
        match windowsDisjoint C WS with
        | .ok (true, _) => found := found.push (WS.rhoNum.toFloat / 65536, x)
        | _ => pure ()
    let sorted := found.qsort fun u v ↦ u.1 > v.1
    IO.println s!"{sorted.size} window shapes with disjoint windows (coefficients in [-{B}, {B}])"
    for (ρ, x) in sorted do
      IO.println s!"  ρ̄ = {fmtFloat ρ 5}  w = {elemToString x}"
  if (a.get? "--window").isSome then
    let w ← parseWindow F a
    let WS ← orThrow (WindowSet.make C w)
    let corners ← orThrow (windowCorners C WS.shape)
    let (disj, pairs) ← orThrow (windowsDisjoint C WS)
    let rc := Float.sqrt ((F.evalConjF 1 r2.num).1 / r2.den.toFloat)
    let (wx, wy) := F.evalConjF 1 w
    let mut ρ : Float := 0
    for (v, s) in corners do
      let (vx, vy) := F.evalConjF 1 v
      let (ex, ey) := F.evalConjF 1 s.e
      let (dx, dy) := (ex - vx, ey - vy)
      let nd := Float.sqrt (dx * dx + dy * dy)
      let h := Float.sqrt (rc * rc - nd * nd / 4)
      let sg : Float := if s.plus then 1 else -1
      let px := vx + dx / 2 - sg * h * dy / nd
      let py := vy + dy / 2 + sg * h * dx / nd
      ρ := max ρ (Float.sqrt (px * px + py * py))
    IO.println s!"window w = {elemToString w}: {WS.shape.size} disks, inradius \
      {fmtFloat (rc - Float.sqrt (wx * wx + wy * wy)) 5}, circumradius {fmtFloat ρ 5} \
      ({corners.size} corners); pairwise disjoint: {disj} ({pairs} pairs, exact)"
  return 0

/-- The `certify-relative` command. -/
def cmdCertifyRelative (a : Args) : IO UInt32 := do
  let F ← getField a
  let spec := (a.get? "--r2").getD ""
  let r2 ← orThrow (parseRadiusSq F (a.get? "--r2") (a.get? "--r"))
  if !F.isReal r2.num then throw <| IO.userError "the squared radius is not real"
  let w ← parseWindow F a
  let opts : CloseOptions :=
    { maxPieces := ← a.nat "--max-pieces" 2000000000,
      maxCircles := ← a.nat "--max-circles" 200000000,
      maxSeconds := ← a.nat "--max-seconds" 0, progress := ← a.nat "--progress" 0 }
  let r2s := showReal F r2
  let r2v := F.realToSci r2.num r2.den 17
  let specS := if spec.isEmpty then "" else s!" ({spec})"
  let comment := #[s!"relative certificate: n = {F.n}, r² = {r2s} ≈ {r2v}{specS}, \
      window shape {elemToString w}",
    "arcs run counterclockwise; symbol (e, ±) on the circle about c is the intersection point",
    "c + (d/2)(1 ± i h), d = e - c, h = sqrt(4 r²/|d|² - 1); coefficients in 1, ζ, …, ζ^(φ(n)-1)"]
  IO.println s!"certify-relative: n = {F.n}, r² = {r2s} ≈ {r2v}, window {elemToString w}"
  let sym := a.flags.contains "--symmetric"
  let o ← certifyRelative F r2 w opts comment sym ((a.get? "--out").map (⟨·⟩))
  IO.println s!"critical points (windows) {o.WS.crit.size}, window disks {o.WS.shape.size}"
  if !o.reason.isEmpty && o.summary.isNone && o.result.millis == 0 then
    IO.println s!"result NOT CERTIFIED: {o.reason}"
    return 3
  let res := o.result
  let st := res.stats
  IO.println s!"pieces {st.pieces}, image arcs {st.images}, circles {res.store.size}, \
    clipped pieces on window-crossing circles {res.windowClips}"
  IO.println s!"decisions made exactly: {st.exactHalves} halves, {st.exactCross} orders; \
    {st.coincidences} equalities of points with different symbols"
  IO.println s!"tangencies to a boundary circle: {res.tangencies.size} circles, \
    {o.tangentAtCritical} with the point of contact at a critical point"
  IO.println s!"time {fmtFloat (res.millis.toFloat / 1000) 4} s"
  if let some K := o.coinc then
    IO.println s!"coincidences: {K.records} distinct (circle, symbol, symbol) records, \
      {K.latticePoints} distinct lattice points; at critical points {K.atCritical}, at other \
      lattice points {K.atOtherLattice}, at non-lattice points {K.nonLattice}; in window \
      interiors {K.inWindow}, on window boundaries {K.onWindowBoundary}, in the bulk {K.inBulk}"
    for (c, x, y) in K.bulkExamples do
      IO.println s!"  bulk coincidence on {elemToString c}: ({elemToString x.e}, {x.plus}) = \
        ({elemToString y.e}, {y.plus})"
  if !o.WS.active && o.summary.isSome then
    let ok := res.tangencies.isEmpty && o.c4.2 == 0
    IO.println s!"no windows: (C3) tangencies {res.tangencies.size}, (C4) endpoints {o.c4.1}, \
      failures {o.c4.2}{if ok then "; (C1)–(C4) hold (an ordinary cut-set certificate)" else ""}"
  if let some S := o.summary then
    IO.println s!"circles {S.circles} (full {S.fullCircles}), maximal arcs {S.arcs}; modulo \
      ±z, ±z̄: circles {S.canonCircles}, arcs {S.canonArcs}"
    let cs := S.maxConj.toList.map fun (k, m) ↦ s!"σ_{k}: {fmtFloat m 5}"
    IO.println s!"max |σ_k(c)| over centres: {cs}"
  match o.text with
  | some _ =>
    if let some path := a.get? "--out" then
      IO.println s!"relative certificate written to {path}{if sym then " (symmetric)" else ""}"
    IO.println "result CLOSED (generator); check with `check-relative-certificate`"
    return 0
  | none =>
    IO.println s!"result NOT CERTIFIED: {o.reason}"
    return 3

/-- The `check-relative-certificate` command. -/
def cmdCheckRelative (a : Args) : IO UInt32 := do
  let some (path : String) := a.pos[1]? |
    throw <| IO.userError "usage: check-relative-certificate FILE"
  let t0 ← IO.monoNanosNow
  let threads ← a.nat "--threads" 1
  match (← parseRelativeFile path) >>= (checkRelative · threads) with
  | .ok rep =>
    IO.println s!"relative certificate VALID: circles {rep.circles} (full {rep.fullCircles}), \
      maximal arcs {rep.arcs}; modulo ±z, ±z̄: circles {rep.canonCircles}, arcs \
      {rep.canonArcs}; windows {rep.windows} ({rep.windowPairs} pairs disjoint), boundary \
      arcs {rep.boundaryArcs}, (K3) image arcs {rep.images}, tangent circles \
      {rep.tangentCircles}"
    if rep.windows == 0 || rep.windowPairs == 0 then
      let ok := rep.tangentCircles == 0 && rep.c4Failures == 0
      IO.println s!"no windows: (C3) tangent circles {rep.tangentCircles}, (C4) endpoints \
        {rep.c4Endpoints}, failures {rep.c4Failures}{if ok then
          "; (C1)–(C4) hold: an ordinary cut-set certificate" else ""}"
    IO.println s!"time {fmtFloat (← secondsSince t0) 4} s"
    return 0
  | .error e =>
    IO.println s!"relative certificate REJECTED: {e}"
    return 2

/-- The largest `m` with `m / 2^k < num / den` (`den > 0` real elements), by bisection with exact
signs. -/
def dyadicBelow (C : CircleCtx) (num den : Elem) (k : Nat) (hi0 : Nat) : IO Nat := do
  let F := C.F
  let below (m : Nat) : IO Bool := do
    -- m / 2^k < num / den  ⟺  m den - 2^k num < 0
    match C.S.sign (F.sub (F.smul (m : Int) den) (F.smul ((2 ^ k : Nat) : Int) num)) with
    | some s => return s < 0
    | none => throw <| IO.userError "sign determination failed"
  let mut lo := 0
  let mut hi := hi0
  while !(← below 0) do throw <| IO.userError "the event is not positive"
  while (← below hi) do hi := 2 * hi
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if ← below mid then lo := mid else hi := mid
  return lo

/-- The `validity-interval` command. -/
def cmdValidity (a : Args) : IO UInt32 := do
  let some (path : String) := a.pos[1]? |
    throw <| IO.userError "usage: validity-interval FILE [--threads T] [--out FILE]"
  let threads ← a.nat "--threads" 1
  let t0 ← IO.monoNanosNow
  let P ← orThrow (← parseCertificateFile path)
  if !a.flags.contains "--no-check" then
    match checkCertificate P with
    | .ok _ => IO.println s!"certificate VALID at its radius ({fmtFloat (← secondsSince t0) 4} s)"
    | .error e =>
      IO.println s!"certificate REJECTED: {e}"
      return 2
  let F := CycField.make P.n
  let C := CircleCtx.make F P.r2
  let rep ← orThrow (validityInterval P threads)
  IO.println s!"adjacent pairs examined {rep.pairs}, disk events {rep.diskEvents}, \
    coincident at the start {rep.coincidentAtStart}"
  IO.println s!"time {fmtFloat (← secondsSince t0) 4} s"
  if rep.coincidentAtStart > 0 then
    IO.println "result: two compared points coincide at the certificate's radius; no extension"
    return 3
  let some e := rep.least | do
    IO.println "result: no event found"
    return 3
  let ev := (F.evalConjF 1 e.num).1 / (F.evalConjF 1 e.den).1
  let r0 := (F.evalConjF 1 P.r2.num).1 / P.r2.den.toFloat
  IO.println s!"least event: {e.kind} on the circle about {elemToString e.circle}"
  IO.println s!"  ρ₁ = ({elemToString e.num}) / ({elemToString e.den}) ≈ {fmtFloat ev 15}; \
    ρ₀ ≈ {fmtFloat r0 15}"
  match namedReal F "closed" with
  | .ok rc =>
    let rcv := (F.evalConjF 1 rc.num).1 / rc.den.toFloat
    IO.println s!"  r_c² - ρ₀ ≈ {fmtFloat (rcv - r0) 8}, r_c² - ρ₁ ≈ {fmtFloat (rcv - ev) 8}"
  | .error _ => pure ()
  -- a dyadic radius just below ρ₁, for an independent re-check of the same arcs there
  let k := 100
  let m ← dyadicBelow C e.num e.den k ((ev.ceil.toUInt64.toNat + 1) * 2 ^ k)
  let above := match C.S.sign (F.sub (F.smul (m : Int) (F.ofInt P.r2.den))
      (F.smul ((2 ^ k : Nat) : Int) P.r2.num)) with
    | some s => decide (s > 0)
    | none => false
  IO.println s!"  dyadic radius below ρ₁: r² = {m} / 2^{k} (above ρ₀: {above})"
  if let some out := a.get? "--out" then
    let text ← IO.FS.readFile path
    let ls := (text.splitOn "\n").map fun l ↦
      if l.startsWith "r2 " then
        s!"r2 {",".intercalate ((F.ofInt (m : Int)).toList.map toString)} / {2 ^ k}" else l
    IO.FS.writeFile out ("\n".intercalate ls)
    IO.println s!"  the same arcs at that radius written to {out}"
  return 0

/-- The `info` command. -/
def cmdInfo (a : Args) : IO Unit := do
  let F ← getField a
  IO.println s!"n = {F.n}, φ(n) = {F.deg}, Φ_n = {F.phi}"
  IO.println s!"embeddings k (σ_k : ζ ↦ ζ^k, 1 ≤ k < n/2): {F.embeddings}"
  IO.println s!"certified float table error: {fmtFloat F.trigErr 3}"
  for name in ["touch", "closed", "r1", "fund", "ra"] do
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
    | some "group" => cmdGroup a
    | some "events" => cmdEvents a
    | some "gap" => cmdGap a
    | some "scan" => cmdScan a
    | some "arrangement" => cmdArrangement a
    | some "walk" => cmdWalk a
    | some "certify" => return (← cmdCertify a)
    | some "check-certificate" => return (← cmdCheck a)
    | some "critical-points" => return (← cmdCritical a)
    | some "certify-relative" => return (← cmdCertifyRelative a)
    | some "check-relative-certificate" => return (← cmdCheckRelative a)
    | some "validity-interval" => return (← cmdValidity a)
    | _ => IO.print usage
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
