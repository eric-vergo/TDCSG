/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Thresholds

/-!
# Self-tests of the orbit engine

`runSelfTests` (run by `lake test` or `tdcsg-orbit --selftest`) checks the arithmetic, the
certified membership test, and known facts about the two-disk systems.
-/

namespace TDCSGCompute

/-- Accumulated test outcomes. -/
structure TestLog where
  /-- Number of passed checks. -/
  passed : Nat := 0
  /-- Descriptions of failed checks. -/
  failed : Array String := #[]

/-- Record one check. -/
def check (log : IO.Ref TestLog) (name : String) (ok : Bool) : IO Unit := do
  if ok then log.modify fun l ↦ { l with passed := l.passed + 1 }
  else
    IO.println s!"FAIL: {name}"
    log.modify fun l ↦ { l with failed := l.failed.push name }

/-- A deterministic pseudo-random element with coefficients in `[-B, B]`. -/
def pseudoElem (F : CycField) (seed B : Nat) : Elem :=
  (Array.range F.deg).map fun i ↦
    let h := (PointSet.hashElem #[Int.ofNat seed, Int.ofNat i]).toNat
    ((h % (2 * B + 1) : Nat) : Int) - B

/-- Arithmetic identities in `ℤ[ζ_n]`. -/
def testArithmetic (log : IO.Ref TestLog) : IO Unit := do
  -- degrees of cyclotomic polynomials
  check log "deg Φ_n = φ(n) for n ≤ 200"
    ((List.range 201).all fun n ↦ n == 0 || (cyclotomic n).size - 1 == totient n)
  check log "Φ_105 has a coefficient -2" ((cyclotomic 105).contains (-2))
  for n in [3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 16, 20, 21, 30, 33, 36, 44, 60, 84, 100] do
    let F := CycField.make n
    let z1 := F.zetaPow 1
    check log s!"n={n}: ζ^n = 1" (F.mul (F.zetaPow (n - 1)) z1 == F.one)
    check log s!"n={n}: ζ ζ⁻¹ = 1" (F.mulZeta (F.mulZetaInv F.one) == F.one)
    -- ∑ ζ^k = 0 (n > 1)
    let s := (Array.range n).foldl (fun (acc : Elem) (k : Nat) ↦ F.add acc (F.zetaPow (Int.ofNat k))) F.zero
    check log s!"n={n}: ∑ ζ^k = 0" (F.isZero s)
    for seed in [1, 2, 3] do
      let a := pseudoElem F seed 50
      let b := pseudoElem F (seed + 100) 50
      let c := pseudoElem F (seed + 200) 50
      check log s!"n={n}: commutativity" (F.mul a b == F.mul b a)
      check log s!"n={n}: associativity" (F.mul (F.mul a b) c == F.mul a (F.mul b c))
      check log s!"n={n}: distributivity" (F.mul a (F.add b c) == F.add (F.mul a b) (F.mul a c))
      check log s!"n={n}: mulZeta = mul by ζ" (F.mulZeta a == F.mul a z1)
      check log s!"n={n}: mulZetaInv = mul by ζ⁻¹" (F.mulZetaInv a == F.mul a (F.zetaPow (-1)))
      check log s!"n={n}: conj is an involution" (F.conj (F.conj a) == a)
      check log s!"n={n}: conj is multiplicative" (F.conj (F.mul a b) == F.mul (F.conj a) (F.conj b))
      check log s!"n={n}: normSq = a conj a" (F.normSq a == F.mul a (F.conj a))
      check log s!"n={n}: normSq is real" (F.isReal (F.normSq a))
      check log s!"n={n}: |ab|² = |a|²|b|²" (F.normSq (F.mul a b) == F.mul (F.normSq a) (F.normSq b))
      for k in F.embeddings do
        for l in F.embeddings do
          let kl := (k * l) % n
          check log s!"n={n}: σ_k σ_l = σ_kl" (F.galois k (F.galois l a) == F.galois kl a)
        check log s!"n={n}: σ_k is multiplicative"
          (F.galois k (F.mul a b) == F.mul (F.galois k a) (F.galois k b))
      -- real basis round trip
      let x := F.normSq a
      match F.toRealBasis x with
      | some bs => check log s!"n={n}: real basis round trip" (F.ofRealBasis bs == x)
      | none => check log s!"n={n}: |a|² has integral real coordinates" false
      check log s!"n={n}: non-real element rejected" ((F.toRealBasis z1).isNone || n ≤ 4)
      -- float evaluation of |a|² agrees with the product of float values
      let (re, im) := F.evalConjF 1 a
      let exact := F.realToSci x 1 10
      let approx := fmtFloat (re * re + im * im) 10
      check log s!"n={n}: |a|² numerically ({exact} vs {approx})"
        (exact.take 6 == approx.take 6 || (F.realBall x F.basePrec).bound < 2 ^ (F.basePrec - 20))
  -- ball arithmetic: π, cos (2π/5) = (√5 - 1)/4 so (4c + 1)² = 5, cos² (π/4) = 1/2
  let p := 200
  let piB := Ball.pi p
  let sc : Int := ((2 ^ p : Nat) : Int)
  check log "π enclosure" ((piB.mid - piB.rad) * 10 ^ 35 > 314159265358979323846264338327950288 * sc
    && (piB.mid + piB.rad) * 10 ^ 35 < 314159265358979323846264338327950289 * sc)
  check log "π enclosure is tight" (piB.rad < 2 ^ 20)
  let (c5, _) := Ball.trigTable p 5
  let t := (c5[1]!.mulInt 4).add (Ball.ofInt p 1)
  check log "(4 cos 72° + 1)² = 5" (Ball.containsRat p (Ball.mul p t t) 5 1)
  let (c8, s8) := Ball.trigTable p 8
  check log "cos² 45° = 1/2" (Ball.containsRat p (Ball.mul p c8[1]! c8[1]!) 1 2)
  check log "sin 315° = -cos 45°" (Ball.containsRat p (c8[1]!.add s8[7]!) 0 1)
  -- certified float tables
  for n in [3, 5, 7, 12, 33, 100] do
    let F := CycField.make n
    check log s!"n={n}: float table error ≤ 2⁻⁵²" (F.trigErr ≤ (1.0 : Float).scaleB (-52))
  -- exact signs that need more than double precision: (√2 - 1)^k for k up to 80
  let F8 := CycField.make 8
  let u := F8.ofRealBasis #[-1, 1]
  let mut x := F8.one
  for k in [1:81] do
    x := F8.mul x u
    check log s!"(√2 - 1)^{k} > 0" (F8.signReal x == some 1)
    check log s!"-(√2 - 1)^{k} < 0" (F8.signReal (F8.neg x) == some (-1))
  -- (√2 - 1)^40 ≈ 4.886e-16, (√2 - 1)^80 ≈ 2.387e-31
  let x40 := (List.range 40).foldl (fun acc _ ↦ F8.mul acc u) F8.one
  check log "(√2 - 1)^40 value" ((F8.realToSci x40 1 6).startsWith "4.88622e-16")
  -- the golden ratio for n = 5: φ = -(ζ² + ζ³), φ² = φ + 1
  let F5 := CycField.make 5
  match namedReal F5 "fund" with
  | .ok phi =>
    check log "φ² = φ + 1 (n = 5)" (F5.mul phi.num phi.num == F5.addInt phi.num 1)
    check log "φ ≈ 1.6180339887" ((F5.realToSci phi.num 1 11).startsWith "1.6180339887")
  | .error e => check log e false
  -- 3 + φ for n = 5 against rationals
  let c5r ← orThrowTest (parseReal F5 "closed")
  check log "3 + φ > 4.618033988749" (RealQ.compare F5 c5r (RealQ.ofRat F5 (4618033988749 / 10 ^ 12)) == some .gt)
  check log "3 + φ < 4.618033988750" (RealQ.compare F5 c5r (RealQ.ofRat F5 (4618033988750 / 10 ^ 12)) == some .lt)
  -- closed forms have the expected values
  for (n, v) in [(5, "4.6180339887"), (10, "2.3819660112"), (8, "2.9289321881"),
      (12, "1.8948822334")] do
    let F := CycField.make n
    let r ← orThrowTest (parseReal F "closed")
    check log s!"closed form for n = {n} ≈ {v}" ((F.realToSci r.num r.den 15).startsWith v)
  -- parsing
  check log "parseRat 2.5e-7" (parseRat "2.5e-7" == some ((25 : Rat) / 10 ^ 8))
  check log "parseRat -3/4" (parseRat "-3/4" == some (-(3 : Rat) / 4))
  check log "parseRat 1.0362" (parseRat "1.0362" == some ((10362 : Rat) / 10000))
where
  orThrowTest {α : Type} [Inhabited α] : Except String α → IO α
    | .ok a => pure a
    | .error e => throw <| IO.userError e

/-- Membership edge cases. -/
def testMembership (log : IO.Ref TestLog) : IO Unit := do
  for n in [5, 7, 8, 12, 20, 33] do
    let F := CycField.make n
    let g2 : RadiusSq := { num := F.ofRealBasis #[5, -2], den := 1 }
    let T := DiskTest.make F g2
    -- b(0) = 1 - ζ⁻¹ lies exactly on the left circle at r = g: |b0 + 1| = |2 - ζ⁻¹| = g
    let b0 := F.addInt (F.neg (F.zetaPow (-1))) 1
    check log s!"n={n}: b(0) on the left boundary at r = g" (T.decide b0 1 == .boundary)
    check log s!"n={n}: a(0) on the right boundary at r = g"
      (T.decide (F.neg b0) (-1) == .boundary)
    -- every rotation image ζ^k (b0 + 1) - 1 is on the same circle
    for k in [0:n] do
      let w := F.addInt (F.mulZetaPow (F.addInt b0 1) k) (-1)
      check log s!"n={n}: rotated boundary point {k}" (T.decide w 1 == .boundary)
    -- just inside and just outside: r² = g² ± 10⁻³⁰
    let tiny : Rat := 1 / 10 ^ 30
    let Tin := DiskTest.make F (RealQ.addRat F g2 tiny)
    let Tout := DiskTest.make F (RealQ.addRat F g2 (-tiny))
    check log s!"n={n}: inside at g² + 1e-30" (Tin.decide b0 1 == .exact true)
    check log s!"n={n}: outside at g² - 1e-30" (Tout.decide b0 1 == .exact false)
    -- the filter agrees with the exact decision on many points
    let mut agree := true
    let mut decided := 0
    for seed in [0:300] do
      let z := pseudoElem F seed 3
      for side in [(1 : Int), -1] do
        match T.decide z side, T.exactDecide z side with
        | .filter b, .exact b' => if b != b' then agree := false else decided := decided + 1
        | .filter _, _ => agree := false
        | _, _ => pure ()
    check log s!"n={n}: float filter agrees with exact decisions ({decided})" (agree && decided > 0)

/-- Known facts about orbits. -/
def testOrbits (log : IO.Ref TestLog) : IO Unit := do
  -- n ∈ {3, 4, 6}: finite orbits at several radii
  for n in [3, 4, 6] do
    let F := CycField.make n
    for r in ["1", "3/2", "2", "5/2", "3", "touch"] do
      let r2 ← match parseRadiusSq F (if r == "touch" then some r else none)
          (if r == "touch" then none else some r) with
        | .ok x => pure x
        | .error e => throw <| IO.userError e
      for start in ["0", "pow:1", "b0"] do
        let z ← match parsePoint F start with
          | .ok z => pure z
          | .error e => throw <| IO.userError e
        let res ← orbit (DiskTest.make F r2) z { cap := 200000, conj := false }
        check log s!"n={n}, r={r}, start={start}: finite ({res.size})" res.complete
  -- n = 5 below r_c² = 3 + φ: finite and growing
  let F5 := CycField.make 5
  let mut prev := 0
  for e in [10, 30, 100] do
    let r2 ← match parseReal F5 s!"closed-1/{e}" with
      | .ok x => pure x
      | .error e => throw <| IO.userError e
    let res ← orbit (DiskTest.make F5 r2) F5.zero { cap := 3000000, conj := false }
    check log s!"n=5, r² = 3 + φ - 1/{e}: finite ({res.size})" res.complete
    check log s!"n=5, r² = 3 + φ - 1/{e}: larger than before" (res.size > prev)
    prev := res.size
  -- at r² = 3 + φ the origin's orbit exceeds the cap
  match parseReal F5 "closed" with
  | .ok r2 =>
    let res ← orbit (DiskTest.make F5 r2) F5.zero { cap := 2000000, conj := false }
    check log "n=5, r² = 3 + φ: origin orbit reaches the cap of 2·10⁶" (!res.complete)
  | .error e => check log e false
  -- below the touching radius the origin's orbit has 2n - 1 points
  for n in [5, 7, 12, 33] do
    let F := CycField.make n
    match parseReal F "touch-1/1000000" with
    | .ok r2 =>
      let res ← orbit (DiskTest.make F r2) F.zero { cap := 100000, conj := false }
      check log s!"n={n}: 2n - 1 points just below g ({res.size})"
        (res.complete && res.size == 2 * n - 1)
    | .error e => check log e false
  -- serial and parallel searches agree
  let F7 := CycField.make 7
  match parseReal F7 "touch+1/100" with
  | .ok r2 =>
    let T := DiskTest.make F7 r2
    let a ← orbit T F7.zero { cap := 300000, threads := 1 }
    let b ← orbit T F7.zero { cap := 300000, threads := 4 }
    check log s!"serial and parallel agree ({a.size}, {b.size})"
      (a.size == b.size && a.complete == b.complete && a.generations == b.generations)
  | .error e => check log e false
  -- the threshold sweep agrees with direct orbit searches at its thresholds
  for n in [5, 8, 12] do
    let F := CycField.make n
    let res ← sweep F F.zero { cap := 20000 }
    let mut ok := true
    let ths := res.thresholds
    for i in [0:min ths.size 40] do
      let th := ths[i]!
      if th.size < 20000 then
        let o ← orbit (DiskTest.make F { num := th.value, den := 1 }) F.zero
          { cap := 20000, conj := false }
        if !(o.complete && o.size == th.size) then ok := false
    check log s!"n={n}: sweep sizes equal orbit sizes at the thresholds" (ok && ths.size > 3)
    -- thresholds increase strictly
    let mut incr := true
    for i in [1:ths.size] do
      if F.compareReal ths[i - 1]!.value ths[i]!.value != some .lt then incr := false
    check log s!"n={n}: thresholds strictly increase" incr
  -- storage widens instead of overflowing
  let F := CycField.make 7
  let mut s := PointSet.empty F.deg 1
  let pts := #[F.zero, F.ofInt 100, F.ofInt 200, F.ofInt (-40000), F.ofInt (2 ^ 40), F.ofInt 5]
  for z in pts do
    match s.insert z with
    | .added t => s := t
    | _ => pure ()
  check log "storage widened to 8 bytes" (s.width == 8 && s.widenings == 3)
  check log "stored points survive widening" (pts.all s.contains && s.size == pts.size)
  check log "2^70 overflows loudly"
    (match s.insert (F.ofInt (2 ^ 70)) with | .overflow _ => true | _ => false)

/-- Run all self-tests; returns the process exit code. -/
def runSelfTests : IO UInt32 := do
  let log ← IO.mkRef ({} : TestLog)
  let t0 ← IO.monoMsNow
  testArithmetic log
  testMembership log
  testOrbits log
  let l ← log.get
  let t1 ← IO.monoMsNow
  IO.println s!"self-test: {l.passed} passed, {l.failed.size} failed ({t1 - t0} ms)"
  return if l.failed.isEmpty then 0 else 1

end TDCSGCompute
