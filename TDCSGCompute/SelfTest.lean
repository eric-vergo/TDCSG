/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Group
import TDCSGCompute.Closure
import TDCSGCompute.CertCheck
import TDCSGCompute.RelClosure
import TDCSGCompute.RelCheck
import TDCSGCompute.Validity

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
    let h := ((PointSet.hashElem #[Int.ofNat seed, Int.ofNat i]) &&& 0xFFFFFFF).toNat
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

/-- The per-point conjugate records of `orbit --conj-points`. -/
def testConjPoints (log : IO.Ref TestLog) : IO Unit := do
  let F5 := CycField.make 5
  let ks := F5.embeddings
  -- E = ζ - ζ², σ_2 E = ζ² - ζ⁴ = 1 + ζ + 2ζ² + ζ³, |σ_2 E|² = σ_2 (3 - φ) = 2 + φ
  let e : Elem := #[0, 1, -1, 0]
  match conjData F5 ks 1 e with
  | #[(k, w, _, _, m)] =>
    check log "conjugate record of E: k = 2" (k == 2)
    check log "conjugate record of E: σ_2 E = 1 + ζ + 2ζ² + ζ³" (w == #[1, 1, 2, 1])
    check log "conjugate record of E: |σ_2 E| ≈ √(2 + φ)" (Float.abs (m - 1.9021130) < 1e-6)
    -- 2 + φ = 3 + θ_1 with θ_1 = ζ + ζ⁻¹ = φ - 1
    check log "conjugate record of E: |σ_2 E|² is 2 + φ exactly"
      (F5.toRealBasis (F5.normSq w) == some #[3, 1])
  | _ => check log "conjugate record of E has one embedding" false
  let rec5 := pointRecord F5 ks 1 7 3 e
  check log "point record of E"
    ((rec5.splitOn "\t").take 7 ==
      ["point", "7", "3", "0,1,-1,0", "1.118033989e0", "3.632712640e-1", "2"])
  check log "point record of E: conjugate coefficients" ((rec5.splitOn "\t")[7]? == some "1,1,2,1")
  -- scaled points: the conjugate of w / M has modulus |σ w| / M, with the numerator printed
  match conjData F5 ks 4 e with
  | #[(_, w, _, _, m)] =>
    check log "scaled conjugate record"
      (w == #[1, 1, 2, 1] && Float.abs (4 * m - 1.9021130) < 1e-6)
  | _ => check log "scaled conjugate record has one embedding" false
  -- n = 7: two non-trivial embeddings, conjugates are the exact Galois images
  let F7 := CycField.make 7
  let a := pseudoElem F7 5 20
  let d7 := conjData F7 F7.embeddings 1 a
  check log "n=7: two conjugates per point" (d7.size == 2 && d7.map (·.1) == #[2, 3])
  check log "n=7: conjugates are σ_k" (d7.all fun (k, w, _, _, _) ↦ w == F7.galois k a)
  -- over an orbit, the per-point conjugates reproduce the reported maxima
  match parseReal F5 "closed-1/10" with
  | .ok r2 =>
    let res ← orbit (DiskTest.make F5 r2) F5.zero { cap := 100000 }
    let mut mx : Float := 0
    let mut exactOk := true
    for i in [0:res.size] do
      let z := res.points.get i
      for (k, w, _, _, m) in conjData F5 ks 1 z do
        if m > mx then mx := m
        if w != F5.galois k z then exactOk := false
    let rep := (res.maxConj.find? (·.1 == 2)).map (·.2)
    check log s!"n=5, δ = 1/10: per-point conjugate maximum equals the reported one ({mx})"
      (res.complete && res.size == 1433 && rep == some mx)
    check log "n=5, δ = 1/10: per-point conjugates are exact Galois images" exactOk
    let gen := generationOf res.generations res.size
    let counts := (Array.range res.generations.size).map fun g ↦ (gen.filter (· == g)).size
    check log "generation of each point matches the per-generation counts"
      (counts == res.generations && gen[0]! == 0)
  | .error e => check log e false

/-- Exact results recorded in `notes/engine.md`, re-checked as regression tests. -/
def testKnownResults (log : IO.Ref TestLog) : IO Unit := do
  let parse (F : CycField) (s : String) : IO RadiusSq := match parseReal F s with
    | .ok x => pure x
    | .error e => throw <| IO.userError e
  -- n ≡ 4 (mod 8): exactly n² - 3n + 1 points at r = g, and the next threshold is exactly r₁
  for n in [12, 20, 28, 36, 44] do
    let F := CycField.make n
    let g2 ← parse F "touch"
    let res ← orbit (DiskTest.make F g2) F.zero { cap := 100000, conj := false }
    check log s!"n={n}: n² - 3n + 1 points at r = g ({res.size})"
      (res.complete && res.size == n * n - 3 * n + 1)
    let sw ← sweep F F.zero { cap := 3000000, start2 := some g2, maxSteps := 1 }
    let r1 ← parse F "r1"
    check log s!"n={n}: the next threshold after g² is r₁²"
      (sw.initialSize == n * n - 3 * n + 1 &&
        (sw.thresholds[0]?.map (·.value == r1.num)).getD false)
  -- n = 33 at r = g: 65 089 points
  let F33 := CycField.make 33
  let res ← orbit (DiskTest.make F33 (← parse F33 "touch")) F33.zero { cap := 200000, conj := false }
  check log s!"n=33: 65089 points at r = g ({res.size})" (res.complete && res.size == 65089)
  -- rows of the preliminary table, reproduced exactly at r² = r_c² - δ
  for (n, δ, size) in [(5, "7.36e-2", 9477), (5, "1.52e-2", 112539), (8, "6.13e-2", 16297),
      (8, "2.15e-2", 87247), (12, "1.67e-2", 23813)] do
    let F := CycField.make n
    let res ← orbit (DiskTest.make F (← parse F s!"closed-{δ}")) F.zero { cap := 1000000, conj := false }
    check log s!"n={n}, δ={δ}: {size} points ({res.size})" (res.complete && res.size == size)

/-- Permutation groups, the group computation and the scaled points. -/
def testGroups (log : IO.Ref TestLog) : IO Unit := do
  let parse (F : CycField) (s : String) : IO RadiusSq := match parseReal F s with
    | .ok x => pure x
    | .error e => throw <| IO.userError e
  -- Schreier–Sims on known groups
  let cyc (D : Nat) (cs : List (List Nat)) : Perm := Perm.ofCycles D cs
  let known : List (String × Nat × Array Perm × Nat) := [
    ("S_8", 8, #[cyc 8 [[0, 1]], cyc 8 [[0, 1, 2, 3, 4, 5, 6, 7]]], 40320),
    ("A_9", 9, #[cyc 9 [[0, 1, 2]], cyc 9 [[0, 1, 2, 3, 4, 5, 6, 7, 8]]], 181440),
    ("Frobenius F_21", 7, #[cyc 7 [[0, 1, 2, 3, 4, 5, 6]], cyc 7 [[1, 2, 4], [3, 6, 5]]], 21),
    ("M_11", 11, #[cyc 11 [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]], cyc 11 [[2, 6, 10, 7], [3, 9, 4, 5]]],
      7920),
    ("M_12", 12, #[cyc 12 [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]], cyc 12 [[2, 6, 10, 7], [3, 9, 4, 5]],
      cyc 12 [[0, 11], [1, 10], [2, 5], [3, 7], [4, 8], [6, 9]]], 95040),
    ("C_4 x C_6", 10, #[cyc 10 [[0, 1, 2, 3]], cyc 10 [[4, 5, 6, 7, 8, 9]]], 24),
    ("trivial", 5, #[Perm.one 5], 1)]
  for (name, D, gens, ord) in known do
    check log s!"Schreier–Sims: |{name}| = {ord}" (schreierSimsOrder D gens == some ord)
  -- Schreier–Sims against brute-force closure for pseudo-random pairs on 6 to 8 points
  let mut rng : Rng := ⟨12345⟩
  let mut agreeBF := true
  for t in [0:24] do
    let D := 6 + t % 3
    let mut gs : Array Perm := #[]
    for _ in [0:2] do
      let mut p := Perm.one D
      for i in [0:D] do
        let (j, r') := rng.below (D - i)
        rng := r'
        let (x, y) := (p[i]!, p[i + j]!)
        p := (p.set! i y).set! (i + j) x
      gs := gs.push p
    -- closure by breadth-first search over group elements
    let mut seenG : Std.HashSet Perm := ({} : Std.HashSet Perm).insert (Perm.one D)
    let mut queue : Array Perm := #[Perm.one D]
    let mut head := 0
    while head < queue.size do
      let g := queue[head]!
      head := head + 1
      for s in gs do
        let h := Perm.mul s g
        if !seenG.contains h then
          seenG := seenG.insert h
          queue := queue.push h
    if schreierSimsOrder D gs != some queue.size then agreeBF := false
  check log "Schreier–Sims agrees with brute-force closure (24 groups)" agreeBF
  -- the structural order agrees with Schreier–Sims: two independent alternating groups, a
  -- diagonal copy (equivalent constituent, dropped), and a cyclic constituent
  let a1 := cyc 9 [[0, 1, 2]]
  let b1 := cyc 9 [[0, 1, 2, 3, 4, 5, 6, 7, 8]]
  let a2 := cyc 10 [[0, 1]]
  let b2 := cyc 10 [[1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let relabel (p : Perm) : Perm := (Array.range 9).map fun x ↦ (p[(x + 4) % 9]! + 5) % 9
  let cs := #[Constituent.make #[a1, b1], Constituent.make #[a2.map id, b2],
    Constituent.make #[relabel a1, relabel b1],
    Constituent.make #[cyc 4 [[0, 1, 2, 3]], Perm.one 4]]
  check log "relabelled copy is equivalent" (cs[0]!.equivalent cs[2]!)
  check log "different actions are not equivalent" (!cs[0]!.equivalent cs[1]!)
  let R := structuralOrder cs
  check log s!"structural order of A_9 × (S_10 ⊗ C_4) ({R.order})"
    (R.certified && R.duplicates == 1 && R.order == some (181440 * 3628800 * 2))
  -- the group below r_A: n² (2n - 1)! / 2, for n = 5, 7, 8
  for (n, r) in [(5, "1.02"), (7, "1.02"), (8, "1.06")] do
    let F := CycField.make n
    let r2 := RealQ.ofRat F ((parseRat r).get! ^ 2)
    let rep ← groupOn F r2 (gridSamples F 23 1.2) {}
    let expect := n * n * factorial (2 * n - 1) / 2
    check log s!"n={n}, r={r}: |GG_n(r)| = n²(2n-1)!/2 ({rep.result.order})"
      (rep.result.certified && rep.result.order == some expect)
  -- just above r_A: the structural order equals Schreier–Sims on all constituents, and exceeds
  -- n² (2n - 1)! / 2
  for (n, expect) in [(5, 7144200000000000), (7, 72248994832675942827786240000),
      (8, 122407445020162057231033958400000)] do
    let F := CycField.make n
    let r2 ← parse F "ra+1e-6"
    let (u, D) ← match parsePointQ F "necklace" with
      | .ok x => pure x
      | .error e => throw <| IO.userError e
    let samples := gridSamples F 11 1.6 ++ cloudAround F 100000007 2 u D ++
      cloudAround F 100000007 2 (F.conj u) D
    let rep ← groupOn F r2 samples {}
    check log s!"n={n}, r² = r_A² + 1e-6: order {expect} ({rep.result.order})"
      (rep.result.certified && rep.result.order == some expect)
    -- direct Schreier–Sims on the same constituents
    let mut tests : Std.HashMap Nat DiskTest := {}
    let mut S : ConstituentSet := {}
    for (M, w) in samples do
      let T := match tests[M]? with
        | some T => T
        | none => DiskTest.makeScaled F r2 M
      tests := tests.insert M T
      let o ← actionOrbit T M w 100000
      if o.complete && o.generic && o.pts.size > 1 then
        S := (S.insert (Constituent.make #[o.a, o.b])).1
    let offs := S.items.foldl (fun a C ↦ a.push (a.back! + C.deg)) #[0]
    let gens := (Array.range 2).map fun k ↦ Id.run do
      let mut p : Perm := #[]
      for i in [0:S.items.size] do
        for x in S.items[i]!.gens[k]! do
          p := p.push (x + offs[i]!)
      return p
    check log s!"n={n}: structural order = Schreier–Sims order"
      (schreierSimsOrder offs.back! gens == some expect)
  -- points with denominators: the triple point lies on the three circles at r = r_A
  for n in [5, 7, 8, 12] do
    let F := CycField.make n
    let ra ← parse F "ra"
    match parsePointQ F "necklace" with
    | .ok (u, D) =>
      let T := DiskTest.makeScaled F ra D
      check log s!"n={n}: the triple point is on both circles at r_A"
        (T.decide u (D : Int) == .boundary && T.decide u (-(D : Int)) == .boundary)
      let aOne := F.addInt (F.smul 2 (F.zetaPow (-1))) (-1)
      let w := F.sub u (F.smul D aOne)
      check log s!"n={n}: the triple point is at distance r_A from a(1)"
        (F.normSq w == F.smul (D * D) ra.num || F.smul ra.den (F.normSq w) == F.smul (D * D) ra.num)
    | .error e => check log e false
    let x := pseudoElem F 5 9
    match F.normAdj x with
    | some (adj, N) => check log s!"n={n}: x · adj x = N(x)" (F.mul x adj == F.ofInt N)
    | none => check log s!"n={n}: normAdj" false
  -- scaled orbits and sweeps agree with integral ones
  for n in [5, 8, 12] do
    let F := CycField.make n
    let r2 ← parse F "touch+1/100"
    let o1 ← orbit (DiskTest.make F r2) F.zero { cap := 100000, conj := false }
    let o7 ← orbit (DiskTest.makeScaled F r2 7) F.zero { cap := 100000, conj := false, scale := 7 }
    let zb := F.addInt (F.neg (F.zetaPow (-1))) 1
    let p1 ← orbit (DiskTest.make F r2) zb { cap := 100000, conj := false }
    let p7 ← orbit (DiskTest.makeScaled F r2 7) (F.smul 7 zb)
      { cap := 100000, conj := false, scale := 7 }
    check log s!"n={n}: scaled orbits have the same sizes ({o1.size}, {p1.size})"
      (o1.size == o7.size && p1.size == p7.size && o1.complete)
    let s1 ← sweep F F.zero { cap := 5000 }
    let s7 ← sweep F F.zero { cap := 5000, scale := 7 }
    check log s!"n={n}: scaled sweep has the same thresholds"
      (s1.thresholds.size == s7.thresholds.size && s1.thresholds.size > 3 &&
        (s1.thresholds.zip s7.thresholds).all fun (x, y) ↦
          F.smul 49 x.value == y.value && y.den == 49 && x.size == y.size)
  -- the circumradius of -1, 1, a(1) is r_A = sec (π/n), and r_A² is an event candidate
  for n in [5, 7, 8, 12] do
    let F := CycField.make n
    let ra ← parse F "ra"
    let aOne := F.addInt (F.smul 2 (F.zetaPow (-1))) (-1)
    let okCirc := match circumcircle F (F.ofInt (-1)) (F.ofInt 1) aOne with
      | some (_, _, rr) => RealQ.compare F rr ra == some .eq
      | none => false
    check log s!"n={n}: circumradius² of -1, 1, a(1) = r_A²" okCirc
    let st0 := GroupState.init F (← parse F "ra-1/100") {} (track := true)
    let st ← st0.add (gridSamples F 11 1.3)
    let cs := (st.centres.toArray.push (F.ofInt 1)).push (F.ofInt (-1))
    let cands ← eventCandidatesOfCentres F cs
      (← parse F "1") (← parse F "ra+1/1000")
    check log s!"n={n}: r_A² is among the event candidates below r_A + 1e-3"
      (cands.any fun c ↦ RealQ.compare F c.r2 ra == some .eq)
  -- rim-vertex sampling: n² (2n - 1)! / 2 just below r_A, and the regression values just above
  for (n, below, above) in [(5, 4536000, "1.7029510e2"), (7, 152562009600, "5.8370846e2"),
      (8, 41845579776000, "2.2174292e2")] do
    let F := CycField.make n
    let (u, D) ← match parsePointQ F "necklace" with
      | .ok x => pure x
      | .error e => throw <| IO.userError e
    let smp := gridSamples F 11 1.6 ++ cloudAround F 100000007 2 u D ++
      cloudAround F 100000007 2 (F.conj u) D ++ cloudAround F 100000007 2 (F.neg u) D
    let (r1, _, c1, _) ← groupFixpoint F (← parse F "ra-1e-6") smp {} 1e-11 10000000000037
    check log s!"n={n}: rim-vertex fixpoint below r_A gives n²(2n-1)!/2 ({r1.result.order})"
      (c1 && r1.result.order == some below)
    let (r2, _, c2, _) ← groupFixpoint F (← parse F "ra+1e-6") smp {} 1e-11 10000000000037
    let lg := (r2.result.log10Order.map (fmtFloat · 8)).getD "-"
    check log s!"n={n}: rim-vertex fixpoint above r_A, log10 |G| = {above} ({lg})"
      (c2 && r2.result.certified && lg == above)
  -- a rational strictly between two thresholds
  let F5 := CycField.make 5
  let sw ← sweep F5 F5.zero { cap := 2000 }
  let mut okBetween := true
  for i in [1:min 30 sw.thresholds.size] do
    let x := RealQ.ofElem sw.thresholds[i - 1]!.value
    let y := RealQ.ofElem sw.thresholds[i]!.value
    match rationalBetween F5 x y with
    | some q => if !(RealQ.compare F5 x (RealQ.ofRat F5 q) == some .lt &&
        RealQ.compare F5 (RealQ.ofRat F5 q) y == some .lt) then okBetween := false
    | none => okBetween := false
  check log "rationals strictly between consecutive thresholds" okBetween

/-- A squared radius from a `SPEC` string. -/
def specRadius (F : CycField) (s : String) : IO RadiusSq :=
  match parseReal F s with
  | .ok x => pure x
  | .error e => throw <| IO.userError e

/-- The angle in `[0, 2π)` of the point named by `s` on the circle of radius `√ρ` about `c`,
computed in floating point (an independent numerical reference for the tests). -/
def floatAngle (F : CycField) (rho : Float) (c : Elem) (s : Sym) : Float :=
  let (dx, dy) := F.evalConjF 1 (F.sub s.e c)
  let N := dx * dx + dy * dy
  let h := Float.sqrt (4 * rho / N - 1)
  let sg : Float := if s.plus then 1 else -1
  let x := (dx - sg * h * dy) / 2
  let y := (dy + sg * h * dx) / 2
  let t := Float.atan2 y x
  if t < 0 then t + 2 * 3.141592653589793 else t

/-- The lines of a certificate with one line replaced (`none`: deleted). -/
def editLine (text : String) (i : Nat) (new : Option String) : String :=
  let ls := (text.splitOn "\n").toArray
  let ls := match new with
    | some l => ls.set! i l
    | none => ls.eraseIdxIfInBounds i
  "\n".intercalate ls.toList

/-- Whether the checker rejects a certificate text; also returns its message. -/
def rejects (text : String) : Bool × String :=
  match parseCertificate text >>= checkCertificate with
  | .ok _ => (false, "accepted")
  | .error e => (true, e)

/-- The certificate generator (`TDCSGCompute.Closure`), its exact layer, and the independent
checker (`TDCSGCompute.CertCheck`). -/
def testCertificates (log : IO.Ref TestLog) : IO Unit := do
  -- towers: exact zeros and agreement with floating-point values
  let F8 := CycField.make 8
  let S8 := RealSign.make F8
  check log "tower: √2 √2 - 2 = 0"
    (Tower.sign S8 #[F8.ofInt 2, F8.ofInt 2] #[F8.ofInt (-2), F8.zero, F8.zero, F8.one] == some 0)
  check log "tower: √4 - 2 = 0" (Tower.sign S8 #[F8.ofInt 4] #[F8.ofInt (-2), F8.one] == some 0)
  for n in [3, 4, 5, 6, 7, 8, 10, 12] do
    let F := CycField.make n
    let S := RealSign.make F
    let val (x : Elem) : Float := (F.evalConjF 1 x).1
    let mut agreeReal := true
    let mut agreeTower := true
    let mut decided := 0
    for seed in [0:200] do
      let x := F.sub (F.normSq (pseudoElem F seed 6)) (F.normSq (pseudoElem F (seed + 999) 6))
      if S.sign x != F.signReal x then agreeReal := false
      -- a tower element over two positive radicands
      let r1 := F.addInt (F.normSq (pseudoElem F (seed + 7) 3)) 1
      let r2 := F.addInt (F.normSq (pseudoElem F (seed + 8) 3)) 1
      let cs := (Array.range 4).map fun j ↦
        F.sub (F.normSq (pseudoElem F (seed * 4 + j + 50) 3))
          (F.normSq (pseudoElem F (seed * 4 + j + 90) 3))
      let v := val cs[0]! + val cs[1]! * (val r1).sqrt + val cs[2]! * (val r2).sqrt +
        val cs[3]! * (val r1 * val r2).sqrt
      if v.abs > 1e-6 then
        decided := decided + 1
        if Tower.sign S #[r1, r2] cs != some (if v > 0 then 1 else -1) then agreeTower := false
    check log s!"n={n}: integer sign test agrees with signReal" agreeReal
    check log s!"n={n}: tower signs agree with floating point ({decided})"
      (agreeTower && decided > 100)
  -- the order of points on a circle: filter, exact comparison and float angles agree
  for (n, spec) in [(5, "closed-1/10"), (8, "closed-1/7"), (12, "closed-1/20"), (7, "2.3")] do
    let F := CycField.make n
    let r2 ← specRadius F spec
    let C := CircleCtx.make F r2
    let G : Gen := { FC := FilterCtx.make C, stats := ← IO.mkRef {} }
    let rho := (F.evalConjF 1 r2.num).1 / r2.den.toFloat
    let mut ok := true
    let mut pairs := 0
    for seed in [0:40] do
      let c := pseudoElem F (seed + 300) 4
      let mut pts : Array (Sym × GPt × CircleCtx.ExactPt) := #[]
      for j in [0:30] do
        let s : Sym := ⟨F.add c (pseudoElem F (seed * 100 + j) 2), j % 2 == 0⟩
        if (C.validSym c s).toOption.isSome then
          let gp ← G.mkPt c s
          match C.exactPt c s with
          | .ok ep => pts := pts.push (s, gp, ep)
          | .error _ => ok := false
      for i in [0:pts.size] do
        for j in [0:pts.size] do
          let (si, gi, ei) := pts[i]!
          let (sj, gj, ej) := pts[j]!
          let o ← G.cmp c gi gj
          match C.cmpExact ei ej, C.cmpExact ej ei with
          | .ok o1, .ok o2 =>
            pairs := pairs + 1
            if o != o1 || o2 != o1.swap then ok := false
            let ai := floatAngle F rho c si
            let aj := floatAngle F rho c sj
            if (ai - aj).abs > 1e-9 && o1 != (if ai < aj then .lt else .gt) then ok := false
            if si == sj && o1 != .eq then ok := false
          | _, _ => ok := false
    check log s!"n={n}: filtered, exact and float orders of circle points agree ({pairs} pairs)"
      (ok && pairs > 1000)
  -- known finite cases: n = 3, 4, 6 at several radii
  for (n, spec, circles) in [(3, "2.1", 6), (3, "3.7", 14), (3, "6.1", 16), (4, "2.1", 12),
      (4, "3.7", 12), (4, "6.1", 26), (6, "2.1", 10), (6, "3.7", 18), (6, "6.1", 24)] do
    let F := CycField.make n
    let o ← certify F (← specRadius F spec) {}
    let valid := match o.text with
      | some t => (parseCertificate t >>= checkCertificate).toOption.isSome
      | none => false
    check log s!"n={n}, r² = {spec}: certified with {circles} circles, checker accepts"
      (o.certified && valid && (o.summary.map (·.circles)) == some circles)
  -- n = 5: rows of Table 5.1 of critical-radius-n5.md, and the radius below sec (π/5)
  let F5 := CycField.make 5
  let mut cert910 := ""
  for (spec, circles, arcs, pieces, c4) in [("closed-31/10", 10, 10, 10, 16),
      ("closed-13/5", 54, 64, 112, 60), ("closed-9/10", 466, 952, 2040, 316)] do
    let o ← certify F5 (← specRadius F5 spec) {}
    let rep := match o.text with
      | some t => (parseCertificate t >>= checkCertificate).toOption
      | none => none
    if spec == "closed-9/10" then cert910 := o.text.getD ""
    let S := o.summary
    check log s!"n=5, r² = {spec}: {circles} circles, {arcs} maximal arcs, {pieces} pieces"
      (o.certified && (S.map (·.circles)) == some circles && (S.map (·.arcs)) == some arcs &&
        o.result.stats.pieces == pieces && (S.map (·.c4Endpoints)) == some c4)
    check log s!"n=5, r² = {spec}: the checker accepts with the same counts"
      ((rep.map fun r ↦ (r.circles, r.arcs, r.c4Endpoints)) == some (circles, arcs, c4))
  -- tangencies, a radius above r_c, and r ≤ 1
  for spec in ["closed", "closed-1"] do
    let o ← certify F5 (← specRadius F5 spec) {}
    let isTangent := match o.result.status with | .tangency _ _ => true | _ => false
    check log s!"n=5, r² = {spec}: stops on an exact tangency, not certified"
      (isTangent && !o.certified)
  let oAbove ← certify F5 (← specRadius F5 "closed+1/10") { maxPieces := 20000 }
  let isCap := match oAbove.result.status with | .cap _ => true | _ => false
  check log "n=5, r² = 3 + φ + 1/10 (above r_c): cap reached, not certified"
    (isCap && !oAbove.certified)
  let oSmall ← certify F5 (← specRadius F5 "1/2") {}
  check log "r² = 1/2: refused (the theorem needs r > 1)" (!oSmall.certified)
  -- a triple point: at r = sec (π/n) the circles about -1, 1 and a(1) pass through one point
  for n in [5, 7] do
    let F := CycField.make n
    let r2 ← specRadius F "ra"
    let G : Gen := { FC := FilterCtx.make (CircleCtx.make F r2), stats := ← IO.mkRef {} }
    let res ← closure G {}
    let closed := match res.status with | .closed => true | _ => false
    let S ← summarize G res.store
    check log s!"n={n}, r = sec (π/n): closes; triple-point equalities found exactly \
      ({res.stats.coincidences}); (C4) fails ({S.c4Failures})"
      (closed && res.stats.coincidences > 0 && S.c4Failures > 0)
    let forged ← certificateText G res.store S
    let (rej, msg) := rejects forged
    check log s!"n={n}, r = sec (π/n): the checker rejects the arcs ({msg})"
      (rej && msg.startsWith "(C4)")
  -- tampering with the certificate at δ = 9/10
  let ls := (cert910.splitOn "\n").toArray
  let arcIdx := (Array.range ls.size).filter fun i ↦ ls[i]!.startsWith "arc "
  let fullIdx := (Array.range ls.size).filter fun i ↦ ls[i]!.startsWith "full "
  let r2Idx := (Array.range ls.size).filter fun i ↦ ls[i]!.startsWith "r2 "
  check log "the δ = 9/10 certificate is accepted untouched" (!(rejects cert910).1)
  let mid := arcIdx[arcIdx.size / 2]!
  let words (i : Nat) : Array String := ((ls[i]!.splitOn " ").filter (!·.isEmpty)).toArray
  let w := words mid
  let flip (s : String) : String := if s == "+" then "-" else "+"
  let tampered : List (String × String) := [
    ("delete an arc", editLine cert910 mid none),
    ("delete another arc", editLine cert910 arcIdx[3]! none),
    ("delete a boundary circle", editLine cert910 fullIdx[0]! none),
    ("flip the side of an endpoint",
      editLine cert910 mid (some (" ".intercalate (w.set! 5 (flip w[5]!)).toList))),
    ("move an endpoint to another intersection point",
      editLine cert910 mid (some (" ".intercalate (w.set! 4 w[2]! |>.set! 5 (flip w[3]!)).toList))),
    ("replace an endpoint by that of another arc",
      let w' := words arcIdx[arcIdx.size / 2 + 1]!
      editLine cert910 mid (some (" ".intercalate (w.set! 4 w'[4]! |>.set! 5 w'[5]!).toList))),
    ("duplicate an arc", editLine cert910 mid (some (ls[mid]! ++ "\n" ++ ls[mid]!))),
    ("change the radius (δ = 9/10 to 4/5)",
      let rw := words r2Idx[0]!
      let num := (rw[1]!.splitOn ",").toArray
      let num := num.set! 0 (toString ((num[0]!.toInt?.getD 0) + 1))
      editLine cert910 r2Idx[0]! (some s!"r2 {",".intercalate num.toList} / {rw[3]!}")),
    ("change the summary", cert910.replace "c4-endpoints 316" "c4-endpoints 317"),
    ("truncate the file", editLine cert910 (ls.size - 2) none)]
  for (what, t) in tampered do
    let (rej, msg) := rejects t
    check log s!"tampered certificate rejected: {what} ({msg})" rej
  -- a small change of the radius keeps the combinatorics: the same arcs are the certificate at
  -- δ = 899/1000, as the generator confirms there
  let rw := words r2Idx[0]!
  let num := (rw[1]!.splitOn ",").toArray.map fun t ↦ toString ((t.toInt?.getD 0) * 100)
  let num := num.set! 0 (toString ((num[0]!.toInt?.getD 0) + 1))
  let moved := editLine cert910 r2Idx[0]! (some s!"r2 {",".intercalate num.toList} / 1000")
  let o899 ← certify F5 (← specRadius F5 "closed-899/1000") {}
  let body (t : String) : List String :=
    (t.splitOn "\n").filter fun l ↦ l.startsWith "arc " || l.startsWith "full "
  check log "δ = 9/10 → 899/1000: same arcs as the generator's certificate there, accepted"
    (!(rejects moved).1 && (o899.text.map body) == some (body cert910))

/-- Whether the relative checker rejects a certificate text; also returns its message. -/
def rejectsRel (text : String) (threads : Nat := 1) : Bool × String :=
  match parseRelative text >>= (checkRelative · threads) with
  | .ok _ => (false, "accepted")
  | .error e => (true, e)

/-- Relative certificates: critical points, the window geometry, the exact disk test, the n = 5
closure at `r_c` with the largest window of `sharp-lower-bound-combined.md`, and tamperings. -/
def testRelative (log : IO.Ref TestLog) : IO Unit := do
  -- critical points at r_c (Lemma 2.1 of the note for n = 5; 32 points in 8 classes for n = 8)
  for (n, norms, crit, classes) in [(5, 20, 38, 10), (8, 16, 32, 8), (10, 20, 38, 10),
      (12, 24, 48, 12)] do
    let F := CycField.make n
    let r2 ← specRadius F "closed"
    let ws := (latticeOfNorm F r2).toOption.getD #[]
    let cp := (criticalPoints F r2).toOption.getD #[]
    let C := CircleCtx.make F r2
    let cp' := (RelChecker.critPoints C).toOption.getD #[]
    check log s!"n={n}: {norms} lattice elements of norm r_c², {crit} critical points in \
      {classes} classes; the checker's enumeration agrees"
      (ws.size == norms && cp.size == crit && (sortDedup (cp.map (symCanonical F))).size == classes
        && sortDedup cp' == cp)
  -- latticeOfNorm against a brute-force search
  for (n, spec) in [(5, "closed"), (5, "5"), (8, "closed"), (12, "closed"), (4, "13")] do
    let F := CycField.make n
    let r2 ← specRadius F spec
    let ws := (latticeOfNorm F r2).toOption.getD #[]
    let mut brute := #[]
    let B : Int := 7
    let d := F.deg
    let total := (2 * B.toNat + 1) ^ d
    for t in [0:total] do
      let mut x : Array Int := #[]
      let mut rest := t
      for _ in [0:d] do
        x := x.push ((rest % (2 * B.toNat + 1) : Nat) - B)
        rest := rest / (2 * B.toNat + 1)
      if F.smul (r2.den : Int) (F.normSq x) == r2.num then brute := brute.push x
    check log s!"n={n}, r² = {spec}: latticeOfNorm agrees with a search over [-7, 7]^{d} \
      ({brute.size} elements)" (sortDedup ws == sortDedup brute)
  -- the exact disk test against floating point
  for n in [5, 8, 12] do
    let F := CycField.make n
    let r2 ← specRadius F "closed"
    let C := CircleCtx.make F r2
    let rho := (F.evalConjF 1 r2.num).1 / r2.den.toFloat
    let mut ok := true
    let mut tested := 0
    for seed in [0:300] do
      let c := pseudoElem F seed 3
      let e := pseudoElem F (seed + 1000) 3
      let z := pseudoElem F (seed + 2000) 3
      let t := pseudoElem F (seed + 3000) 4
      let tr : RadiusSq := { num := F.add t (F.conj t), den := 3 }
      if c == e || (C.gapSign c e).toOption != some 1 then continue
      for plus in [false, true] do
        let s : Sym := ⟨e, plus⟩
        let (cx, cy) := F.evalConjF 1 c
        let a := floatAngle F rho c s
        let (px, py) := (cx + Float.sqrt rho * Float.cos a, cy + Float.sqrt rho * Float.sin a)
        let (zx, zy) := F.evalConjF 1 z
        let tv := (F.evalConjF 1 tr.num).1 / 3
        let fv := tv - ((px - zx) * (px - zx) + (py - zy) * (py - zy))
        match C.diskSign c s z tr with
        | .ok v =>
          tested := tested + 1
          if fv.abs > 1e-9 && v != (if fv > 0 then 1 else -1) then ok := false
        | .error _ => ok := false
    check log s!"n={n}: diskSign agrees with floating point ({tested} points)" (ok && tested > 100)
  -- the window geometry: the shape (0,2,-1,0) of Table 5.1, and a shape that overlaps
  let F5 := CycField.make 5
  let C5 := CircleCtx.make F5 (← specRadius F5 "closed")
  let w1 : Elem := #[0, 2, -1, 0]
  match WindowSet.make C5 w1 >>= WindowSet.withBound C5 with
  | .ok WS =>
    let corners := (windowCorners C5 WS.shape).toOption.getD #[]
    check log "n=5, w = (0,2,-1,0): 4 disks, 8 corners, 38 disjoint windows, ρ̄ ∈ (0.2924, 0.2925)"
      (WS.shape.size == 4 && corners.size == 8 &&
        (windowsDisjoint C5 WS).toOption == some (true, 703) &&
        WS.rhoNum * 10000 > 2924 * 65536 && WS.rhoNum * 10000 < 2925 * 65536)
  | .error _ => check log "n=5, w = (0,2,-1,0): window set" false
  check log "n=5, w = (0,1,0,0): overlapping windows are detected"
    (match WindowSet.make C5 #[0, 1, 0, 0] >>= fun WS ↦ windowsDisjoint C5 WS with
      | .ok (false, _) => true
      | _ => false)
  check log "a zero window shape and |w| ≥ r are refused"
    ((WindowSet.make C5 F5.zero).toOption.isNone &&
      (WindowSet.make C5 #[3, 0, 0, 0]).toOption.isNone)
  -- n = 5 at r_c with the window (0,2,-1,0): Table 5.1 of sharp-lower-bound-combined.md
  let o ← certifyRelative F5 C5.r2 w1 {}
  let S := o.summary
  let K := o.coinc
  check log "n=5, r_c, w = (0,2,-1,0): closes with 3 442 circles and 5 614 maximal arcs modulo \
    ±z, ±z̄ (plus one full boundary circle), 13 692 and 22 230 in all"
    (o.text.isSome && (S.map (·.canonCircles)) == some 3442 && (S.map (·.canonArcs)) == some 5615
      && (S.map (·.circles)) == some 13692 && (S.map (·.arcs)) == some 22230)
  check log "n=5, r_c, w = (0,2,-1,0): 8 tangencies to ∂D_p, all at critical points"
    (o.result.tangencies.size == 8 && o.tangentAtCritical == 8)
  check log "n=5, r_c, w = (0,2,-1,0): exact coincidences found, none in the bulk"
    (match K with
      | some K => K.records > 0 && K.inBulk == 0 && K.nonLattice == 0
      | none => false)
  -- the symmetric mode: one circle per orbit, the same K'
  let oS ← certifyRelative F5 C5.r2 w1 {} (sym := true)
  check log "n=5, r_c, w = (0,2,-1,0), symmetric mode: the same counts"
    (oS.text.isSome && (oS.summary.map fun S ↦ (S.circles, S.arcs, S.canonCircles, S.canonArcs))
      == some (13692, 22230, 3442, 5615))
  let cert5 := oS.text.getD ""
  match parseRelative cert5 >>= checkRelative with
  | .ok rep =>
    check log "n=5, r_c, w = (0,2,-1,0): the checker accepts the symmetric certificate, \
      13 692 circles and 22 230 arcs in all"
      (rep.canonCircles == 3442 && rep.circles == 13692 && rep.arcs == 22230)
  | .error e => check log s!"n=5, r_c, w = (0,2,-1,0): the checker accepts ({e})" false
  -- shrinking the window: the boundary of the smaller windows is not in K'
  let shrunk := cert5.replace "window 0,2,-1,0" "window 5,-1,4,0"
  let (rejS, msgS) := rejectsRel shrunk
  check log s!"tampered relative certificate rejected: a smaller window ({msgS})" rejS
  let unsym := cert5.replace "symmetric\n" ""
  let (rejU, msgU) := rejectsRel unsym
  check log s!"tampered relative certificate rejected: the symmetric line removed ({msgU})" rejU
  -- a small case for tamperings: n = 6, r² = 13, w = (2, 2)
  let F6 := CycField.make 6
  let o6 ← certifyRelative F6 (← specRadius F6 "13") #[2, 2] {}
  let cert6 := o6.text.getD ""
  check log "n=6, r² = 13, w = (2,2): 22 windows, closes with 215 circles and 536 arcs, accepted"
    ((o6.summary.map (·.arcs)) == some 536 && o6.WS.crit.size == 22 && !(rejectsRel cert6).1)
  let ls := (cert6.splitOn "\n").toArray
  let idx (pre : String) := (Array.range ls.size).filter fun i ↦ ls[i]!.startsWith pre
  let arcIdx := idx "arc "
  let critIdx := idx "critical "
  let fullIdx := idx "full "
  let r2Idx := idx "r2 "
  let words (i : Nat) : Array String := ((ls[i]!.splitOn " ").filter (!·.isEmpty)).toArray
  let flip (x : String) : String := if x == "+" then "-" else "+"
  let mid := arcIdx[arcIdx.size / 2]!
  let w := words mid
  -- an arc on a window circle (its centre is P + v for a critical point P)
  let winArc := arcIdx.find? fun i ↦
    let c := (parseVec 2 (words i)[1]!).toOption.getD #[]
    o6.WS.centres.any (·.contains c)
  let tampered : List (String × String) := [
    ("delete an arc", editLine cert6 mid none),
    ("delete an arc on a window circle", editLine cert6 (winArc.getD mid) none),
    ("delete a boundary circle", editLine cert6 fullIdx[0]! none),
    ("flip the side of an endpoint",
      editLine cert6 mid (some (" ".intercalate (w.set! 5 (flip w[5]!)).toList))),
    ("move an endpoint to another intersection point",
      editLine cert6 mid (some (" ".intercalate (w.set! 4 w[2]! |>.set! 5 (flip w[3]!)).toList))),
    ("replace an endpoint by that of another arc",
      let w' := words arcIdx[arcIdx.size / 2 + 1]!
      editLine cert6 mid (some (" ".intercalate (w.set! 4 w'[4]! |>.set! 5 w'[5]!).toList))),
    ("drop a critical point", editLine cert6 critIdx[3]! none),
    ("add a point that is not critical", editLine cert6 critIdx[0]! (some "critical 0,0")),
    ("list a critical point twice", editLine cert6 critIdx[0]! (some (ls[critIdx[0]!]! ++ "\n" ++
      ls[critIdx[0]!]!))),
    ("an overlapping window", cert6.replace "window 2,2" "window 0,1"),
    ("the windows removed", cert6.replace "window 2,2" "window 0,0"),
    ("change the radius", editLine cert6 r2Idx[0]! (some "r2 14,0 / 1")),
    ("change the summary", cert6.replace "arcs 536" "arcs 537"),
    ("truncate the file", editLine cert6 (ls.size - 2) none)]
  for (what, t) in tampered do
    let (rej, msg) := rejectsRel t
    check log s!"tampered relative certificate rejected: {what} ({msg})" rej
  -- n = 6 in the symmetric mode: accepted with the same totals; a non-canonical circle and a
  -- deleted arc are rejected
  let o6s ← certifyRelative F6 (← specRadius F6 "13") #[2, 2] {} (sym := true)
  let cert6s := o6s.text.getD ""
  check log "n=6, r² = 13, symmetric: accepted with 215 circles and 536 arcs in all"
    (match parseRelative cert6s >>= checkRelative with
      | .ok rep => rep.circles == 215 && rep.arcs == 536
      | .error _ => false)
  let ls6 := (cert6s.splitOn "\n").toArray
  let arc6 := (Array.range ls6.size).filter fun i ↦ ls6[i]!.startsWith "arc "
  let nonCanon := arc6.find? fun i ↦
    let w := ((ls6[i]!.splitOn " ").filter (!·.isEmpty)).toArray
    let c := (parseVec 2 w[1]!).toOption.getD #[]
    symApply F6 1 c != c
  match nonCanon with
  | some i =>
    let w := ((ls6[i]!.splitOn " ").filter (!·.isEmpty)).toArray
    let c := (parseVec 2 w[1]!).toOption.getD #[]
    let (c', a', b') := symArc F6 1 c ⟨(parseVec 2 w[2]!).toOption.getD #[], w[3]! == "+"⟩
      ⟨(parseVec 2 w[4]!).toOption.getD #[], w[5]! == "+"⟩
    let sg (x : Sym) := if x.plus then "+" else "-"
    let moved := editLine cert6s i (some s!"arc {elemToString c'} {elemToString a'.e} {sg a'} \
      {elemToString b'.e} {sg b'}")
    let (rej, msg) := rejectsRel moved
    check log s!"tampered symmetric certificate rejected: an arc moved to a non-canonical circle \
      ({msg})" rej
  | none => check log "n=6 symmetric: an arc on a circle with trivial stabiliser" false
  let (rejD, msgD) := rejectsRel (editLine cert6s arc6[arc6.size / 2]! none)
  check log s!"tampered symmetric certificate rejected: delete an arc ({msgD})" rejD
  -- no windows: the symmetric closure is the cut set K(r); at δ = 1/10 it has the counts of the
  -- ordinary engine (and 12 715 circles, 49 838 arcs modulo ±z, ±z̄, as in rcut.c), and
  -- (C1)–(C4) hold
  let o10 ← certifyRelative F5 (← specRadius F5 "closed-1/10") F5.zero {} (sym := true)
  check log "n=5, δ = 1/10, no windows, symmetric: 50 714 circles, 198 470 arcs (12 715 and \
    49 839 canonical), no tangency, (C4) holds"
    ((o10.summary.map fun S ↦ (S.circles, S.arcs, S.canonCircles, S.canonArcs)) ==
      some (50714, 198470, 12715, 49839) && o10.result.tangencies.isEmpty && o10.c4.2 == 0)
  check log "n=5, δ = 1/10, no windows, symmetric: the relative checker accepts, (C3), (C4) hold"
    (match parseRelative (o10.text.getD "") >>= (checkRelative · 4) with
      | .ok rep => rep.circles == 50714 && rep.arcs == 198470 && rep.tangentCircles == 0 &&
          rep.c4Failures == 0 && rep.c4Endpoints > 0
      | .error _ => false)
  -- the interval of validity of the δ = 9/10 certificate of n = 5: the first event is the
  -- tangency of the circle about -3 + 2ζ to ∂D_R at ρ₁ = 7 - 2φ; the same arcs are accepted just
  -- below ρ₁ and rejected just above
  let o910 ← certify F5 (← specRadius F5 "closed-9/10") {}
  match parseCertificate (o910.text.getD "") >>= (validityInterval · 1) with
  | .ok rep =>
    match rep.least with
    | some e =>
      let rho1 : RadiusSq := { num := F5.ofInt 7 |> F5.add (F5.smul 2 #[0, 0, 1, 1]), den := 1 }
      let same := e.kind == "disk" && F5.smul (rho1.den : Int) e.num == F5.mul rho1.num e.den
      let ls := ((o910.text.getD "").splitOn "\n").toArray
      let r2i := (Array.range ls.size).filter fun i ↦ ls[i]!.startsWith "r2 "
      -- 7 - 2φ ≈ 3.763932; test at 3.7639 (below) and 3.764 (above)
      let at_ (num : Int) (den : Nat) := editLine (o910.text.getD "") r2i[0]!
        (some s!"r2 {num},0,0,0 / {den}")
      check log "n=5, δ = 9/10: the interval of validity ends at the tangency ρ₁ = 7 - 2φ; the \
        arcs are accepted at r² = 3.7639 and rejected at 3.764"
        (same && rep.coincidentAtStart == 0 && !(rejects (at_ 37639 10000)).1 &&
          (rejects (at_ 3764 1000)).1)
    | none => check log "n=5, δ = 9/10: an event is found" false
  | .error e => check log s!"n=5, δ = 9/10: interval of validity ({e})" false

/-- Run all self-tests; returns the process exit code. -/
def runSelfTests : IO UInt32 := do
  let log ← IO.mkRef ({} : TestLog)
  let t0 ← IO.monoMsNow
  testArithmetic log
  testMembership log
  testOrbits log
  testConjPoints log
  testKnownResults log
  testGroups log
  testCertificates log
  testRelative log
  let l ← log.get
  let t1 ← IO.monoMsNow
  IO.println s!"self-test: {l.passed} passed, {l.failed.size} failed ({t1 - t0} ms)"
  return if l.failed.isEmpty then 0 else 1

end TDCSGCompute
