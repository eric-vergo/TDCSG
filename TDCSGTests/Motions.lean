/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures

/-!
# The exact arrival checks of the animations refuse wrong moves

The animations of chapters 1, 2, 3, 6 and 7 check every declared turn and slide exactly
(`TDCSGFigures.allArrive`): the move, applied in `ℚ(ζ₅)` or `ℚ(√5)²` to the anchors of the actors of
one key, must give those of the next. Each theorem here changes one thing, a centre, a fraction of
a turn, a vector of a slide or the place of an actor, and proves, by `decide +kernel`, that the
check then fails. The figures' own statements are on the page of the figures' theorems
(`TDCSGFigures.generatorStep_keys` and the other `_keys` theorems).

`engineErrors` lists the errors PILean's engine reports for the animations of the site, wide and
narrow; the test driver (`TDCSGTests.Main`, run by `lake test`) runs it compiled and fails when the
list is not empty, so that a drawn move that misses its key stops the gate. A `#guard` line requires
that every caption and title has all its characters in PILean's lettering, which draws them on the
contact sheets and in print. The other `#guard` lines pin the captions of the animations whose captions are built from
their data, word for word, by evaluation: the kernel does not reduce the string functions these
captions are built with, so the theorems state the caption functions and these lines their texts. -/

namespace TDCSGTests.Motions

open PILean PILean.Exact TDCSGFigures TDCSGFigures.Early

/-- The generator's turn about `+1` instead of `-1` misses its key. -/
theorem generator_wrongCentre :
    allArrive 2 (fun k => if k == 0 then [("disk", .turn ⟨ZetaFrac.ofZeta rightCentre, -1 / 5⟩)]
      else generatorMoves k) generatorActors = false := by
  decide +kernel

/-- The generator's turn counterclockwise instead of clockwise misses its key. -/
theorem generator_wrongDirection :
    allArrive 2 (fun k => if k == 0 then [("disk", .turn ⟨ZetaFrac.ofZeta leftCentre, 1 / 5⟩)]
      else generatorMoves k) generatorActors = false := by
  decide +kernel

/-- A sample of the left disk drawn somewhere else after the turn is caught. -/
theorem generator_displaced :
    allArrive 2 generatorMoves (fun k => if k == 1 then
      [⟨"disk", [ZetaFrac.ofZeta aZero, ZetaFrac.ofZeta leftCentre, ZetaFrac.ofZeta aZero,
        ZetaFrac.ofZeta origin]⟩, ⟨"outside", fixedSamples.map ZetaFrac.ofZeta⟩]
      else generatorActors k) = false := by
  decide +kernel

/-- The generator's turn declared as `4/5`, the same turn the other way round plus a full turn,
arrives exactly, since the arrival check works modulo a full turn; the declared fractions, which
`generatorStep_keys` writes out as `[-1/5]`, tell it apart. -/
theorem generator_fourFifths :
    let moves := fun k =>
      if k == 0 then [("disk", ExactMove.turn ⟨ZetaFrac.ofZeta leftCentre, 4 / 5⟩)]
      else generatorMoves k
    allArrive 2 moves generatorActors = true ∧ (declaredTurns 2 moves == [-1 / 5]) = false := by
  decide +kernel

/-- The word `a b b a` with the second letter turning about `-1` misses its key. -/
theorem steps_wrongCentre :
    allArrive 4 (fun k => if k == 1 then
      [("point", .turn ⟨ZetaFrac.ofZeta leftCentre, -1 / 5⟩), ("pivot-right", .appear),
        ("trail-1", .appear), ("pivot-left", .vanish)] else stepMoves k) stepActors = false := by
  decide +kernel

/-- A turn declared for the last letter, which does not act, is caught. -/
theorem steps_idleLetterTurns :
    allArrive 4 (fun k => if k == 3 then
      [("point", .turn (stepTurn 3)), ("reach", .appear), ("pivot-right", .vanish)]
      else stepMoves k) stepActors = false := by
  decide +kernel

/-- The bar of the jump turned by `2/5` of a turn misses its key. -/
theorem jump_wrongFraction :
    allArrive 2 (fun k => if k == 0 then [("inner", .turn ⟨ZetaFrac.ofZeta origin, -2 / 5⟩),
      ("gap", .vanish), ("gap-label", .vanish), ("p-label", .vanish)] else jumpMoves k)
      jumpActors = false := by
  decide +kernel

/-- In the copy of `b`, then `a`, turning `x` first misses its key. -/
theorem disjoint_wrongOrder :
    allArrive 3 (fun k => if k == 0 then
      [("ab-x", .turn (disjointTurnA true)), ("ba-x", .turn (disjointTurnA false))]
      else disjointMoves k) disjointActors = false := by
  decide +kernel

/-- An actor whose anchors are left out is caught: the copy of `a`, then `b` with no anchors for
its moving `x` fails the check. -/
theorem disjoint_emptyAnchors :
    allArrive 3 disjointMoves (fun k => (disjointActors k).map fun a =>
      if a.id == "ab-x" then { a with anchors := [] } else a) = false := by
  decide +kernel

/-- Piece 3 of the interval exchange slid by `2φ - 2` instead of `2φ - 4` misses its key. -/
theorem interval_wrongVector :
    allArrive 4 (fun k => if k == 2 then
      [("piece-3", .slide (phi * rat 2 - rat 2, rat (-1 / 2)))] else intervalMoves k)
      intervalActors = false := by
  decide +kernel

/-- A hop of the orbit by `2φ - 2` where word 3 applies misses its key. -/
theorem orbit_wrongHop :
    allArrive (orbitHops + 1) (fun k => if k == 0 then
      [("hop", .slide (phi * rat 2 - rat 2, rat (-1 / 20))), ("row-0", .appear)]
      else orbitMoves k) orbitActors = false := by
  decide +kernel

/-- The walk's first step slid by `-ζ` instead of `+ζ` misses its key. -/
theorem walk_wrongVector :
    allArrive (Confinement.path.length + 1) (fun k => if k == 0 then
      [("walker", .slide (ZetaFrac.ofZeta (-zeta 1))), ("edge-0", .appear), ("label-1", .appear)]
      else Confinement.walkMoves k) Confinement.walkActors = false := by
  decide +kernel

/-- The crossing's walk slid from `n` straight to the leaf, where the key has it at `(1.512, 0)`,
misses its key. -/
theorem crossing_wrongSlide :
    allArrive 5 (fun k => if k == 0 then
      [("walker", .slide (Levels.zetaFracSub Levels.leafZ Levels.nZ))]
      else Levels.crossMoves k) Levels.crossActors = false := by
  decide +kernel

/-! ### The engine finds no error in any animation of the site -/

/-- The animations of the site, with the names of their files in the site: the declaration's name,
without the name of its module where the module's name begins it (`walkToLeaf`, declared in
`TDCSGFigures.Confinement`). -/
def siteMotions : Array (String × PILean.Plane.MotionPanels) := #[
  ("TDCSGFigures.wordLoop1", wordLoop1),
  ("TDCSGFigures.wordLoop2", wordLoop2),
  ("TDCSGFigures.wordLoop3", wordLoop3),
  ("TDCSGFigures.Lift.framePair", Lift.framePair),
  ("TDCSGFigures.extensionJump", extensionJump),
  ("TDCSGFigures.disjointDisks", disjointDisks),
  ("TDCSGFigures.generatorStep", generatorStep),
  ("TDCSGFigures.wordSteps", wordSteps),
  ("TDCSGFigures.exchangedIntervals", exchangedIntervals),
  ("TDCSGFigures.chordOrbit", chordOrbit),
  ("walkToLeaf", Confinement.walkToLeaf),
  ("TDCSGFigures.orbitRadius", orbitRadius),
  ("lensRadius", Lens.lensRadius),
  ("terminalCrossing", Levels.terminalCrossing)]

/-- The errors PILean's engine reports for the animations of the site and their narrow renditions,
each with the animation's name: every move drawn must land on its next key, every rest show its
still, the writer agree with the baker. The test driver runs this compiled and fails when it is not
empty. -/
def engineErrors : List String :=
  siteMotions.toList.flatMap fun (name, P) =>
    let all := [("", P)] ++ (P.narrow.map fun n => [("-narrow", n)]).getD []
    all.flatMap fun (suffix, Q) =>
      Q.report.errors.toList.map fun e => s!"{name}{suffix}: {e}"

-- Every caption, title and panel title of the animations of the site has all its characters in
-- PILean's lettering, which draws them on the contact sheets and in print.
#guard siteMotions.all fun (_, P) =>
  ((P.captions.toList ++ [P.info.title] ++ P.panels.toList.map (·.title)).all
    fun c => (PILean.Lettering.missing c).isEmpty)

/-! ### The orbits of zero as the radius grows

The orbits of `TDCSGFigures.orbitRadius` come from the exact orbit engine, which the kernel does
not run, so their facts are checked here by evaluation. -/

section OrbitRadius

open TDCSGFigures.OrbitLoop

-- The orbits are computed once. They have 9, 9, 71, 151, 801 and 1000 points; the first five, at
-- r = 1.5, 1.9, 1.95, 2.05 and 2.1, are complete; at R the search was stopped at 1000 points (the
-- orbit there is infinite, `TDCSG.CriticalRadius.infinite_orbit_zero_five`). Each drawn orbit
-- contains the one before it, and the engine decides on which side of each disk every point drawn
-- lies; the groups that appear up to each key are the points of its orbit, each once; every
-- declared appearance and disappearance is the change from one key to the next, and no group of
-- points moves (`allArrive`). The 801 points of the orbit at r = 2.1 are among the first 997
-- points of the search at R, and not all among the first 996. The lines under the disks are
-- written out.
#guard
  let os := figureConfig.orbits
  let within := fun (n : Nat) => (os.getD 4 default).points.all fun p =>
    ((os.getD 5 default).points.extract 0 n).any (·.z == p.z)
  os.map (·.points.size) == #[9, 9, 71, 151, 801, 1000] &&
    os.map (·.complete) == #[true, true, true, true, true, false] &&
    figureConfig.nested os && figureConfig.partitions os && figureConfig.arrives os &&
    within 997 && !within 996 &&
    (List.range 6).map (figureConfig.valueText os) == ["r = 1.5: 9 points", "r = 1.9: 9 points",
      "r = 1.95: 71 points", "r = 2.05: 151 points", "r = 2.1: 801 points",
      "r = R: infinite, the first 1000 shown"]

end OrbitRadius

/-! ### The captions built from data, word for word -/

#guard orbitRadius.captions == #[
  "The orbit of 0 under the two moves at r = 1.5, computed exactly: 9 points. As r grows the \
    closed disks grow and the orbit can only grow: from one radius shown to the next the circles \
    grow and the points the orbit gains fade in. The orbit is exact only at the radii shown.",
  "r = 1.9: the disks are larger, and the orbit is the same 9 points.",
  "r = 1.95: 71 points; the 62 new ones have faded in, and the 9 points of the orbit at r = 1.9 \
    are among them.",
  "r = 2.05: 151 points; the 80 new ones have faded in, and the 71 points of the orbit at \
    r = 1.95 are among them.",
  "r = 2.1: 801 points; the 650 new ones have faded in, and the 151 points of the orbit at \
    r = 2.05 are among them.",
  "r = R = √(3 + φ): the orbit is infinite, and only the first 1000 of its points that a \
    breadth-first search from 0 finds are drawn; the 801 points of the orbit at r = 2.1 are \
    among them."]

#guard Lens.lensRadius.captions == #[
  "The lens of the closed disks |v| ≤ r/2 and |v − u| ≤ r/2 at r = 1.8, with the half-planes \
    Re v ≥ κ − η (dashed edge) and Re v ≥ κ, η = (3 + φ − r²)/16, and v∗ on Re v = κ. The \
    second panel shows the tip enlarged, and above it the margin η between the edges as a bar. \
    The tip lies left of the dashed edge, at least η from it. The circle |v| = r/2 lies left of \
    the dashed edge: no v meets the hypothesis of the lemma.",
  "r = 2: the margin η is smaller, and the tip has moved right; it stays at least η left of the \
    dashed edge. The circle |v| = r/2 lies left of the dashed edge: no v meets the hypothesis \
    of the lemma.",
  "r = 2.08: the margin η is smaller, and the tip has moved right; it stays at least η left of \
    the dashed edge. The circle |v| = r/2 lies left of the dashed edge: no v meets the \
    hypothesis of the lemma.",
  "r = 2.12: the margin η is smaller, and the tip has moved right; it stays at least η left of \
    the dashed edge. The circle |v| = r/2 crosses the dashed edge, and the lens does not.",
  "r = R = √(3 + φ): η = 0, so the dashed edge has reached Re v = κ, and so has the tip: the \
    tip is v∗.",
  "At R the two half-planes are one, Re v ≥ κ, and the tip of the lens is v∗, on its edge. \
    Below R it stays at least η left of the dashed edge."]

#guard chordOrbit.captions == #[
  "The orbit of 0 along the chord at the critical radius: the parameter t of the point tE, \
    −1 ≤ t < 1, one row per return k, from the top. t₀ = 0 lies in piece 3: word 3 applies next.",
  "Return 1: word 3 moved the point by 2φ − 4, to t₁ = 2φ − 4, in piece 1: word 1 applies next.",
  "Return 2: word 1 moved the point by 2φ − 2, to t₂ = 4φ − 6, in piece 3: word 3 applies next.",
  "Return 3: word 3 moved the point by 2φ − 4, to t₃ = 6φ − 10, in piece 2: word 2 applies next.",
  "Return 4: word 2 moved the point by 2φ − 2, to t₄ = 8φ − 12, in piece 3: word 3 applies next.",
  "Return 5: word 3 moved the point by 2φ − 4, to t₅ = 10φ − 16, in piece 3: word 3 applies next.",
  "Return 6: word 3 moved the point by 2φ − 4, to t₆ = 12φ − 20, in piece 2: word 2 applies next.",
  "Return 7: word 2 moved the point by 2φ − 2, to t₇ = 14φ − 22, in piece 3: word 3 applies next.",
  "Return 8: word 3 moved the point by 2φ − 4, to t₈ = 16φ − 26, in piece 3: word 3 applies next.",
  "Return 9: word 3 moved the point by 2φ − 4, to t₉ = 18φ − 30, in piece 1: word 1 applies next.",
  "Return 10: word 1 moved the point by 2φ − 2, to t₁₀ = 20φ − 32, in piece 3: word 3 applies \
    next.",
  "Return 11: word 3 moved the point by 2φ − 4, to t₁₁ = 22φ − 36, in piece 2: word 2 applies \
    next.",
  "Return 12: word 2 moved the point by 2φ − 2, to t₁₂ = 24φ − 38, in piece 3: word 3 applies \
    next.",
  "The returns t₀, …, t₂₄, the last 12 shown at once. Each point lies in the band of the word \
    applied next, which adds 2φ − 2 modulo 2; the rotation is irrational, so the points never \
    repeat."]

#guard Confinement.walkToLeaf.captions == #[
  "A walk in the center graph at r = 2.13, x = 1/5, from the label 0, along a path that a \
    breadth-first search found; the circle marks where the walk is. Each step adds or removes \
    one unit vector eⱼ, and every label lies in the window.",
  "Move 1: + e₁, to (0, 1, 0, 0, 0); n₂ = 0.", "Move 2: − e₂, to (0, 1, −1, 0, 0); n₂ = −1.",
  "Move 3: + e₃, to (0, 1, −1, 1, 0); n₂ = −1.", "Move 4: − e₄, to (0, 1, −1, 1, −1); n₂ = −1.",
  "Move 5: + e₃, to (0, 1, −1, 2, −1); n₂ = −1.", "Move 6: − e₂, to (0, 1, −2, 2, −1); n₂ = −2.",
  "Move 7: + e₁, to (0, 2, −2, 2, −1); n₂ = −2.", "Move 8: − e₂, to (0, 2, −3, 2, −1); n₂ = −3.",
  "Move 9: + e₃, to (0, 2, −3, 3, −1); n₂ = −3.", "Move 10: − e₄, to (0, 2, −3, 3, −2); n₂ = −3.",
  "Move 11: + e₃, to (0, 2, −3, 4, −2); n₂ = −3.", "Move 12: − e₂, to (0, 2, −4, 4, −2); n₂ = −4.",
  "Move 13: + e₁, to n + e₂ = (0, 3, −4, 4, −2): n₂ has fallen from 0 to −4.",
  "Move 14: − e₂, into n = (0, 3, −5, 4, −2): the step crosses the good level −5 of n₂.",
  "n is a leaf: its other candidates n + eₖ, k ≠ 2, lie outside the window (open rings at the \
    ends of dashed spokes).",
  "From the leaf n the only step leads back to n + e₂, as the one-step lemma requires. The \
    labels of the path are numbered 1 to 12 in the order of the walk; labels 13 and 14 are n + e₂ \
    and n."]

end TDCSGTests.Motions
