/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures

/-!
# The exact arrival checks of the animations refuse wrong moves

The animations of chapters 1, 2, 3 and 7 check every declared turn and slide exactly
(`TDCSGFigures.allArrive`): the move, applied in `ℚ(ζ₅)` or `ℚ(√5)²` to the anchors of the actors of
one key, must give those of the next. Each theorem here changes one thing, a centre, a fraction of
a turn, a vector of a slide or the place of an actor, and proves, by `decide +kernel`, that the
check then fails. The figures' own statements are on the page of the figures' theorems
(`TDCSGFigures.generatorStep_keys` and the other `_keys` theorems).

A `#guard` line requires that PILean's engine reports no error for any animation of the site, wide
or narrow, so that a drawn move that misses its key stops the build, and another that every caption
and title has all its characters in PILean's lettering, which draws them on the contact sheets and
in print. The other `#guard` lines pin the captions of the animations whose captions are built from
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
  ("walkToLeaf", Confinement.walkToLeaf)]

-- Every animation of the site, and its narrow rendition, has no error in PILean's engine: every
-- move it draws lands on its next key, every rest shows its still, the writer agrees with the
-- baker. A drawn move that differs from the exact one it is made from stops the build here.
#guard siteMotions.all fun (_, P) =>
  P.report.errors.isEmpty && (P.narrow.map (·.report.errors.isEmpty)).getD true

-- Every caption, title and panel title of the animations of the site has all its characters in
-- PILean's lettering, which draws them on the contact sheets and in print.
#guard siteMotions.all fun (_, P) =>
  ((P.captions.toList ++ [P.info.title] ++ P.panels.toList.map (·.title)).all
    fun c => (PILean.Lettering.missing c).isEmpty)

/-! ### The captions built from data, word for word -/

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
    labels of the path are numbered in the order of the walk."]

end TDCSGTests.Motions
