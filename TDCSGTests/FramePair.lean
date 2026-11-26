/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.FramePairMotion
import TDCSGFigures.Chord

/-!
# The declared moves of the frame pair arrive exactly

For words of the frame pair at `r = 1.95` from `z = 0`, checked by `decide +kernel`: every
declared turn of every step (`TDCSGFigures.Lift.FramePairConfig.frameSteps`), applied exactly in
`ℤ[ζ₅]` to the anchors of the actors that the key figures draw (`FramePairConfig.actorsAt`) in key
`k`, gives their anchors in key `k + 1` (`FramePairConfig.allArrive`), in each panel's own
coordinates. A misplaced actor makes the check fail. Every drawn actor gives back its base title
(`FramePairConfig.baseTitlesRecoverable`, checked by evaluation, since the drawing goes through
floating point). The letters that act are the ones pinned in `TDCSGTests.FrameWords` and
`TDCSGFigures.Lift.wordSummary_word`. This is the exact counterpart of the floating-point arrival
check of an animation; the general statements behind it are `TDCSG.Five.framePicture_genA_genB`
and `TDCSG.Five.halved_genA` with their companions. The animation made from these moves
(`FramePairConfig.motion`) passes the checks of PILean's motion engine for the figure's word and
for `a b a b`, checked by evaluation. The figure's own key data are stated in
`TDCSGFigures.Lift.framePair_keys`, on the page of the figures' theorems.
-/

namespace TDCSGTests.FramePair

open TDCSGFigures TDCSGFigures.Lift TDCSGFigures.Early

/-- The turn factors of the declared fractions: `-1/5` is `ζ⁴`, `1/5` is `ζ`. -/
theorem turnFactor_fifths :
    (turnFactor (-1 / 5) == some (zeta 4)) = true ∧
      (turnFactor (1 / 5) == some (zeta 1)) = true := by
  decide +kernel

/-- `a b a b`: every step arrives; every letter acts. -/
theorem frameSteps_abab :
    ({ word := [.a, .b, .a, .b] } : FramePairConfig).allArrive = true ∧
      (({ word := [.a, .b, .a, .b] } : FramePairConfig).frameSteps.map (·.acts)) =
        [true, true, true, true] := by
  decide +kernel

/-- `a b a b b a b`: every step arrives; the letter `6` does not act (two steps). -/
theorem frameSteps_ababbab :
    ({ word := [.a, .b, .a, .b, .b, .a, .b] } : FramePairConfig).allArrive = true ∧
    (({ word := [.a, .b, .a, .b, .b, .a, .b] } : FramePairConfig).frameSteps.map (·.acts)) =
      [true, true, true, true, true, false, false, true] := by
  decide +kernel

/-- `a a b a a a b b b b b`: every step arrives; the letter `3` does not act (two steps). -/
theorem frameSteps_aabaaabbbbb :
    ({ word := [.a, .a, .b, .a, .a, .a, .b, .b, .b, .b, .b] } : FramePairConfig).allArrive = true ∧
    (({ word := [.a, .a, .b, .a, .a, .a, .b, .b, .b, .b, .b] } : FramePairConfig).frameSteps.map
      (·.acts)) = [true, true, false, false, true, true, true, true, true, true, true, true] := by
  decide +kernel

/-- The inverse letters: the figure's word followed by its inverse arrives at every step. -/
theorem frameSteps_inverse :
    ({ word := word ++ inverseWord word } : FramePairConfig).allArrive = true := by
  decide +kernel

/-- The actors of a frame pair with the right riding disk drawn at the left centre. -/
def misplaced (cfg : FramePairConfig) (p : Panel) (k : Nat) : List Actor :=
  (cfg.actorsAt p k).map fun a =>
    if a.id == "right-disk" then { a with anchors := [(cfg.centresAt k).1] } else a

/-- A misplaced actor fails the check: with the right riding disk drawn at the left centre, the
steps of `a b a b` do not all arrive. -/
theorem misplaced_fails :
    ({ word := [.a, .b, .a, .b] } : FramePairConfig).allArriveWith
      (misplaced { word := [.a, .b, .a, .b] }) = false := by
  decide +kernel

/-- The actors of the figure's word with the ring of each idle letter drawn, in the moving frame,
about the other centre of the pair. -/
def ringElsewhere (p : Panel) (k : Nat) : List Actor :=
  let cfg : FramePairConfig := {}
  (cfg.actorsAt p k).map fun a =>
    if p == .right && a.id.startsWith "idle-" then
      let (l, r) := cfg.centresAt (cfg.keyRef k).state
      { a with anchors := a.anchors.map fun c => if ZetaFrac.same c l then r else l }
    else a

/-- A ring about the wrong centre fails the check of the rings. -/
theorem ringElsewhere_fails :
    ({} : FramePairConfig).ringsPlacedWith ringElsewhere = false := by
  decide +kernel

/-- A word whose turns alternate between the two centres except around its idle letters, at
`r = 2.12`: `a b⁻¹ a b a⁻¹ b⁻¹ a b a⁻¹ b`, with the turn centres marked (`pivotMark`). -/
def pivotWord : FramePairConfig :=
  { word := [.a, .bInv, .a, .b, .aInv, .bInv, .a, .b, .aInv, .b], radius := 53 / 25,
    pivotMark := true }

/-- With the turn centres marked, every step arrives and every turn centre is marked where its
turn turns (`pivotsPlaced`): the letters `3` and `8` do not act, and each of the eight turns gets
a key of its own in which its centre is marked first. -/
theorem frameSteps_pivot :
    pivotWord.allArrive = true ∧ pivotWord.pivotsPlaced = true ∧ pivotWord.keyCount = 21 ∧
      idlePositions pivotWord.r2 pivotWord.word = [3, 8] ∧
      (pivotWord.frameSteps.map (·.phase)).count .pivotShown = 8 := by
  decide +kernel

/-- The actors of `pivotWord` with the ring of each turn centre drawn, in the moving frame, about
the other centre of the pair. -/
def pivotElsewhere (p : Panel) (k : Nat) : List Actor :=
  (pivotWord.actorsAt p k).map fun a =>
    if p == .right && a.id.startsWith "pivot-" then
      let (l, r) := pivotWord.centresAt (pivotWord.keyRef k).state
      { a with anchors := a.anchors.map fun c => if ZetaFrac.same c l then r else l }
    else a

/-- A turn centre marked about the wrong centre fails the check of the marks. -/
theorem pivotElsewhere_fails : pivotWord.pivotsPlacedWith pivotElsewhere = false := by
  decide +kernel

/-- Without the option, no key shows a turn-centre mark, for the figure's word. -/
theorem no_pivots : ({} : FramePairConfig).pivotsPlaced = true := by
  decide +kernel

-- The animations with the turn centres marked, and with the riding disks faint as well, pass every
-- check of PILean's engine; checked by evaluation (the drawing is in floating point).
#guard pivotWord.motion.problems.isEmpty
#guard ({ pivotWord with faintDisks := true }).motion.problems.isEmpty
#guard ({ pivotMark := true } : FramePairConfig).motion.problems.isEmpty

/-- The word strip, an option off on the site, marks the letter of every key, for the frame pair
and for the three words. -/
theorem strip_marks :
    ({ strip := true } : FramePairConfig).stripMarkIds 4 = ["strip-2"] ∧
      ({} : FramePairConfig).stripMarkIds 4 = [] := by
  decide +kernel

-- The marks the strip draws are those `stripMarkIds` names, and the animations with the strip pass
-- every check of PILean's engine; checked by evaluation (the drawing is in floating point).
#guard ({ strip := true } : FramePairConfig).stripMarks
#guard wordStripMarks 1 && wordStripMarks 2 && wordStripMarks 3
#guard ({ strip := true } : FramePairConfig).motion.problems.isEmpty
#guard [1, 2, 3].all fun i => (wordLoopWith i true).problems.isEmpty

-- Every drawn actor of the figure's word gives back its base title. The drawing goes through
-- floating point, which the kernel does not reduce, so this is checked by evaluation when the
-- module is built.
#guard ({} : FramePairConfig).baseTitlesRecoverable

-- The animation of the frame pair passes every check of PILean's engine, with no error and no
-- note, for the figure (`framePair`, and its narrow rendition) and for `a b a b`. The engine's
-- checks are in floating point, so these are checked by evaluation when the module is built.
#guard framePair.report.problems.isEmpty
#guard (framePair.narrow.map (·.report.problems.isEmpty)) == some true
#guard ({ word := [.a, .b, .a, .b] } : FramePairConfig).motion.problems.isEmpty

end TDCSGTests.FramePair
