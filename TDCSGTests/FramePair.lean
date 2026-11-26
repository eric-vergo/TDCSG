/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.FramePairMotion

/-!
# The declared moves of the frame pair arrive exactly

For the words of the frame pair at `r = 1.95` from `z = 0`, checked by `decide +kernel`: every
declared turn of every step (`TDCSGFigures.Lift.FramePairConfig.frameSteps`), applied exactly in
`ℤ[ζ₅]` to the anchors of the actors that the key figures draw (`FramePairConfig.actorsAt`) in key
`k`, gives their anchors in key `k + 1` (`FramePairConfig.allArrive`), in each panel's own
coordinates: with and without the riding disks, with the left panel halved and full size, with the
idle marks as outlines and as rings, with trails as dots and as arcs. A misplaced actor makes the
check fail. Every drawn actor gives back its base title (`FramePairConfig.baseTitlesRecoverable`,
checked by evaluation, since the drawing goes through floating point).
The letters that act are the ones pinned in `TDCSGTests.FrameWords`. This is the exact counterpart
of the floating-point arrival check of an animation; the general statements behind it are
`TDCSG.Five.framePicture_genA_genB` and `TDCSG.Five.halved_genA` with their companions. The
animation made from these moves (`FramePairConfig.motion`) passes the checks of PILean's motion
engine for two of the words, checked by evaluation.
-/

namespace TDCSGTests.FramePair

open TDCSGFigures TDCSGFigures.Lift TDCSGFigures.Early

/-- The turn factors of the declared fractions: `-1/5` is `ζ⁴`, `1/5` is `ζ`. -/
theorem turnFactor_fifths :
    (turnFactor (-1 / 5) == some (zeta 4)) = true ∧
      (turnFactor (1 / 5) == some (zeta 1)) = true := by
  decide +kernel

/-- `a b a b`: every step arrives in every variant of the panels; every letter acts. -/
theorem frameSteps_abab :
    ({ word := [.a, .b, .a, .b] } : FramePairConfig).allArrive = true ∧
      ({ word := [.a, .b, .a, .b], right := .centres } : FramePairConfig).allArrive = true ∧
      ({ word := [.a, .b, .a, .b], left := .full, trails := true } : FramePairConfig).allArrive =
        true ∧
      ({ word := [.a, .b, .a, .b], trails := true, trailLength := none } :
        FramePairConfig).allArrive = true ∧
      (({ word := [.a, .b, .a, .b] } : FramePairConfig).frameSteps.map (·.acts)) =
        [true, true, true, true] := by
  decide +kernel

/-- `a a b a b a a b b a b b`: every step arrives, with trails and centre-graph edges, and with the
left panel full size and the idle marks as dashed circles outside the disks; the letters `3`, `5`
and `10` do not act, so each has two steps (its mark appears, then vanishes) and the word has
sixteen keys; the centre-graph edge turns with the body in some step. -/
theorem frameSteps_aababaabbabb :
    ({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b], right := .bodiesGraph,
        trails := true } : FramePairConfig).allArrive = true ∧
    ({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b], left := .full,
        idleMark := .outline } : FramePairConfig).allArrive = true ∧
    ({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] } : FramePairConfig).keyCount =
      16 ∧
    (({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] } : FramePairConfig).frameSteps.map
      (·.acts)) = [true, true, false, false, true, false, false, true, true, true, true, false,
        false, true, true] ∧
    (({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] } : FramePairConfig).frameSteps.map
      (·.phase)).take 4 = [.turn, .turn, .markAppears, .markVanishes] ∧
    ({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b], right := .bodiesGraph } :
      FramePairConfig).frameSteps.any (·.rightTurning.contains "graph-edge") = true := by
  decide +kernel

/-- `a b a b b a b`: every step arrives; the letter `6` does not act (two steps). -/
theorem frameSteps_ababbab :
    ({ word := [.a, .b, .a, .b, .b, .a, .b] } : FramePairConfig).allArrive = true ∧
    (({ word := [.a, .b, .a, .b, .b, .a, .b] } : FramePairConfig).frameSteps.map (·.acts)) =
      [true, true, true, true, true, false, false, true] := by
  decide +kernel

/-- `a a b a a a b b b b b`: every step arrives, with trails as arcs; the letter `3` does not
act (two steps). -/
theorem frameSteps_aabaaabbbbb :
    ({ word := [.a, .a, .b, .a, .a, .a, .b, .b, .b, .b, .b], trails := true,
        trailStyle := .arcs } : FramePairConfig).allArrive = true ∧
    (({ word := [.a, .a, .b, .a, .a, .a, .b, .b, .b, .b, .b] } : FramePairConfig).frameSteps.map
      (·.acts)) = [true, true, false, false, true, true, true, true, true, true, true, true] := by
  decide +kernel

/-- The inverse letters: the twelve-letter word followed by its inverse arrives at every step. -/
theorem frameSteps_inverse :
    ({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] ++
        inverseWord [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] } :
      FramePairConfig).allArrive = true := by
  decide +kernel

/-- The actors of `a b a b` with the right riding disk drawn at the left centre. -/
def misplaced (cfg : FramePairConfig) (p : Panel) (k : Nat) : List Actor :=
  (cfg.actorsAt p k).map fun a =>
    if a.id == "right-disk" then { a with anchors := [(cfg.centresAt k).1] } else a

/-- A misplaced actor fails the check: with the right riding disk drawn at the left centre, the
steps of `a b a b` do not all arrive. -/
theorem misplaced_fails :
    ({ word := [.a, .b, .a, .b] } : FramePairConfig).allArriveWith
      (misplaced { word := [.a, .b, .a, .b] }) = false := by
  decide +kernel

/-- `a a b a b a a b b a b b` with trails, centre-graph edges and dashed circles. -/
def twelveLetters : FramePairConfig :=
  { word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b], right := .bodiesGraph,
    trails := true, idleMark := .outline }

-- Every drawn actor of `a a b a b a a b b a b b` (with trails, centre-graph edges and idle marks)
-- gives back its base title. The drawing goes through floating point, which the kernel does not
-- reduce, so this is checked by evaluation when the module is built.
#guard twelveLetters.baseTitlesRecoverable

-- The animation of the frame pair (`FramePairConfig.motion`, two panels on one clock) passes
-- every check of PILean's engine, with no error and no note, for `a b a b`, and for the
-- twelve-letter word as it opens the preview and with the centre-graph edge, trails and dashed
-- circles. The engine's checks are in floating point, so these are checked by evaluation when the
-- module is built.
#guard ({ word := [.a, .b, .a, .b] } : FramePairConfig).motion.problems.isEmpty
#guard ({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b], view := .wideRight } :
  FramePairConfig).motion.problems.isEmpty
#guard twelveLetters.motion.problems.isEmpty

end TDCSGTests.FramePair
