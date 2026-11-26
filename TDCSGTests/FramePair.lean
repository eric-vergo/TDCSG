/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.FramePair

/-!
# The declared moves of the frame pair arrive exactly

For the words of the frame pair at `r = 1.95` from `z = 0`, checked by `decide +kernel`: every
declared turn of every step (`TDCSGFigures.Lift.FramePairConfig.frameSteps`), applied exactly in
`ℤ[ζ₅]` to the actors' positions in key `k`, gives their positions in key `k + 1`
(`FramePairConfig.allArrive`), with the riding disks (`bodies`) and without (`centres`); and the
letters that act are the ones pinned in `TDCSGTests.FrameWords`. This is the exact counterpart of
the floating-point arrival check of an animation; the general statements behind it are
`TDCSG.Five.framePicture_genA_genB` and `TDCSG.Five.halved_genA` with their companions.
-/

namespace TDCSGTests.FramePair

open TDCSGFigures.Lift TDCSGFigures.Early

/-- The turn factors of the declared fractions: `-1/5` is `ζ⁴`, `1/5` is `ζ`. -/
theorem turnFactor_fifths :
    (turnFactor (-1 / 5) == some (TDCSGFigures.zeta 4)) = true ∧
      (turnFactor (1 / 5) == some (TDCSGFigures.zeta 1)) = true := by
  decide +kernel

/-- `a b a b`: every step arrives, with and without the riding disks; every letter acts. -/
theorem frameSteps_abab :
    ({ word := [.a, .b, .a, .b] } : FramePairConfig).allArrive = true ∧
      ({ word := [.a, .b, .a, .b], right := .centres } : FramePairConfig).allArrive = true ∧
      (({ word := [.a, .b, .a, .b] } : FramePairConfig).frameSteps.map (·.acts)) =
        [true, true, true, true] := by
  decide +kernel

/-- `a a b a b a a b b a b b`: every step arrives; the letters `3`, `5` and `10` do not act. -/
theorem frameSteps_aababaabbabb :
    ({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] } : FramePairConfig).allArrive =
      true ∧
    (({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] } : FramePairConfig).frameSteps.map
      (·.acts)) = [true, true, false, true, false, true, true, true, true, false, true, true] := by
  decide +kernel

/-- `a b a b b a b`: every step arrives; the letter `6` does not act. -/
theorem frameSteps_ababbab :
    ({ word := [.a, .b, .a, .b, .b, .a, .b] } : FramePairConfig).allArrive = true ∧
    (({ word := [.a, .b, .a, .b, .b, .a, .b] } : FramePairConfig).frameSteps.map (·.acts)) =
      [true, true, true, true, true, false, true] := by
  decide +kernel

/-- `a a b a a a b b b b b`: every step arrives; the letter `3` does not act. -/
theorem frameSteps_aabaaabbbbb :
    ({ word := [.a, .a, .b, .a, .a, .a, .b, .b, .b, .b, .b] } : FramePairConfig).allArrive = true ∧
    (({ word := [.a, .a, .b, .a, .a, .a, .b, .b, .b, .b, .b] } : FramePairConfig).frameSteps.map
      (·.acts)) = [true, true, false, true, true, true, true, true, true, true, true] := by
  decide +kernel

/-- The inverse letters: the twelve-letter word followed by its inverse arrives at every step. -/
theorem frameSteps_inverse :
    ({ word := [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] ++
        inverseWord [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] } :
      FramePairConfig).allArrive = true := by
  decide +kernel

end TDCSGTests.FramePair
