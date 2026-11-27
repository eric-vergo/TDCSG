/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.Lift

/-!
# Words for the frame pair of chapter 4

Pins, by `decide +kernel`, of words, most with letters that do not act, at `r = 1.95` from `z = 0`
(`TDCSGFigures.Lift.radiusSq`): for each word one summary (`TDCSGFigures.Lift.wordSummary`) of its
idle positions, the geometry of every step (`State.stepHolds`), whether the orbit closes and its
squared extents `|(y + 1)/2|²` and `|P - x|²` in the two frames. These are other words for the
frame pair, found by `scripts/FrameWords.lean`; the figure's own word, at `r = 2.12`, is pinned in
`TDCSGFigures.Lift.wordSummary_word`. This module is built by the test driver, not by
the figures or the blueprint.
-/

namespace TDCSGTests.FrameWords

open PILean.Exact TDCSGFigures.Lift TDCSGFigures.Early

/-- `a b a b`: every letter acts, every step has the geometry of `State.stepHolds`, the orbit does
not close, and it reaches `|(y + 1)/2|² = 21/4 - 2√5` (about `0.88²`) and `|P - x|² = 3/2 - √5/4`
(about `0.97²`). -/
theorem wordSummary_abab :
    wordSummary radiusSq [.a, .b, .a, .b] = ⟨[], true, false, ⟨21 / 4, -2⟩, ⟨3 / 2, -1 / 4⟩⟩ := by
  decide +kernel

/-- `a b a b b a b`, `a b a b` continued: only the letter `6` does not act; the orbit does not
close; it reaches `|(y + 1)/2|² = |P - x|² = 11/4 - √5/2` (about `1.28²`). -/
theorem wordSummary_ababbab :
    wordSummary radiusSq [.a, .b, .a, .b, .b, .a, .b] =
      ⟨[6], true, false, ⟨11 / 4, -1 / 2⟩, ⟨11 / 4, -1 / 2⟩⟩ := by
  decide +kernel

/-- `a a b a a a`: only the letter `3` does not act, and the orbit closes: the five acting `a`
turn the right centre once around the left centre. It reaches `|(y + 1)/2|² = 1/4` and
`|P - x|² = 3/2 + √5/4`. -/
theorem wordSummary_aabaaa :
    wordSummary radiusSq [.a, .a, .b, .a, .a, .a] =
      ⟨[3], true, true, ⟨1 / 4, 0⟩, ⟨3 / 2, 1 / 4⟩⟩ := by
  decide +kernel

/-- `a a b a a a b b b b b`: only the letter `3` does not act, both `a` and `b` act, and the orbit
closes; it reaches `|(y + 1)/2|² = |P - x|² = 3/2 + √5/4`. -/
theorem wordSummary_aabaaabbbbb :
    wordSummary radiusSq [.a, .a, .b, .a, .a, .a, .b, .b, .b, .b, .b] =
      ⟨[3], true, true, ⟨3 / 2, 1 / 4⟩, ⟨3 / 2, 1 / 4⟩⟩ := by
  decide +kernel

/-- The inverse letters follow their frame rule: the twelve-letter word followed by its inverse
has the idle letters `3, 5, 10` and their mirror images `15, 20, 22`, every step has the geometry
of `State.stepHolds`, and the orbit returns to its start. -/
theorem wordSummary_aababaabbabb_inverse :
    wordSummary radiusSq ([.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b] ++
      inverseWord [.a, .a, .b, .a, .b, .a, .a, .b, .b, .a, .b, .b]) =
      ⟨[3, 5, 10, 15, 20, 22], true, true, ⟨3 / 2, 1 / 4⟩, ⟨3 / 2, 1 / 4⟩⟩ := by
  decide +kernel

end TDCSGTests.FrameWords
