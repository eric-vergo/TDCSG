/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.Data.PartTwo
import TDCSGFigures.Data.Early

/-!
# Exact turns for the animations

A turn about an exact centre by an exact fraction of a full turn (`ExactTurn`), applied exactly to
points of `ℚ(ζ₅)` (`ZetaFrac.turnAbout`, `turnFactor`). The animations declare their moves with
it, and their exact arrival checks apply the same declared turns to the exact anchors of their key
frames: `TDCSGFigures.wordArrives` for the three words,
`TDCSGFigures.Lift.FramePairConfig.allArrive` for the frame pair.
-/

namespace TDCSGFigures

open PILean PILean.Exact

/-- A turn about an exact centre by an exact fraction of a full turn (counterclockwise). -/
structure ExactTurn where
  /-- The centre, in the panel's own coordinates. -/
  centre : ZetaFrac
  /-- The fraction of a full turn. -/
  turns : Rat

/-- Equality of two numbers of `ℚ(ζ₅)` given over denominators, exact. -/
def ZetaFrac.same (p q : ZetaFrac) : Bool :=
  p.num * Zeta5.ofInt q.den == q.num * Zeta5.ofInt p.den

/-- `c + τ (p - c)`: `p` turned about `c` by the factor `τ`, exact. -/
def ZetaFrac.turnAbout (c : ZetaFrac) (τ : Zeta5) (p : ZetaFrac) : ZetaFrac :=
  ⟨c.num * Zeta5.ofInt p.den + τ * (p.num * Zeta5.ofInt c.den - c.num * Zeta5.ofInt p.den),
    c.den * p.den⟩

/-- `ζᵏ` for a turn by `k/5` of a full turn (counterclockwise), `none` for any other fraction. -/
def turnFactor (q : Rat) : Option Zeta5 :=
  if q.den == 5 || q.den == 1 then
    let k := (q * 5).num
    some (zeta (k % 5).toNat)
  else none

/-- `p` turned exactly by the turn `t`; `none` when its fraction is not a multiple of a fifth. -/
def ExactTurn.apply (t : ExactTurn) (p : ZetaFrac) : Option ZetaFrac :=
  (turnFactor t.turns).map fun τ => ZetaFrac.turnAbout t.centre τ p

/-- The turn of the letter's point about its disk's centre, as a fraction of a full turn: `-1/5`
(clockwise) for `a` and `b`, `1/5` for their inverses. Every animation that turns by a letter
declares this fraction. -/
def Early.Letter.turns (l : Early.Letter) : Rat :=
  match l with
  | .a | .b => -1 / 5
  | .aInv | .bInv => 1 / 5

/-- Whether the letters' fractions are their own turns: for each letter, `Letter.turns` is a fifth
of a full turn, `1/5` or `-1/5`, and its factor (`turnFactor`) is the letter's turn `Letter.turn`
(`ζ⁴`, clockwise, for `a` and `b`; `ζ` for their inverses), the turn of its exact rotation
(`Letter.rotate`). The exact arrival check works modulo a full turn (a turn by `-4/5` lands where
one by `1/5` does), so the sense and the size of each declared turn are pinned by this and by the
declared fractions each animation's statement writes out. -/
def turnsAreFifths : Bool :=
  [Early.Letter.a, .aInv, .b, .bInv].all fun l =>
    turnFactor l.turns == some l.turn && (l.turns == 1 / 5 || l.turns == -1 / 5)

end TDCSGFigures
