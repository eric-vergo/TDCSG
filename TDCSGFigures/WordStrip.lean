/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.Style

/-!
# A word strip for the animations

An option of the animations, off on the site: the word written in a row, letter by letter, with a
mark under the letter that acts at the current key. The letters are fixed items (a letter that
does not act faint); the mark of letter `i` is the actor `strip-<i>`, shown in the keys of that
letter and faded out and in when the next letter comes, so that only opacity is animated and
nothing in the panels moves. `stripIds` reads back which marks a key shows, for the exact checks
that the mark is under the key's letter.
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact

/-- The abscissa of letter `i` of a strip of `n` letters centred at `cx`, `gap` apart. -/
def stripX (n i : Nat) (cx gap : Rat) : Rat := cx + ((i : Rat) - ((n : Rat) - 1) / 2) * gap

/-- The letters `texts` in a row centred at `(cx, y)`, `gap` apart, in `role`; the letters whose
entry of `idle` is `true` faint. -/
def stripLetters (texts : List String) (idle : List Bool) (cx y gap : Rat) (role : String) :
    Array Item :=
  (texts.zip (idle ++ List.replicate texts.length false)).toArray.mapIdx fun i (t, quiet) =>
    let it := Plane.Exact.label t (stripX texts.length i cx gap, y) .center |>.role role
    if quiet then it.faint else it

/-- The mark under letter `i` of a strip of `n` letters (see `stripLetters`): a short thick
segment, the actor `strip-<i>`. -/
def stripMark (n i : Nat) (cx y gap : Rat) (role : String) : Item :=
  let x := stripX n i cx gap
  let y' := y - gap * 7 / 10
  Plane.Exact.segment (x - gap * 3 / 10, y') (x + gap * 3 / 10, y') |>.role role |>.width 3
    |>.named s!"the mark under letter {i + 1} of the word" |>.withId s!"strip-{i}"

/-- The ids of the strip's marks among `items`, in order. -/
def stripIds (items : Array Item) : List String :=
  (items.toList.filterMap fun it => match it with
    | .shape _ _ info | .group _ info => some info.id).filter (·.startsWith "strip-")

end TDCSGFigures
