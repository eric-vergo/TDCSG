/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.Data.Turns
import TDCSGFigures.Style

/-!
# Exact moves of the animations

The animations of chapters 1, 2, 3 and 7 declare their moves exactly and check them exactly: an
actor of a key frame is an id with the exact points that fix its drawing (`ExactActor`), and a
step lists, for some ids, an exact move (`ExactMove`): a turn about an exact centre by an exact
fraction of a full turn (`ExactTurn`), a slide along an exact vector, an appearance or a
disappearance. `stepArrives` decides, in the exact number field of the points, that every
declared turn or slide carries the anchors of its actor in one key onto those in the next, that
an actor no move names keeps its anchors, and that actors come and go only by a declared
appearance or disappearance. `exactStep` is the step the animation itself declares: the same
moves, read by PILean's engine (`ExactMove.toMove`), so that the exact check and the drawn
animation read one list.

The points are either of `ℚ(ζ₅)` (`ZetaFrac`, in which turns by fifths are exact) or of
`ℚ(√5)²` (`QSqrt5 × QSqrt5`, for the diagrams on a parameter line, which only slide);
`ExactPlane` gives each its equality, sum and turns.

`moveTiming` is the timing of a step under `motionPacing`: a turn or a slide eased, a step that
only fades not eased.
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact

/-- The sum of two numbers of `ℚ(ζ₅)` given over denominators, exact. -/
def ZetaFrac.add (p q : ZetaFrac) : ZetaFrac :=
  ⟨p.num * Zeta5.ofInt q.den + q.num * Zeta5.ofInt p.den, p.den * q.den⟩

/-- The exact operations the arrival checks use on points of type `α`. -/
class ExactPlane (α : Type) where
  /-- Equality, decided exactly. -/
  same : α → α → Bool
  /-- The point moved by a vector. -/
  add : α → α → α
  /-- The point turned exactly, `none` when the turn is not exact in this field. -/
  turn : ExactTurn → α → Option α

instance : ExactPlane ZetaFrac := ⟨ZetaFrac.same, ZetaFrac.add, ExactTurn.apply⟩

instance : ExactPlane (QSqrt5 × QSqrt5) :=
  ⟨fun p q => p.1 == q.1 && p.2 == q.2, fun p v => (p.1 + v.1, p.2 + v.2), fun _ _ => none⟩

/-- A declared move of an actor between two keys, exact. -/
inductive ExactMove (α : Type) where
  /-- A turn. -/
  | turn (t : ExactTurn)
  /-- A slide along the vector `v`. -/
  | slide (v : α)
  /-- The actor is in the next key and not in this one. -/
  | appear
  /-- The actor is in this key and not in the next. -/
  | vanish

/-- An actor of a key frame: its id and the exact points that fix its drawing, in the order of its
drawing. -/
structure ExactActor (α : Type) where
  /-- The id. -/
  id : String
  /-- The anchors. -/
  anchors : List α

variable {α : Type}

/-- The kind of the move, in words: `"turn"`, `"slide"`, `"appear"` or `"vanish"`. -/
def ExactMove.kind : ExactMove α → String
  | .turn _ => "turn"
  | .slide _ => "slide"
  | .appear => "appear"
  | .vanish => "vanish"

/-- The moves `moves` in words: each id with the kind of its move. -/
def moveKinds (moves : List (String × ExactMove α)) : List (String × String) :=
  moves.map fun (id, m) => (id, m.kind)

/-- The move as PILean's engine reads it: the same turn (`Plane.Exact.turnAbout`) or slide (the
page vector of `v`), appearance or disappearance. -/
def ExactMove.toMove [PlanePoint α] : ExactMove α → Move
  | .turn t => Plane.Exact.turnAbout t.centre t.turns
  | .slide v => .slide (PlanePoint.toPoint v)
  | .appear => .appear
  | .vanish => .vanish

/-- The step the animation declares: the moves, as PILean's engine reads them. -/
def exactStep [PlanePoint α] (moves : List (String × ExactMove α)) : MotionStep :=
  { moves := moves.toArray.map fun (id, m) => (id, m.toMove) }

/-- Whether the anchors `ps`, each moved by `f`, are the anchors `qs`, exactly. -/
def landsBy [ExactPlane α] (f : α → Option α) (ps qs : List α) : Bool :=
  ps.length == qs.length && (ps.zip qs).all fun (p, q) => (f p).any (ExactPlane.same · q)

/-- Whether the moves `moves` carry the actors `before` of one key onto the actors `after` of the
next, exactly: an actor turned or slid lands on its anchors in `after`; an actor no move names is
in `after` with the same anchors; one that vanishes is not in `after`; an actor of `after` that
is not in `before` appears; and every move names an actor of one of the two keys. -/
def stepArrives [ExactPlane α] (moves : List (String × ExactMove α))
    (before after : List (ExactActor α)) : Bool :=
  let find : List (ExactActor α) → String → Option (ExactActor α) := fun xs id =>
    xs.find? (·.id == id)
  let moveOf : String → Option (ExactMove α) := fun id => (moves.find? (·.1 == id)).map (·.2)
  before.all (fun a => match moveOf a.id, find after a.id with
    | some .vanish, none => true
    | some (.turn t), some b => landsBy (ExactPlane.turn t) a.anchors b.anchors
    | some (.slide v), some b => landsBy (fun p => some (ExactPlane.add p v)) a.anchors b.anchors
    | none, some b => landsBy some a.anchors b.anchors
    | _, _ => false) &&
  after.all (fun b => (find before b.id).isSome ||
    (match moveOf b.id with | some .appear => true | _ => false)) &&
  moves.all fun (id, _) => (find before id).isSome || (find after id).isSome

/-- Whether every step `k < n` (`moves k`) carries the actors of key `k` onto those of key
`k + 1` (`stepArrives`). -/
def allArrive [ExactPlane α] (n : Nat) (moves : Nat → List (String × ExactMove α))
    (actors : Nat → List (ExactActor α)) : Bool :=
  (List.range n).all fun k => stepArrives (moves k) (actors k) (actors (k + 1))

/-- The timing of a step with the moves `moves` under `motionPacing`: a turn takes `turn`, a slide
`slide` (by default the pacing's), both eased with the pacing's easing; a step that only fades
takes `fade`, not eased. -/
def moveTiming (moves : List (String × ExactMove α)) (slide : Rat := motionPacing.slide) :
    PanelTiming :=
  if moves.any (fun m => match m.2 with | .turn _ => true | _ => false) then
    { duration := some motionPacing.turn, easing := some motionPacing.easing }
  else if moves.any (fun m => match m.2 with | .slide _ => true | _ => false) then
    { duration := some slide, easing := some motionPacing.easing }
  else { duration := some motionPacing.fade, easing := some .linear }

end TDCSGFigures
