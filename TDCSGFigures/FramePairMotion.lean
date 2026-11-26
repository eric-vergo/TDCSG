/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.FramePair

/-!
# The frame pair as a motion of two panels on one clock

The key figures of the frame pair (`FramePairConfig.keys`) as a `PILean.Plane.MotionPanels`: the
traditional view (left) and the moving frame (right) side by side in one picture, one step per
letter that acts and two per letter that does not (its ring appears, then vanishes), both panels
moving at once (`FramePairConfig.motion`). `framePair`, the word `a a b a b a a b b a b b` at
`r = 1.95`, is Figure 4.2 of the site, an illustration (`@[figure illustration]`): its key figures
are stated in `TDCSGFigures.Lift.framePair_keys` on the page of the figures' theorems, and the
browser turns the drawn items between them.

* **Moves.** The moves of each step are those of `FramePairConfig.frameSteps`, in each panel's own
  coordinates: in the left panel the actor `"point"` turns by the step's exact `leftTurn` (about
  the centre of the letter's disk, by `-1/5` for `a` and `b`, `1/5` for their inverses); in the
  right panel the turning actors of the body (the edge, the other centre and its riding disk) turn
  about the active centre by `rightTurn`; the ring of an idle letter appears or vanishes. A panel
  whose step has no move idles while the other moves.
* **Timing.** Every step gets its duration from the pacing explicitly (`MotionPanels.timing`): a
  letter that acts takes `Pacing.turn` with `Pacing.easing`; the ring of a letter that does not act
  fades in and later out in `Pacing.fade` each, not eased, and is held in between for
  `Pacing.hold` like any key. So the pacing's `turn`, `fade`, `hold`, `firstHold`, `lastHold`,
  `easing` and `seam` are the whole timing (`motionPacing`, the pacing of every animation of the
  site).
* **Views.** No key sets a view of its own: the engine lays each panel out in one view for all its
  keys and for what its turns sweep (`Motion.sweptItems`), at one unit length in both panels
  (`PanelScale.common`). The panels' shares of the width are the page widths of the keys. The
  narrow rendition stacks the panels at `FramePairConfig.narrowWidth`.

**The checks and the exact pins.** `TDCSGTests.FramePair` proves, by `decide +kernel`, that each
declared turn of `frameSteps`, applied exactly in `ℤ[ζ₅]` to the anchors of the actors that the key
figures draw (`FramePairConfig.allArrive`), gives the anchors of the next key: a statement about
the exact data, before any drawing. The motion's own checks (`MotionPanels.report`) are about the
drawing, in floating point on the page: each turn, applied to the drawn actor, lands on the next
key within `0.01` px (arrival); the rest of every key shows that key's still (rest check); the
written SVG shows what the baker draws (writer); and nothing leaves its panel while it turns
(bounds). Both read the same moves (`frameSteps`) and the same actors (`actorsAt`).
-/

namespace TDCSGFigures.Lift

open PILean PILean.Plane PILean.Anim

/-- The step of one panel: the actors of `turning` turned by `turn`, those of `appear` faded in,
those of `vanish` faded out; an idle step when nothing moves. -/
def panelStep (turn : Option ExactTurn) (turning appear vanish : List String) : MotionStep :=
  let turns : Array (String × Move) := match turn with
    | some t => turning.toArray.map fun id => (id, Plane.Exact.turnAbout t.centre t.turns)
    | none => #[]
  let moves := turns ++ appear.toArray.map (·, Move.appear) ++
    vanish.toArray.map (·, Move.vanish)
  if moves.isEmpty then MotionStep.idle else { moves }

namespace FramePairConfig

variable (cfg : FramePairConfig)

/-- The word in letters `a`, `b`, `a⁻¹`, `b⁻¹`, separated by spaces. -/
def wordText : String := " ".intercalate (cfg.word.map Early.Letter.text)

/-- The timing of each step under `motionPacing`: `turn` with the pacing's easing for a letter
that acts, `fade` and not eased for the ring of one that does not appearing or vanishing. -/
def stepTimings : Array PanelTiming :=
  cfg.frameSteps.toArray.map fun s =>
    if s.acts then { duration := some motionPacing.turn, easing := some motionPacing.easing }
    else { duration := some motionPacing.fade, easing := some .linear }

/-- The frame pair as two panels on one clock (see the module docstring). -/
def motion : MotionPanels :=
  let ks := cfg.keys
  let unviewed := fun (f : Figure) => { f with view := none }
  let lefts := ks.map fun (l, _) => unviewed l
  let rights := ks.map fun (_, r) => unviewed r
  let steps := cfg.frameSteps.toArray
  let leftSteps := steps.map fun s => panelStep s.leftTurn s.leftTurning s.appearLeft s.vanishLeft
  let rightSteps := steps.map fun s =>
    panelStep s.rightTurn s.rightTurning s.appearRight s.vanishRight
  let (lw, rw) := match ks[0]? with
    | some (l, r) => (l.width, r.width)
    | none => (cfg.width, cfg.width)
  let gap : Float := 24
  { panels := #[{ title := "Traditional view", motion := { keys := lefts, steps := leftSteps } },
      { title := "Moving frame", motion := { keys := rights, steps := rightSteps } }]
    captions := ((List.range cfg.keyCount).map cfg.keyCaption).toArray
    pacing := motionPacing
    timing := cfg.stepTimings
    info := { title := s!"The frame pair for the word {cfg.wordText}"
              description := s!"The word {cfg.wordText} applied to z = 0, letter by letter, " ++
                "in two frames on one clock. Left: the disks halved, about 0 and 1, stay, and " ++
                "the point (y + 1)/2 turns a fifth of a turn about the center of the disk of " ++
                "each letter that acts. Right: the window about x = 1/2 and the point at x " ++
                "stay, and the pair of centers with the halved disks riding on them turns a " ++
                "fifth of a turn the other way about the active center. A letter that does " ++
                "not act is marked by a ring about its center while nothing moves." }
    checks := .fail
    gap
    scale := .common
    width := lw + gap + rw
    narrowWidth := some cfg.narrowWidth
    shares := #[lw, rw] }

end FramePairConfig

/-- The frame pair of chapter 4: the word `a a b a b a a b b a b b` applied to `z = 0` at
`r = 1.95`, in the traditional view (the disks halved, the point turning) beside the moving frame
of the chapter's proof (the window and the point fixed, the pair of centers turning about the
active center), on one clock; the letters 3, 5 and 10 do not act and are marked by a ring. -/
@[figure illustration]
def framePair : MotionPanels := ({} : FramePairConfig).motion

end TDCSGFigures.Lift
