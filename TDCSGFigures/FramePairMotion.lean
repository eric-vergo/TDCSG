/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.FramePair

/-!
# The frame pair as a motion of two panels on one clock

The key figures of the frame pair (`FramePairConfig.keys`) as a `PILean.Plane.MotionPanels`: the
traditional view (left) and the moving frame (right) side by side in one picture, one step per
letter that acts and two per letter that does not (its mark appears, then vanishes), both panels
moving at once (`FramePairConfig.motion`).

* **Moves.** The moves of each step are those of `FramePairConfig.frameSteps`, in each panel's own
  coordinates: in the left panel the actor `"point"` turns by the step's exact `leftTurn` (about
  the centre of the letter's disk, by `-1/5` for `a` and `b`, `1/5` for their inverses); in the
  right panel the turning actors of the body (the edge, the other centre and its riding disk, and
  the centre-graph edge while it stays shown) turn about the active centre by `rightTurn`; the
  actors the step's key adds or drops (the mark of an idle letter, trail marks, the edge of the
  centre graph) appear or vanish. A panel whose step has no move idles while the other moves.
* **Timing.** Every step gets its duration from the pacing explicitly (`MotionPanels.timing`): a
  letter that acts takes `Pacing.turn` with `Pacing.easing`; the mark of a letter that does not act
  fades in and later out in `Pacing.fade` each, not eased, and is held in between for `Pacing.hold`
  like any key. So the pacing's `turn`, `fade`, `hold`, `firstHold`, `lastHold`, `easing` and
  `seam` are the whole timing, and `idle` and `slide` play no part.
* **Views.** No key sets a view of its own: the engine lays each panel out in one view for all its
  keys and for what its turns sweep (`Motion.sweptItems`), at one unit length in both panels
  (`PanelScale.common`); a full-size left panel is drawn at half the unit length of the right
  one, as the keys draw it, so each panel is fitted to its share on its own
  (`PanelScale.independent`). The panels' shares of the width are the page widths of the
  variant's keys (`ViewStyle`: equal for `shared`, each cropped for `cropped`, twice the panel
  width in all for `wideRight`). The narrow rendition stacks the panels at the variant's narrow
  width.

**The checks and the exact pins.** `TDCSGTests.FramePair` proves, by `decide +kernel`, that each
declared turn of `frameSteps`, applied exactly in `ℤ[ζ₅]` to the anchors of the actors that the key
figures draw (`FramePairConfig.allArrive`), gives the anchors of the next key: a statement about
the exact data, before any drawing. The motion's own checks (`MotionPanels.report`) are about the
drawing, in floating point on the page: each turn, applied to the drawn actor, lands on the next
key within `0.01` px (arrival); the rest of every key shows that key's still (rest check); the
written SVG shows what the baker draws (writer); and nothing leaves its panel while it turns
(bounds). Both read the same moves (`frameSteps`) and the same actors (`actorsAt`), so the exact
pins say that the declared moves are right and the engine's checks say that they are drawn as
declared.
-/

namespace TDCSGFigures.Lift

open PILean PILean.Plane PILean.Anim

/-- The canonical pacing of the preview: every move and every rest one second, moves not eased,
the loop closed by a cut. A page that maps wall time onto this cycle piecewise can play any other
pacing exactly: a move of length `d'` at progress `u` shows the canonical time
`start + ease(u)`, a rest shows `start + u`. -/
def canonicalPacing : Pacing :=
  { turn := 1, slide := 1, fade := 1, hold := 1, idle := 1, firstHold := 1, lastHold := 1,
    easing := .linear, seam := .cut }

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

/-- The variant's word in letters `a`, `b`, `A = a⁻¹`, `B = b⁻¹`. -/
def wordText : String :=
  String.join (cfg.word.map fun l => match l with
    | .a => "a" | .b => "b" | .aInv => "A" | .bInv => "B")

/-- The timing of each step under `pacing`: `turn` with the pacing's easing for a letter that
acts, `fade` and not eased for the mark of one that does not appearing or vanishing. -/
def stepTimings (pacing : Pacing) : Array PanelTiming :=
  cfg.frameSteps.toArray.map fun s =>
    if s.acts then { duration := some pacing.turn, easing := some pacing.easing }
    else { duration := some pacing.fade, easing := some .linear }

/-- The frame pair as two panels on one clock under `pacing` (see the module docstring), in the
house style's dark twin when `dark`. -/
def motionWith (pacing : Pacing) (dark : Bool := false) : MotionPanels :=
  let ks := cfg.keys
  let restyle := fun (f : Figure) =>
    { f with view := none, style := if dark then f.style.darkTwin?.getD f.style else f.style }
  let lefts := ks.map fun (l, _) => restyle l
  let rights := ks.map fun (_, r) => restyle r
  let steps := cfg.frameSteps.toArray
  let leftSteps := steps.map fun s => panelStep s.leftTurn s.leftTurning s.appearLeft s.vanishLeft
  let rightSteps := steps.map fun s =>
    panelStep s.rightTurn s.rightTurning s.appearRight s.vanishRight
  let (lw, rw) := match ks[0]? with
    | some (l, r) => (l.width, r.width)
    | none => (cfg.width, cfg.width)
  let gap : Float := 24
  let (n0, n1) := cfg.leftNames
  let leftText := match cfg.left with
    | .halved => s!"the disks halved, about {n0} and {n1}, stay, and the point (y + 1)/2"
    | .full => s!"the disks of radius r about {n0} and {n1} stay, and the point y"
  let rightText := if cfg.riding then
      "the window about x = 1/2 and the point at x stay, and the pair of centers with the " ++
        "halved disks riding on them"
    else "the window about x = 1/2 stays, and the pair of centers with the edge between them"
  { panels := #[{ title := "Traditional view", motion := { keys := lefts, steps := leftSteps } },
      { title := "Moving frame", motion := { keys := rights, steps := rightSteps } }]
    captions := ((List.range cfg.keyCount).map cfg.keyCaption).toArray
    pacing
    timing := cfg.stepTimings pacing
    info := { title := s!"The frame pair for the word {cfg.wordText}"
              description := s!"The word {cfg.wordText} applied to z = 0, letter by letter, in " ++
                s!"two frames on one clock. Left: {leftText} turns a fifth of a turn about " ++
                "the center of the disk of each letter that acts. Right: " ++ rightText ++
                " turns a fifth of a turn the other way about the active center. A letter " ++
                "that does not act is marked while nothing moves." }
    checks := .fail
    gap
    scale := if cfg.left == .full then .independent else .common
    width := lw + gap + rw
    narrowWidth := some cfg.narrowWidth
    shares := #[lw, rw] }

/-- The frame pair as two panels on one clock at the canonical pacing (`motionWith`,
`canonicalPacing`), in the light style. -/
def motion : MotionPanels := cfg.motionWith canonicalPacing

end FramePairConfig

end TDCSGFigures.Lift
