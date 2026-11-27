/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import PILean.Trust.Attr
import TDCSGFigures.Lens

/-!
# The lens as the radius grows to `R`, as a loop

A looping animation (an illustration) of the lens pictures of chapter 5 (`lensItems`) at
increasing radii, ending at the critical radius `R = √(3 + φ)`: `LensLoopConfig.motion`. Its keys
are the exact pictures at the half radii of `LensLoopConfig.radii`, then two at `R`: the first
with the dashed edge `Re v = κ - η` drawn where it has arrived, on `Re v = κ` (`η = 0`), and the
tip there, and the last as the slider showed `R`, the two half-planes one.

* **Morph** (`morph := true`). The lens is a function of the radius, and so are the circles, the
  dashed edge, the drawn radius and the tip: between two keys of different radii they are morphed
  through the exact pictures at `samples - 1` radii between them (`r²` evenly spaced, all of them
  below `R`, `LensLoopConfig.between`), and the browser interpolates the path data linearly only
  between two consecutive samples. What appears with one key and not the next (the margin `η` and
  `v*` of the first key, the labels that change their words at `R`) fades.
* **Crossfade** (`morph := false`). Every item that changes with the radius is an actor of its key
  alone, so the picture crossfades from one exact key to the next and nothing is interpolated.

The tip and its label slide between two radii, on the line the tip moves on, at constant speed
during the step; the lens's corner, which the morph draws, is at the exact tip at every sample.
-/

namespace TDCSGFigures.Lens

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- `h² = r²/4 - 1/4` at the squared radius `r2`. -/
def hSqOf (r2 : QSqrt5) : QSqrt5 := r2 * rat (1 / 4) - rat (1 / 4)

/-- The setting of a key of a loop at the squared radius `r2` (`r` written `rText`), with the cut
`κ - η` drawn: the half radius `√(r²/4)`, the tip `tipOf (hSqOf r2)` recording that it lies on
both circles and on the lens, and `cuts` relative to both half-planes (`.outside` below `R`, `.on`
at `R`); `v*` and the margin `η` drawn apart when `first`. -/
def loopSetting (r2 : QSqrt5) (rText : String) (first : Bool) (idSuffix : String)
    (cuts : Plane.Incidence := .outside) : Setting (SqrtOf QSqrt5) :=
  { half := ⟨r2 * rat (1 / 4)⟩, r2, rText, tipPt := tipItemWith (tipOf (hSqOf r2)) (some cuts),
    tipXY := PlanePoint.toPoint (tipOf (hSqOf r2)), other := otherSide (r2 * rat (1 / 4)),
    critical := false, showVStar := first, showMargin := first, motion := true, idSuffix }

/-- The loop through the lens pictures as the radius grows to `R` (see the module docstring). -/
structure LensLoopConfig where
  /-- The radii below `R`, increasing, with their values as text. -/
  radii : Array (Rat × String) := #[(9 / 5, "1.8"), (2, "2"), (52 / 25, "2.08"), (53 / 25, "2.12")]
  /-- Whether the pictures between two radii are morphed (otherwise they crossfade). -/
  morph : Bool := true
  /-- The number of intervals of a morph, each ended by an exact picture. -/
  samples : Nat := 12
  /-- The duration of a step that changes the radius, in seconds. -/
  stepTime : Rat := 6 / 5
  /-- The rest at every key but the first and the last, in seconds. -/
  hold : Rat := 3 / 2

namespace LensLoopConfig

variable (cfg : LensLoopConfig)

/-- The number of keys: one per radius below `R`, and two at `R`. -/
def keyCount : Nat := cfg.radii.size + 2

/-- `r²` at key `k` (`3 + φ` for the two keys at `R`). -/
def r2At (k : Nat) : QSqrt5 :=
  match cfg.radii[k]? with
  | some (r, _) => rat (r * r)
  | none => criticalSq

/-- What the ids of key `k` end with: nothing when morphing, `-k` when crossfading. -/
def suffix (k : Nat) : String := if cfg.morph then "" else s!"-{k}"

/-- The setting of key `k`. -/
def setting (k : Nat) : Setting (SqrtOf QSqrt5) :=
  match cfg.radii[k]? with
  | some (_, t) => loopSetting (cfg.r2At k) t (k == 0) (cfg.suffix k)
  | none =>
    let st := loopSetting criticalSq "R = √(3 + φ)" false (cfg.suffix k) .on
    if k == cfg.radii.size then st
    else
      { st with critical := true, tipPt := tipItemWith (tipOf (hSqOf criticalSq)) none
          |>.incident .on "the half-plane Re v ≥ κ" }

/-- Key `k`: the lens picture of its setting, without a view of its own. -/
def key (k : Nat) : Plane.Figure := { lensFigure (cfg.setting k) false with view := none }

/-- The ids of the actors of the figure `f`. -/
def actorIds (f : Plane.Figure) : Array String := f.items.filterMap (·.actorId?)

/-- Whether step `j` changes the radius. -/
def grows (j : Nat) : Bool := j < cfg.radii.size

/-- The tip at key `k`. -/
def tipAt (k : Nat) : SurdPoint := tipOf (hSqOf (cfg.r2At k))

/-- The moves of step `j`: when the radius changes, the tip and its label slide along the line
the tip moves on (`tipOf` is `u/2 + h (s, -c₁)`, so the tip moves on the perpendicular bisector
of `0` and `u`) and the other actors of both keys morph (they stay otherwise); those of key `j`
alone vanish, those of key `j + 1` alone appear. -/
def moves (j : Nat) : Array (String × Move) :=
  let a := actorIds (cfg.key j)
  let b := actorIds (cfg.key (j + 1))
  let slide := Plane.Exact.slideFromTo (cfg.tipAt j) (cfg.tipAt (j + 1))
  (if cfg.grows j then (a.filter b.contains).map fun id =>
      (id, if id == "tip" || id == "tip-label" then slide else Move.morph) else #[]) ++
    (a.filter (!b.contains ·)).map (·, Move.vanish) ++
    (b.filter (!a.contains ·)).map (·, Move.appear)

/-- The picture at the fraction `q` of step `j`: the lens picture at the squared radius
`(1 - q) r_j² + q r_{j+1}²`. -/
def between (j : Nat) (q : Rat) : Option Plane.Figure :=
  if cfg.grows j then
    let r2 := cfg.r2At j * rat (1 - q) + cfg.r2At (j + 1) * rat q
    some { cfg.key j with items := lensItems (loopSetting r2 "" false "") }
  else none

/-- The facts each key shows, exactly: below `R`, the tip lies on both circles and left of
`κ - 2η`, and the disk `|v| ≤ r/2` lies left of `κ - η` or not as the caption says
(`diskLeftOfCut`); at `R`, the tip is `v*` (`h² = s²`, `c₁/2 + s² = κ`). -/
def keyFacts : Bool :=
  cfg.radii.all (fun (r, _) => tipFacts (r / 2) && tipReLe (r / 2)) &&
    (hSqOf criticalSq == sineSq && cosine * rat (1 / 2) + sineSq == kappa)

/-- Whether the disk `|v| ≤ r/2` lies left of the dashed edge at the radius `r`. -/
def diskLeftOfCut (r : Rat) : Bool := QSqrt.lt (rat (r / 2)) (cut (rat (r * r)))

/-- The caption of key `k`. -/
def caption (k : Nat) : String :=
  match cfg.radii[k]? with
  | some (r, t) =>
    let disk := if diskLeftOfCut r then " The circle |v| = r/2 lies left of the dashed edge: no \
        v meets the hypothesis of the lemma."
      else " The circle |v| = r/2 crosses the dashed edge, and the lens does not."
    if k == 0 then
      s!"The lens of the closed disks |v| ≤ r/2 and |v − u| ≤ r/2 at r = {t}, with the \
        half-planes Re v ≥ κ − η (dashed edge) and Re v ≥ κ, η = (3 + φ − r²)/16, and v∗ on \
        Re v = κ. The tip of the lens lies left of the dashed edge, at least η from it." ++ disk
    else
      s!"r = {t}: the strip between the edges is narrower, and the tip has moved right; it \
        stays at least η left of the dashed edge." ++ disk
  | none =>
    if k == cfg.radii.size then
      "r = R = √(3 + φ): η = 0, so the dashed edge has reached Re v = κ, and so has the tip: \
        the tip is v∗."
    else
      "At R the two half-planes are one, Re v ≥ κ, and the tip of the lens is v∗, on its \
        edge. Below R it stays at least η left of the dashed edge."

/-- The loop as a picture of one panel (without a narrow rendition, which only a picture of
panels side by side needs). -/
def motion : MotionPanels :=
  let n := cfg.keyCount
  { panels := #[{ motion :=
      { keys := ((List.range n).map cfg.key).toArray,
        steps := ((List.range (n - 1)).map fun j => ({ moves := cfg.moves j } : MotionStep)).toArray,
        between := cfg.between, morphSamples := cfg.samples } }]
    captions := ((List.range n).map cfg.caption).toArray
    pacing := { motionPacing with hold := cfg.hold, lastHold := 3 }
    timing := ((List.range (n - 1)).map fun j =>
      (if cfg.grows j then { duration := some cfg.stepTime, easing := some .linear }
        else { duration := some motionPacing.fade, easing := some .linear } : PanelTiming)).toArray
    info := { title := "The lens and its tip as r grows to R"
              description := s!"The lens of the closed disks |v| ≤ r/2 about 0 and |v − u| ≤ r/2 \
                about u = ζ, with the half-planes Re v ≥ κ − η (dashed edge) and Re v ≥ κ, at \
                r = {", ".intercalate (cfg.radii.map (·.2)).toList} and R = √(3 + φ). " ++
                (if cfg.morph then "Between two radii the picture passes through the exact \
                  pictures at the radii between, and the browser interpolates between those. "
                else "The picture crossfades from one radius to the next. ") ++
                "As r grows the strip between the edges narrows and the tip moves right, \
                staying left of the dashed edge; at R, where η = 0, the tip is v∗ on \
                Re v = κ." }
    checks := .fail
    poster := n - 1
    width := figureWidth }

end LensLoopConfig

/-! ### The variants for the owner's choice -/

/-- Morphed through the radii of the slider it would replace. -/
def lensMorph : LensLoopConfig := {}

/-- Crossfaded through more radii. -/
def lensFade : LensLoopConfig :=
  { radii := #[(9 / 5, "1.8"), (39 / 20, "1.95"), (2, "2"), (51 / 25, "2.04"), (52 / 25, "2.08"),
      (21 / 10, "2.1"), (53 / 25, "2.12"), (107 / 50, "2.14")],
    morph := false, hold := 1 }

end TDCSGFigures.Lens
