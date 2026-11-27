/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import PILean.Trust.Attr
import TDCSGFigures.Front
import TDCSGFigures.Data.Moves

/-!
# The orbit of zero as the radius grows

`orbitRadius`, a looping animation (an illustration) of the orbit of `0` under the two generators,
computed exactly in `ℤ[ζ₅]` by the orbit engine (`TDCSGFigures.orbit`): one key per radius of
`GrowthConfig.radii` and a last key at the critical radius `R = √(3 + φ)`, where the orbit is
infinite (`TDCSG.CriticalRadius.infinite_orbit_zero_five`) and its first `cap` points, in the order
in which the engine's breadth-first search from `0` finds them, are drawn. Each drawn orbit
contains the one before it (`GrowthConfig.nested`, decided on the drawn points; in general
`TDCSG.orbit_mono`), so from one key to the next the points already drawn stay and the new ones
fade in, while the two circles and their lens grow: a morph through the exact circles and lens at
`samples - 1` radii between two keys, `r²` evenly spaced (`GrowthConfig.between`), between which
the browser interpolates the path data linearly. The orbit itself is drawn only at the keys. The
radius and the number of points are written under the disks.

No point moves. The points a key draws first are one actor, a group (`GrowthConfig.pointGroup`),
which keeps the animated SVG small, and which comes in by an appearance; the groups up to a key are
the points of its orbit, each once (`GrowthConfig.partitions`). The exact arrival check
(`TDCSGFigures.allArrive`) reads the same groups: each stays where it is from key to key and comes
only by its declared appearance (`GrowthConfig.arrives`). The checks are `#guard` lines of
`TDCSGTests.Motions`, and the definitions are stated in `TDCSGFigures.orbitRadius_keys`.
-/

namespace TDCSGFigures.OrbitLoop

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-! ### Radii and orbits -/

/-- A radius of a loop: a rational radius with its value as text, or the critical radius. -/
inductive Radius where
  /-- The rational radius `r`, written `text`. -/
  | rat (text : String) (r : Rat)
  /-- The critical radius `R = √(3 + φ)`. -/
  | critical
  deriving Inhabited

/-- The squared radius for the orbit engine. -/
def Radius.sq : Radius → RadiusSq
  | .rat _ r => .ofRat r
  | .critical => .critical

/-- `r²` in `ℚ(√5)`. -/
def Radius.sqValue : Radius → QSqrt5
  | .rat _ r => TDCSGFigures.rat (r * r)
  | .critical => threePlusPhi

/-- The radius as an exact square root, `√(r²)`. -/
def Radius.value (ρ : Radius) : SqrtOf QSqrt5 := ⟨ρ.sqValue⟩

/-- The radius as text: its decimal value, or `R`. -/
def Radius.text : Radius → String
  | .rat t _ => t
  | .critical => "R"

/-- The empty orbit. -/
instance : Inhabited Orbit := ⟨{ points := #[], complete := false }⟩

/-- The orbit of `0` at the radius `ρ`, at most `cap` points; empty when the engine fails (which
the checks of the loops then report as a wrong count). -/
def orbitAt (ρ : Radius) (cap : Nat) : Orbit :=
  match orbit ρ.sq origin cap with
  | .ok o => o
  | .error _ => { points := #[], complete := false }

/-- Whether every point of `a` is a point of `b`. -/
def subset (a b : Array OrbitPoint) : Bool := a.all fun p => b.any (·.z == p.z)

/-- A point of an orbit as drawn: a small dot without a halo, recording where it stands relative
to each disk of squared radius `r2` and to their lens, as the engine decides it (`decided` checks
that it does). -/
def dot (r2 : RadiusSq) (z : Zeta5) : Item :=
  let it := Plane.Exact.point z |>.size 1.5 |>.halo false
  match sides r2 z with
  | .ok (l, r) => withSides it l r
  | .error _ => it

/-- Whether the engine decides where each of the points `zs` stands relative to the disks of
squared radius `r2`. -/
def decided (r2 : RadiusSq) (zs : Array Zeta5) : Bool :=
  zs.all fun z => (sides r2 z).toOption.isSome

/-- The circles of radius `r` about `-1` and `1` and their lens, the actors `"left-disk"`,
`"right-disk"` and `"lens"`. Their titles do not name the radius, so that they are drawn alike at
every radius but for their path data, which the browser interpolates. -/
def diskActors {β : Type} [RealValue β] (r : β) : Array Item := #[
  Plane.Exact.disk leftCentre r |>.noFill |>.role leftRole |>.named "the left circle"
    |>.describedBy "the closed disk of radius r about −1" |>.actor "left-disk",
  Plane.Exact.disk rightCentre r |>.noFill |>.role rightRole |>.named "the right circle"
    |>.describedBy "the closed disk of radius r about 1" |>.actor "right-disk",
  Plane.Exact.lens leftCentre rightCentre r r |>.role lensRole |>.noOutline
    |>.fillOpacity 0.12 |>.named "the lens" |>.actor "lens"]

/-- The centres `-1` and `1`, recording where they stand relative to the disks of squared radius
`r2`. They carry no labels: the points of the larger orbits come close to them on every side. -/
def centres (r2 : RadiusSq) : Array Item :=
  let side := fun (c : Zeta5) (it : Item) => match sides r2 c with
    | .ok (l, r) => withSides it l r
    | .error _ => it
  #[side leftCentre (Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1"),
    side rightCentre (Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1")]

/-- The height of the line under the disks that gives the radius and the number of points. -/
def valueY : Rat := -27 / 10

/-! ### One picture, one key per radius -/

/-- The loop of one picture through the orbits at increasing radii (see the module docstring). -/
structure GrowthConfig where
  /-- The rational radii below `R`, increasing, with their values as text; from `√2` on, where
  each arc of the lens spans more than a quarter of its circle, so that the lens is drawn with the
  same number of curves at every radius and can be morphed. -/
  radii : Array (String × Rat) :=
    #[("1.5", 3 / 2), ("1.9", 19 / 10), ("1.95", 39 / 20), ("2.05", 41 / 20), ("2.1", 21 / 10)]
  /-- How many points of the infinite orbit at `R` are drawn: the first ones the search finds. -/
  cap : Nat := 1000
  /-- The number of intervals of a step in which the circles and the lens are drawn exactly. -/
  samples : Nat := 12
  /-- The duration of a step, in seconds. -/
  stepTime : Rat := 6 / 5
  /-- The rest at every key but the first and the last, in seconds. -/
  hold : Rat := 3 / 2

namespace GrowthConfig

variable (cfg : GrowthConfig)

/-- The number of keys: one per rational radius, and one at `R`. -/
def keyCount : Nat := cfg.radii.size + 1

/-- The radius of key `k`. -/
def radius (k : Nat) : Radius :=
  match cfg.radii[k]? with
  | some (t, r) => .rat t r
  | none => .critical

/-- The orbits of the keys: complete at the rational radii (at most `100000` points, which they
do not reach), the first `cap` points at `R`. -/
def orbits : Array Orbit :=
  ((List.range cfg.keyCount).map fun k =>
    let ρ := cfg.radius k
    orbitAt ρ (match ρ with | .critical => cfg.cap | .rat .. => 100000)).toArray

/-- The points that key `k` draws first: the points of its orbit not in the orbit of key
`k - 1`, in the order the search found them. -/
def newPoints (os : Array Orbit) (k : Nat) : Array Zeta5 :=
  let here := (os.getD k default).points
  if k == 0 then here.map (·.z)
  else
    let before := (os.getD (k - 1) default).points
    (here.filter fun p => !before.any (·.z == p.z)).map (·.z)

/-- The points first drawn at key `j`, as they are drawn at key `k ≥ j`: one group, the actor
`"orbit-<j>"`, recording at the radius of key `k`. -/
def pointGroup (os : Array Orbit) (j k : Nat) : Item :=
  (group ((newPoints os j).map (dot (cfg.radius k).sq)))
    |>.named s!"the points of the orbit first drawn at r = {(cfg.radius j).text}"
    |>.actor s!"orbit-{j}"

/-- The keys `j ≤ k` that bring new points. -/
def groupsUpTo (os : Array Orbit) (k : Nat) : List Nat :=
  (List.range (k + 1)).filter fun j => !(newPoints os j).isEmpty

/-- The text under the disks at key `k`: the radius and the number of points. -/
def valueText (os : Array Orbit) (k : Nat) : String :=
  let n := (os.getD k default).points.size
  match cfg.radius k with
  | .rat t _ => s!"r = {t}: {n} points"
  | .critical => s!"r = R: infinite, the first {n} shown"

/-- The line under the disks at key `k` (actor `"value-<k>"`). -/
def valueLabel (os : Array Orbit) (k : Nat) : Item :=
  Plane.Exact.label (cfg.valueText os k) ((0 : Rat), valueY) |>.actor s!"value-{k}"

/-- The caption of key `k`. -/
def caption (os : Array Orbit) (k : Nat) : String :=
  let n := (os.getD k default).points.size
  let prev := (os.getD (k - 1) default).points.size
  match cfg.radius k with
  | .rat t _ =>
    if k == 0 then
      s!"The orbit of 0 under the two moves at r = {t}, computed exactly: {n} points. As r \
        grows the closed disks grow and the orbit can only grow: at each radius shown the points \
        it has gained fade in. Between two radii only the circles grow; the orbit is drawn only \
        at the radii shown."
    else if n == prev then
      s!"r = {t}: the disks are larger, and the orbit is the same {n} points."
    else s!"r = {t}: {n} points; the {n - prev} new ones have faded in, and the {prev} points \
      of the orbit at r = {(cfg.radius (k - 1)).text} are among them."
  | .critical =>
    s!"r = R = √(3 + φ): the orbit is infinite, and only the first {n} of its points that a \
      breadth-first search from 0 finds are drawn; the {prev} points of the orbit at \
      r = {(cfg.radius (k - 1)).text} are among them."

/-- Key `k`: the circles and the lens at its radius, the points of its orbit in the groups by the
key that drew them first, the centres and the line under the disks. -/
def key (os : Array Orbit) (k : Nat) : Plane.Figure :=
  let ρ := cfg.radius k
  { width := figureWidth
    padding := 16
    style := orbitStyle
    checks := .fail
    items := diskActors ρ.value ++ ((groupsUpTo os k).map (cfg.pointGroup os · k)).toArray ++
      centres ρ.sq ++ #[cfg.valueLabel os k]
    info := { title := s!"The orbit of 0 at r = {ρ.text}" } }

/-- The exact moves of step `j` (key `j` to key `j + 1`): the line under the disks changes, and
the points new at key `j + 1`, if any, fade in. -/
def moves (os : Array Orbit) (j : Nat) : List (String × ExactMove ZetaFrac) :=
  [(s!"value-{j}", .vanish), (s!"value-{j + 1}", .appear)] ++
    (if (newPoints os (j + 1)).isEmpty then [] else [(s!"orbit-{j + 1}", .appear)])

/-- The exact actors of key `k`: each group of points with its points, and the line under the
disks, whose place does not change and which is given no anchor. -/
def actors (os : Array Orbit) (k : Nat) : List (ExactActor ZetaFrac) :=
  ((groupsUpTo os k).map fun j =>
    ⟨s!"orbit-{j}", (newPoints os j).toList.map ZetaFrac.ofZeta⟩) ++ [⟨s!"value-{k}", []⟩]

/-- Whether every declared appearance and disappearance is the change from one key to the next,
and every group of points stays where it is (`allArrive`). -/
def arrives : Bool :=
  let os := cfg.orbits
  allArrive (cfg.keyCount - 1) (moves os) (actors os)

/-- Whether each drawn orbit contains the one before it, the orbits at the rational radii are
complete, and the engine decides the side of every point drawn. -/
def nested : Bool :=
  let os := cfg.orbits
  ((List.range (cfg.keyCount - 1)).all fun k =>
    subset (os.getD k default).points (os.getD (k + 1) default).points) &&
  ((List.range cfg.radii.size).all fun k => (os.getD k default).complete) &&
  ((List.range cfg.keyCount).all fun k =>
    decided (cfg.radius k).sq ((os.getD k default).points.map (·.z)))

/-- Whether the groups of points up to each key are the points of its orbit, each once: the sizes
of the groups add up to the size of the orbit, and every point of the orbit is in a group. -/
def partitions : Bool :=
  let os := cfg.orbits
  (List.range cfg.keyCount).all fun k =>
    let groups := (groupsUpTo os k).map (newPoints os)
    let pts := (os.getD k default).points
    (groups.map (·.size)).sum == pts.size &&
      pts.all fun p => groups.any fun g => g.contains p.z

/-- The picture between key `j` and key `j + 1` at the fraction `q` of the step: the circles and
the lens at the radius whose square is `(1 - q) r_j² + q r_{j+1}²`. -/
def between (j : Nat) (q : Rat) : Option Plane.Figure :=
  let a := (cfg.radius j).sqValue
  let b := (cfg.radius (j + 1)).sqValue
  some { width := figureWidth, padding := 16, style := orbitStyle, checks := .fail,
         items := diskActors
           (⟨a * TDCSGFigures.rat (1 - q) + b * TDCSGFigures.rat q⟩ : SqrtOf QSqrt5) }

/-- The step from key `j` to key `j + 1`: the exact moves, and the circles and the lens morphed. -/
def step (os : Array Orbit) (j : Nat) : MotionStep :=
  let s := exactStep (moves os j)
  { s with moves := #[("left-disk", .morph), ("right-disk", .morph), ("lens", .morph)] ++ s.moves }

/-- The pacing: `motionPacing` with a longer rest at every key, to read the line under the
disks. -/
def pacing : Anim.Pacing := { motionPacing with hold := cfg.hold, lastHold := 3 }

/-- The loop as a picture of one panel. It has no narrow rendition: at the narrow width the
closest points of the orbit at `R` would be about 3 pixels apart and read as one. -/
def motion : MotionPanels :=
  let os := cfg.orbits
  let n := cfg.keyCount
  let last := (cfg.radius (n - 2)).text
  { panels := #[{ motion :=
      { keys := ((List.range n).map (cfg.key os)).toArray,
        steps := ((List.range (n - 1)).map (step os)).toArray,
        between := cfg.between, morphSamples := cfg.samples } }]
    captions := ((List.range n).map (cfg.caption os)).toArray
    pacing := cfg.pacing
    timing := ((List.range (n - 1)).map fun _ =>
      ({ duration := some cfg.stepTime, easing := some .linear } : PanelTiming)).toArray
    info := { title := "The orbit of 0 as the radius grows"
              description := s!"The closed disks of radius r about −1 and 1, their lens, and \
                the orbit of 0 under the two moves, computed exactly, at r = \
                {", ".intercalate (cfg.radii.map (·.1)).toList} and at the critical radius R. \
                Each orbit contains the one before it: from one radius to the next the circles \
                grow through the exact circles between, and the new points of the orbit fade \
                in; nothing else moves. The orbit is finite up to r = {last} and infinite at R, \
                where its first {cfg.cap} points are drawn." }
    checks := .fail
    poster := n - 1
    width := figureWidth }

end GrowthConfig

/-! ### The figure -/

/-- The configuration of the figure: the defaults. -/
def figureConfig : GrowthConfig := {}

/-- The orbit of 0 under the two generators as the radius grows: one key at each of
r = 1.5, 1.9, 1.95, 2.05 and 2.1 (9, 9, 71, 151 and 801 points) and one at the critical radius
R = √(3 + φ), where the orbit is infinite and the first 1000 points that a breadth-first search
from 0 finds are drawn. The points of each orbit stay at the next radius, and the new ones fade in;
the circles and their lens grow between the keys. -/
@[figure illustration]
def _root_.TDCSGFigures.orbitRadius : MotionPanels := figureConfig.motion

end TDCSGFigures.OrbitLoop
