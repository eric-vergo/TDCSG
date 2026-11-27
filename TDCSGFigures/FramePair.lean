/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import PILean.Trust.Attr
import TDCSGFigures.Lift
import TDCSGFigures.Data.Turns

/-!
# The key figures of the frame pair

The two frames of chapter 4 as key figures, one per rest of a word, for an animation that turns
the moving items between consecutive keys: for any rational radius and any word in `a`, `b`,
`a⁻¹`, `b⁻¹` applied to `z = 0` (states `statesFor`), and each key,

* the left panel (`halvedKey`): the traditional view, halved: the disks of radius `r/2` about `0`
  and `1` (fixed), and the point `(y + 1)/2`, the actor `"point"`;
* the right panel (`centreKey`): the moving frame: the window of radius `r/2` about `x = 1/2`
  (fixed) and the point fixed at `x`, and the rigid body of the left centre `P(n)` (actor
  `"left"`), the right centre `P(n + eⱼ)` (actor `"right"`), the two halved disks riding on them
  (`"left-disk"`, `"right-disk"`) and the unit edge between the centres (`"edge"`).

The figure of the site is the word `TDCSGFigures.Lift.word` at `r = 1.95` (the defaults of
`FramePairConfig`); another word or radius gives the same picture for it.

**One model of the actors.** `FramePairConfig.actorsAt` gives, for each panel and key, every actor
with its id, its kind of drawing, its stable title and its exact anchor points (`Actor`). The key
figures draw the actors from it (`Actor.item`), and the exact arrival check
(`FramePairConfig.arrivesWith`) reads the same list, so a drawn item cannot drift from what is
checked.

**What stays the same across keys.** A moving item keeps its id, its kind of drawing, its look and
its base title (`Actor.base`) in every key that shows it. The incidences it records
(`Item.incident`, decided exactly on every key) and the words they append to its title change from
key to key; `baseTitle` recovers the base title from a drawn item by removing those words, which
`Item.incident` appends as `, <relation> <title>` once per record, in the order of the look's
records. What depends on the step is said in the caption (`keyCaption`) and the legends.

**Keys.** The states after `0, 1, …, |w|` letters (`stateAt`) give the keys, one per state,
except that a letter that does not act gets two: a key with its mark shown, then the state's key
without it (`keyRefs`). So the step of an idle letter is self-contained: its mark appears, is held,
and vanishes before the next letter moves.

**Idle letters.** The mark of a letter that does not act is a dashed ring about the centre of its
disk (left panel) and of its riding disk (right panel). It is an actor of its own, shown only in
the key with the mark, so nothing turns while it is shown.

**Options.** With `pivotMark`, the centre of each turn is marked by a solid ring in both panels
(the centre of the letter's halved disk on the left, the centre that stays on the right): it
appears in a key of its own before the turn, stays through the turn and gives way to the next
mark, and `FramePairConfig.pivotsPlaced` checks exactly that it lies where the declared turn
turns. With `faintDisks`, the riding disks of the right panel are drawn faint. Both are off on
the site.

**Views.** One view for all keys of a panel, both panels at one unit length, side by side in twice
the width of one panel, each cropped to its own extent and a legend above it. Each panel's height
is its own, so a narrow, stacked rendition has no empty band.

`frameSteps cfg` declares the moves between consecutive keys (`FrameStep`: a turn, or a mark that
appears or vanishes) in each panel's own coordinates, and `FramePairConfig.allArrive` checks in
exact arithmetic that each declared turn carries the actors' anchors in key `k` onto those in key
`k + 1`; the general statements are `TDCSG.Five.framePicture_genA_genB`,
`TDCSG.Five.framePicture_symm`, `TDCSG.Five.two_mul_sub_proj_genA`,
`TDCSG.Five.two_mul_sub_proj_genB`, `TDCSG.Five.halved_genA`, `TDCSG.Five.halved_genB` and
`TDCSG.Five.frameMap_genA_halved`.

`TDCSGFigures.FramePairMotion` animates the keys.
-/

namespace TDCSGFigures.Lift

open PILean PILean.Plane PILean.Exact TDCSGFigures TDCSGFigures.Early

/-- A frame pair: the word applied to `z = 0`, the radius, and the page widths of one panel. The
defaults are the figure of the site. -/
structure FramePairConfig where
  /-- The word applied to `z = 0`. -/
  word : List Letter := word
  /-- The radius `r`. -/
  radius : Rat := pairRadius
  /-- The page width of one panel; the two panels share twice this width. -/
  width : Float := figureWidth / 2
  /-- The page width of the panels stacked. -/
  narrowWidth : Float := narrowWidth
  /-- Whether the centre of each turn is marked in both panels (an option, off on the site): a
  solid ring about the centre of the letter's disk, which appears in a key of its own before the
  turn, stays through it and gives way to the next mark (`KeyRef.pivot`). -/
  pivotMark : Bool := false
  /-- Whether the riding disks of the right panel are drawn faint (an option, off on the site), so
  that the pair of centres and its edge stand out. -/
  faintDisks : Bool := false
  /-- Whether each turn is shown by an arrow about its centre in both panels (on for the site): an
  arc of three quarters of a turn with an arrowhead, in the sense of that panel's turn. It fades
  in during the rest before the turn, stays through the turn and fades out after it, in steps of
  its own between keys whose rests are short (`pacing`), so that one arrow at most is shown. -/
  arrowMark : Bool := true

/-- A key of the animation: the state after `state` letters, with the mark of the idle letter
before it shown (`mark`) or not, and with the centre of the turn of letter `i` marked
(`pivot = some i`, with `FramePairConfig.pivotMark`). -/
structure KeyRef where
  /-- The number of letters applied. -/
  state : Nat
  /-- Whether the mark of the letter before it, which does not act, is shown. -/
  mark : Bool := false
  /-- The letter (from `0`) whose turn centre is marked: before its turn (`state = i`) and after
  it (`state = i + 1`). -/
  pivot : Option Nat := none
  /-- Whether this key repeats the one before it, so that the picture rests longer (with
  `FramePairConfig.arrowMark`, the ring of a letter that does not act is held this way). -/
  held : Bool := false
  deriving BEq, Inhabited, Repr

/-- The two panels. -/
inductive Panel where
  /-- The traditional view. -/
  | left
  /-- The moving frame. -/
  | right
  deriving BEq, Inhabited, Repr

namespace FramePairConfig

variable (cfg : FramePairConfig)

/-- `r²`. -/
def r2 : QSqrt5 := rat (cfg.radius * cfg.radius)

/-- `r/2`. -/
def half : Rat := cfg.radius / 2

/-- The states after `0, 1, …, |w|` letters. -/
def states : List State := statesFor cfg.r2 cfg.word

/-- The state at key `k`. -/
def stateAt (k : Nat) : State := cfg.states.getD k (State.start origin)

/-- The letter of step `k`, from key `k` to key `k + 1`. -/
def letterOf (k : Nat) : Letter := cfg.word.getD k .a

/-- Whether the letter before state `k` did not act (`k ≥ 1`). -/
def idleAt (k : Nat) : Bool := k ≥ 1 && !(cfg.stateAt k).acted

/-- The keys (see the module docstring): state `0`, then for each letter the state it reaches,
preceded by the same state with the letter's mark shown when the letter does not act.

With `arrowMark`, a letter that acts gets three keys: the state before it with its turn marked,
the state it reaches with the mark still shown, and that state without the mark; a letter that
does not act gets its ring, the ring held, and the state without it. Otherwise, with
`pivotMark`, a letter that acts gets two keys: the state before it with its turn marked, then the
state it reaches with the mark still shown. -/
def keyRefs : List KeyRef :=
  { state := 0 } :: (List.range cfg.word.length).flatMap fun i =>
    if cfg.idleAt (i + 1) then
      if cfg.arrowMark then
        [{ state := i + 1, mark := true }, { state := i + 1, mark := true, held := true },
          { state := i + 1 }]
      else [{ state := i + 1, mark := true }, { state := i + 1 }]
    else if cfg.arrowMark then
      [{ state := i, pivot := some i }, { state := i + 1, pivot := some i }, { state := i + 1 }]
    else if cfg.pivotMark then
      [{ state := i, pivot := some i }, { state := i + 1, pivot := some i }]
    else [{ state := i + 1 }]

/-- The letters that act, in order: each one's position (from `0`) and the side of its disk
(`0` left, `1` right), which is the side of the centre the turn is about in both panels. -/
def actingSides : List (Nat × Nat) :=
  (List.range cfg.word.length).filterMap fun i =>
    if (cfg.stateAt (i + 1)).acted then
      some (i, match cfg.letterOf i with | .a | .aInv => 0 | .b | .bInv => 1)
    else none

/-- Whether the centre of the turns alternates: two consecutive letters that act turn about the
same centre exactly when a letter that does not act lies between them. -/
def pivotsAlternate : Bool :=
  let xs := cfg.actingSides
  (xs.zip xs.tail).all fun ((i, a), (k, b)) => (a == b) == decide (k > i + 1)

/-- Whether every letter is decided by a margin of at least `d`: the centre of its disk lies at
distance at most `r/2 - d` or at least `r/2 + d` from the window centre `x = 1/2`, decided exactly
(`windowDistSq4`, which is `4 |P - x|²`). -/
def marginsVisible (d : Rat) : Bool :=
  (cfg.word.zip cfg.states).all fun (l, s) =>
    let d2 := windowDistSq4 origin (s.labelOf l)
    QSqrt.le d2 (rat (4 * (cfg.half - d) * (cfg.half - d))) ||
      QSqrt.le (rat (4 * (cfg.half + d) * (cfg.half + d))) d2

/-- The number of keys (`keyRefs`). -/
def keyCount : Nat := cfg.keyRefs.length

/-- Key `j`. -/
def keyRef (j : Nat) : KeyRef := cfg.keyRefs.getD j { state := 0 }

/-- The fixed disks of the left panel, `(title, centre, radius)`, left then right: the disks of
radius `r/2` about `0` and `1`. -/
def leftDisks : List (String × ZetaFrac × Rat) :=
  [("the left disk, halved", ZetaFrac.ofZeta origin, cfg.half),
    ("the right disk, halved", ZetaFrac.ofZeta rightCentre, cfg.half)]

end FramePairConfig

/-- `0` for `a` and `a⁻¹` (the left disk), `1` for `b` and `b⁻¹`. -/
def sideIndex (l : Letter) : Nat := match l with | .a | .aInv => 0 | .b | .bInv => 1

/-! ### Exact points -/

/-- The window centre `x = 1/2` as a point of `ℚ(ζ₅)`. -/
def windowCentre : ZetaFrac := ⟨Zeta5.ofInt 1, 2⟩

/-- Where a point stands relative to the closed disk of radius `ρ` about `c`, decided exactly. -/
def sideTo (p c : ZetaFrac) (ρ : Rat) : Plane.Incidence :=
  (sideOfSq (p - c).normSq (rat (ρ * ρ))).incidence

/-- Whether the point `x` lies on the segment from `a` to `b`, `|b - a| = 1`: `(x - a) (b - a)‾`
is real and between `0` and `1`, decided exactly. -/
def onSegment (x a b : ZetaFrac) : Bool :=
  let d := b.num * Zeta5.ofInt a.den - a.num * Zeta5.ofInt b.den
  let w := (x.num * Zeta5.ofInt a.den - a.num * Zeta5.ofInt x.den) * d.conj
  let scale : Rat := (x.den * a.den * a.den * b.den : Nat)
  w == w.conj && QSqrt.le (rat 0) w.realPart && QSqrt.le w.realPart (rat scale)

/-! ### Actors -/

/-- How an actor is drawn from its anchors. -/
inductive ActorKind where
  /-- A point marker at the first anchor: its size and role. -/
  | dot (size : Float) (role : Option String)
  /-- A circle of radius `ρ` about the first anchor: its role, stroke width, whether dashed. -/
  | outline (ρ : Rat) (role : Option String) (width : Float) (dashed : Bool)
  /-- The segment between the first two anchors: its role and stroke width. -/
  | stroke (role : Option String) (width : Float)
  /-- An arrow about the first anchor: an arc of `radius` pixels through `sweep` of a full turn,
  counterclockwise when `sweep > 0`, with an arrowhead at its end (`Plane.angleMark`), leaving open
  the part of the circle about the direction to the second anchor (`arrowStart`); its role and
  stroke width. -/
  | turnArrow (radius : Float) (sweep : Rat) (role : Option String) (width : Float)
  deriving BEq, Inhabited, Repr

/-- A full turn in radians. -/
def tau : Float := 2 * 3.141592653589793

/-- The angle (radians) where the arrow of a turn by `q` about `c` starts. The arrow leaves a
quarter of a turn open, centred on the direction from `c` to `p` halfway through the turn (`p` the
point that turns, or the other centre of the pair), so that what turns stays in the open part. -/
def arrowStart (c p : ZetaFrac) (q : Rat) : Float :=
  let a := PlanePoint.toPoint c
  let b := PlanePoint.toPoint p
  let σ : Float := if q < 0 then -1 else 1
  Float.atan2 (b.y - a.y) (b.x - a.x) + σ * (tau / 10 + tau / 8)

/-- A moving item of a key: its id, its kind of drawing, its base title (the same in every key),
its exact anchor points, the incidences it records in this key, and the Lean declaration it
links to. -/
structure Actor where
  /-- The id. -/
  id : String
  /-- How it is drawn. -/
  kind : ActorKind
  /-- The title, without the words of the recorded incidences. -/
  base : String
  /-- The exact points that fix the drawing. -/
  anchors : List ZetaFrac
  /-- The incidences recorded in this key. -/
  records : List (Plane.Incidence × String) := []
  /-- The Lean declaration it shows. -/
  decl : Option Lean.Name := none
  /-- Whether it is drawn faint. -/
  faint : Bool := false

/-- The actor as an item: its geometry from its anchors only, its base title, its recorded
incidences and its id. -/
def Actor.item (a : Actor) : Item :=
  let p0 := a.anchors.getD 0 (ZetaFrac.ofZeta origin)
  let p1 := a.anchors.getD 1 p0
  let withRole := fun (r : Option String) (it : Item) => match r with
    | some r => it.role r
    | none => it
  let geom : Item := match a.kind with
    | .dot s r => withRole r (Plane.Exact.point p0 |>.size s)
    | .outline ρ r w dashed =>
      let it := withRole r (Plane.Exact.circle p0 ρ |>.width w)
      if dashed then it.dashed else it
    | .stroke r w => withRole r (Plane.Exact.segment p0 p1 |>.width w)
    | .turnArrow ρ q r w =>
      let θ := arrowStart p0 p1 q
      withRole r (Plane.angleMark (PlanePoint.toPoint p0) θ (θ + tau * Exact.toFloat q) (some ρ)
        |>.width w)
  let named := (if a.faint then geom.faint else geom).named a.base
  let linked := match a.decl with
    | some d => named.declRef d
    | none => named
  (a.records.foldl (fun it (rel, what) => it.incident rel what) linked).withId a.id

/-- The base title of a drawn item: its title without the words that its recorded incidences
appended (`Item.incident` appends `, <relation> <title>` for each record, in the order of the
look's records); `none` when the title does not end with them. -/
def baseTitle : Item → Option String
  | .shape _ look info =>
    let suffix := String.join (look.incidences.toList.map fun (rel, what) =>
      s!", {rel.text} {what}")
    if info.title.endsWith suffix then
      some (String.ofList (info.title.toList.take (info.title.length - suffix.length)))
    else none
  | .group .. => none

/-- The incidences of a point relative to circles `(title, centre, radius)` and segments
`(title, end, end)` it lies on, decided exactly. -/
def recordsOf (p : ZetaFrac) (circles : List (String × ZetaFrac × Rat))
    (segments : List (String × ZetaFrac × ZetaFrac)) : List (Plane.Incidence × String) :=
  circles.map (fun (name, c, ρ) => (sideTo p c ρ, name)) ++
    segments.filterMap fun (name, a, b) => if onSegment p a b then some (.on, name) else none

namespace FramePairConfig

variable (cfg : FramePairConfig)

/-- The point `(y + 1)/2` of the left panel at state `k`. -/
def pointAt (k : Nat) : ZetaFrac := halved (cfg.stateAt k).y

/-- The centres of the right panel at state `k`. -/
def centresAt (k : Nat) : ZetaFrac × ZetaFrac :=
  let s := cfg.stateAt k
  (ZetaFrac.ofZeta s.leftCentre, ZetaFrac.ofZeta s.rightCentre)

/-- The turn of step `k` in the right panel when its letter acts: the active centre (the centre
of the letter's disk at key `k`) and the fraction, `1/5`, or `-1/5` for an inverse. -/
def bodyTurnOf (k : Nat) : Option (ZetaFrac × Rat) :=
  let s := cfg.stateAt k
  let l := cfg.letterOf k
  if l.covers cfg.r2 s.y then some (ZetaFrac.ofZeta (proj (s.labelOf l)), -l.turns) else none

end FramePairConfig

/-! ### The actors of each panel -/

/-- The radius of the ring that marks an idle letter, at the unit length of both panels. -/
def ringRadius : Rat := 1 / 4

/-- The ring of the idle letter before state `k`, about the centre `c` of its disk titled
`name`. -/
def idleActor (k : Nat) (c : ZetaFrac) (role : String) (name : String) : Actor :=
  { id := s!"idle-{k}", kind := .outline ringRadius (some role) 2 true,
    base := s!"a ring about the center of {name}: its letter does not act", anchors := [c] }

/-- The radius of the ring that marks the centre of a turn. -/
def pivotRadius : Rat := 1 / 6

/-- The ring that marks the centre `c` of the turn of letter `i` (from `0`), about the centre of
the disk titled `name`. -/
def pivotActor (i : Nat) (c : ZetaFrac) (role : String) (name : String) : Actor :=
  { id := s!"pivot-{i}", kind := .outline pivotRadius (some role) 3 false,
    base := s!"a solid ring about the center of {name}: the center of the turn", anchors := [c] }

/-- The sweep of a turn's arrow: three quarters of a full turn, in the sense of the turn `q`
(counterclockwise when `q > 0`). -/
def arrowSweep (q : Rat) : Rat := if q < 0 then -3 / 4 else 3 / 4

/-- The arrow of the turn of letter `i` (from `0`) by `q` about `c`, `p` the point that turns, of
`radius` pixels, about the centre of the disk titled `name`. -/
def arrowActor (i : Nat) (c p : ZetaFrac) (q : Rat) (radius : Float) (role : String)
    (name : String) : Actor :=
  { id := s!"arrow-{i}", kind := .turnArrow radius (arrowSweep q) (some role) 2,
    base := s!"an arrow about the center of {name}: the turn of the letter", anchors := [c, p] }

/-- The radius of the arrows of the left panel, in pixels. -/
def leftArrowRadius : Float := 12

/-- The radius of the arrows of the right panel, in pixels. -/
def rightArrowRadius : Float := 15

namespace FramePairConfig

variable (cfg : FramePairConfig)

/-- The letter whose turn centre key `r` marks, when it acts: its index and the letter. -/
def pivotOf (r : KeyRef) : Option (Nat × Letter) :=
  match r.pivot with
  | some i =>
    let l := cfg.letterOf i
    if l.covers cfg.r2 (cfg.stateAt i).y then some (i, l) else none
  | none => none

/-- The pivot ring of key `r` in the left panel, about the halved centre of the letter's disk
(with `pivotMark`). -/
def leftPivot (r : KeyRef) : List Actor :=
  if !cfg.pivotMark then [] else
  match cfg.pivotOf r with
  | some (i, l) =>
    let side := sideIndex l
    let (name, c, _) := cfg.leftDisks.getD side ("", ZetaFrac.ofZeta origin, 0)
    [pivotActor i c (if side == 0 then leftRole else rightRole) name]
  | none => []

/-- The pivot ring of key `r` in the right panel, about the centre of the letter's disk before
its turn (`bodyTurnOf`), which the turn leaves in place (with `pivotMark`). -/
def rightPivot (r : KeyRef) : List Actor :=
  if !cfg.pivotMark then [] else
  match cfg.pivotOf r with
  | some (i, l) =>
    match cfg.bodyTurnOf i with
    | some (c, _) =>
      let (role, name) := if sideIndex l == 0 then (leftRole, "the left disk, riding")
        else (rightRole, "the right disk, riding")
      [pivotActor i c role name]
    | none => []
  | none => []

/-- The arrow of key `r` in the left panel (with `arrowMark`): about the halved centre of the
letter's disk, in the sense of the point's turn (`Letter.turns`), open towards the point. -/
def leftArrow (r : KeyRef) : List Actor :=
  if !cfg.arrowMark then [] else
  match cfg.pivotOf r with
  | some (i, l) =>
    let side := sideIndex l
    let (name, c, _) := cfg.leftDisks.getD side ("", ZetaFrac.ofZeta origin, 0)
    [arrowActor i c (halved (cfg.stateAt i).y) l.turns leftArrowRadius
      (if side == 0 then leftRole else rightRole) name]
  | none => []

/-- The arrow of key `r` in the right panel (with `arrowMark`): about the centre of the letter's
disk before its turn, in the sense of the turn of the pair (`bodyTurnOf`), open towards the other
centre. -/
def rightArrow (r : KeyRef) : List Actor :=
  if !cfg.arrowMark then [] else
  match cfg.pivotOf r with
  | some (i, l) =>
    match cfg.bodyTurnOf i with
    | some (c, q) =>
      let (pl, pr) := cfg.centresAt i
      let (other, role, name) := if sideIndex l == 0 then (pr, leftRole, "the left disk, riding")
        else (pl, rightRole, "the right disk, riding")
      [arrowActor i c other q rightArrowRadius role name]
    | none => []
  | none => []

/-- The circle of the idle mark of key `r` in the left panel, for the records of the points. -/
def leftIdleCircle (r : KeyRef) : List (String × ZetaFrac × Rat) :=
  if r.mark then
    let (name, c, _) := cfg.leftDisks.getD (sideIndex (cfg.letterOf (r.state - 1)))
      ("", ZetaFrac.ofZeta origin, 0)
    [((idleActor r.state c "" name).base, c, ringRadius)]
  else []

/-- The actors of the left panel at key `r`, in drawing order: the fixed centres, the idle mark,
the point. -/
def leftActors (r : KeyRef) : List Actor :=
  let k := r.state
  let disks := cfg.leftDisks
  let pivot := cfg.leftPivot r
  let circles := disks ++ cfg.leftIdleCircle r ++
    pivot.map fun a => (a.base, a.anchors.getD 0 (ZetaFrac.ofZeta origin), pivotRadius)
  let centres := (disks.zipIdx.map fun ((_, c, _), i) =>
    let (role, name) := if i == 0 then (leftRole, "the left center 0")
      else (rightRole, "the right center 1")
    ({ id := s!"center-{i}", kind := .dot 4 (some role), base := name,
       anchors := [c], records := recordsOf c circles [] } : Actor))
  let idleA : List Actor :=
    if r.mark then
      let i := sideIndex (cfg.letterOf (k - 1))
      let (name, c, _) := disks.getD i ("", ZetaFrac.ofZeta origin, 0)
      [idleActor k c (if i == 0 then leftRole else rightRole) name]
    else []
  let p := cfg.pointAt k
  centres ++ idleA ++ pivot ++ cfg.leftArrow r ++
    [{ id := "point", kind := .dot 5 none, base := "the point (y + 1)/2",
       anchors := [p], records := recordsOf p circles [] }]

/-- The title of the edge between the centres. -/
def edgeName : String := "the unit edge from the left to the right center"

/-- The actors of the right panel at key `r`, in drawing order: the riding disks, the idle mark,
the edge, the point at `x`, the centres. -/
def rightActors (r : KeyRef) : List Actor :=
  let k := r.state
  let (pl, pr) := cfg.centresAt k
  let x := windowCentre
  let ρ := cfg.half
  let window : List (String × ZetaFrac × Rat) := [("the window", x, ρ)]
  let riding : List (String × ZetaFrac × Rat) :=
    [("the left disk, riding", pl, ρ), ("the right disk, riding", pr, ρ)]
  let idle : List Actor :=
    if r.mark then
      let i := sideIndex (cfg.letterOf (k - 1))
      let (c, role, name) := if i == 0 then (pl, leftRole, "the left disk, riding")
        else (pr, rightRole, "the right disk, riding")
      [idleActor k c role name]
    else []
  let idleCircles : List (String × ZetaFrac × Rat) :=
    idle.map fun a => (a.base, a.anchors.getD 0 x, ringRadius)
  let pivot := cfg.rightPivot r
  let pivotCircles : List (String × ZetaFrac × Rat) :=
    pivot.map fun a => (a.base, a.anchors.getD 0 x, pivotRadius)
  let circles := window ++ riding ++ idleCircles ++ pivotCircles
  let segments : List (String × ZetaFrac × ZetaFrac) := [(edgeName, pl, pr)]
  let disks : List Actor := [
    { id := "left-disk", kind := .outline ρ (some leftRole) 1.5 false,
      base := "the left disk, riding", anchors := [pl], faint := cfg.faintDisks },
    { id := "right-disk", kind := .outline ρ (some rightRole) 1.5 false,
      base := "the right disk, riding", anchors := [pr], faint := cfg.faintDisks }]
  let edge : Actor :=
    { id := "edge", kind := .stroke none 1.5, base := edgeName, anchors := [pl, pr] }
  let xActor : Actor :=
    { id := "x", kind := .dot 5 none, base := "the point, fixed at x = 1/2",
      anchors := [x], records := recordsOf x riding segments }
  let others := fun (q : ZetaFrac) => circles.filter fun (_, c, _) => !(ZetaFrac.same c q)
  let centres : List Actor := [
    { id := "left", kind := .dot 5 (some leftRole), base := "the left center P(n)",
      anchors := [pl], records := recordsOf pl (others pl) [],
      decl := some `TDCSG.Five.Label.proj },
    { id := "right", kind := .dot 5 (some rightRole), base := "the right center P(n + eⱼ)",
      anchors := [pr], records := recordsOf pr (others pr) [] }]
  disks ++ idle ++ pivot ++ cfg.rightArrow r ++ [edge, xActor] ++ centres

/-- The actors of a panel at key `j` (`leftActors`, `rightActors` of `keyRef j`): the one list
that the key figures draw and the arrival check reads. -/
def actorsAt : Panel → Nat → List Actor
  | .left, j => cfg.leftActors (cfg.keyRef j)
  | .right, j => cfg.rightActors (cfg.keyRef j)

end FramePairConfig

/-! ### The moves -/

/-- What a step between two keys does: the turn of a letter that acts, or the mark of a letter
that does not act appearing or vanishing. -/
inductive StepPhase where
  /-- A letter acts: both panels turn. -/
  | turn
  /-- A letter does not act: its mark appears. -/
  | markAppears
  /-- The mark of a letter that does not act vanishes. -/
  | markVanishes
  /-- The centre of the next turn is marked (with `FramePairConfig.pivotMark` or `arrowMark`); a
  mark of the turn before vanishes. -/
  | pivotShown
  /-- Nothing changes: the picture rests longer (`KeyRef.held`). -/
  | pause
  deriving DecidableEq, Inhabited, Repr

/-- What happens between key `j` and key `j + 1`, in each panel's own coordinates: the letter, what
the step does, whether the letter acts, the turn of the left panel (of the actor `"point"` about the
centre `0` or `1` of the letter's halved disk, by `-1/5` for `a` and `b`, `1/5` for their
inverses) and the turn of the right panel (about the centre of the letter's disk before the turn,
by `1/5`, or `-1/5` for an inverse), the actors each turns, and the actors that appear and vanish
in each panel. -/
structure FrameStep where
  /-- The letter. -/
  letter : Letter
  /-- What the step does. -/
  phase : StepPhase
  /-- Whether the letter acts (then the step turns). -/
  acts : Bool
  /-- The turn of the left panel, when the letter acts. -/
  leftTurn : Option ExactTurn
  /-- The actors of the left panel that turn. -/
  leftTurning : List String
  /-- The turn of the right panel, when the letter acts. -/
  rightTurn : Option ExactTurn
  /-- The actors of the right panel that turn: the edge, the other centre and its riding disk. -/
  rightTurning : List String
  /-- The actors of the left panel that appear in this step. -/
  appearLeft : List String
  /-- The actors of the left panel that vanish in this step. -/
  vanishLeft : List String
  /-- The actors of the right panel that appear in this step. -/
  appearRight : List String
  /-- The actors of the right panel that vanish in this step. -/
  vanishRight : List String

namespace FramePairConfig

variable (cfg : FramePairConfig)

/-- The moves of step `j`, from key `j` to key `j + 1`, with the actors given by `actors` (the
appearances and disappearances are read from it): the letter `i` that leads to the state of key
`j + 1`; a turn when the two keys show different states (the letter acts), the mark appearing when
key `j + 1` shows it, the mark vanishing when both keys show one state. The right panel turns the
edge and the other centre with its riding disk. -/
def frameStepWith (actors : Panel → Nat → List Actor) (j : Nat) : FrameStep :=
  let r := cfg.keyRef j
  let r' := cfg.keyRef (j + 1)
  let i := r'.state - 1
  let s := cfg.stateAt i
  let l := cfg.letterOf i
  let phase : StepPhase :=
    if r.state == r'.state then
      (if r'.held then .pause else if r'.pivot.isSome then .pivotShown else .markVanishes)
    else if r'.mark then .markAppears else .turn
  let acts := phase == .turn && l.covers cfg.r2 s.y
  let ids := fun (p : Panel) (j : Nat) => (actors p j).map (·.id)
  let diff := fun (xs ys : List String) => ys.filter fun id => !xs.contains id
  let side := sideIndex l
  let other := if side == 0 then ["right", "right-disk"] else ["left", "left-disk"]
  { letter := l, phase, acts
    leftTurn := if acts then
      some ⟨(cfg.leftDisks.getD side ("", ZetaFrac.ofZeta origin, 0)).2.1, l.turns⟩ else none
    leftTurning := if acts then ["point"] else []
    rightTurn := if acts then (cfg.bodyTurnOf i).map fun (c, q) => ⟨c, q⟩ else none
    rightTurning := if acts then
      ("edge" :: other).filter fun id =>
        (ids .right j).contains id && (ids .right (j + 1)).contains id
      else []
    appearLeft := diff (ids .left j) (ids .left (j + 1))
    vanishLeft := diff (ids .left (j + 1)) (ids .left j)
    appearRight := diff (ids .right j) (ids .right (j + 1))
    vanishRight := diff (ids .right (j + 1)) (ids .right j) }

/-- The moves of step `j` (`frameStepWith actorsAt`). -/
def frameStep (j : Nat) : FrameStep := cfg.frameStepWith cfg.actorsAt j

/-- The steps between consecutive keys, one fewer than the keys. -/
def frameSteps : List FrameStep := (List.range (cfg.keyCount - 1)).map cfg.frameStep

/-- Whether, in one panel, the turn `turn` of the actors `turning` carries the actors of `before`
onto those of `after`: every actor in both has the same kind and base title, a turning actor's
anchors turned exactly (`ZetaFrac.turnAbout`, `turnFactor`) are the next ones, every other
actor's anchors are unchanged; an actor in one list only must be an appearance or a
disappearance. -/
def panelArrives (turn : Option ExactTurn) (turning appear vanish : List String)
    (before after : List Actor) : Bool :=
  let τ? := turn.bind (turnFactor ·.turns)
  (turn.isNone || τ?.isSome) &&
  before.all (fun a =>
    match after.find? (·.id == a.id) with
    | none => vanish.contains a.id
    | some b =>
      a.kind == b.kind && a.base == b.base && a.anchors.length == b.anchors.length &&
        (a.anchors.zip b.anchors).all fun (p, q) =>
          if turning.contains a.id then
            match turn, τ? with
            | some t, some τ => ZetaFrac.same (ZetaFrac.turnAbout t.centre τ p) q
            | _, _ => false
          else ZetaFrac.same p q) &&
  after.all fun b => before.any (·.id == b.id) || appear.contains b.id

/-- Whether the declared moves of step `k` carry the actors of key `k` onto those of key `k + 1`
in both panels, with the actors given by `actors`. -/
def arrivesWith (actors : Panel → Nat → List Actor) (k : Nat) : Bool :=
  let st := cfg.frameStepWith actors k
  panelArrives st.leftTurn st.leftTurning st.appearLeft st.vanishLeft
      (actors .left k) (actors .left (k + 1)) &&
    panelArrives st.rightTurn st.rightTurning st.appearRight st.vanishRight
      (actors .right k) (actors .right (k + 1)) &&
    (st.acts == (st.phase == .turn)) &&
    (st.acts || (st.leftTurn.isNone && st.rightTurn.isNone))

/-- Whether every step of the frame pair arrives, with the actors given by `actors`. -/
def allArriveWith (actors : Panel → Nat → List Actor) : Bool :=
  (List.range (cfg.keyCount - 1)).all (cfg.arrivesWith actors)

/-- Whether the ring of every letter that does not act is where it belongs, decided exactly: in
the key that shows it, the left panel's ring lies about the halved centre `(c + 1)/2` of the
letter's disk (`0` or `1`), the right panel's about the centre `P(m)` of that disk in the moving
frame (`m` the label of the letter's centre, `State.labelOf`), and that centre lies outside the
window (`inWindowFrom` is false); with the actors given by `actors`. -/
def ringsPlacedWith (actors : Panel → Nat → List Actor) : Bool :=
  (List.range cfg.keyCount).all fun j =>
    let r := cfg.keyRef j
    if !r.mark then true
    else
      let s := cfg.stateAt (r.state - 1)
      let l := cfg.letterOf (r.state - 1)
      let ringAt := fun (p : Panel) (c : ZetaFrac) =>
        (actors p j).any fun a => a.id == s!"idle-{r.state}" &&
          a.anchors.length == 1 && a.anchors.all (ZetaFrac.same · c)
      ringAt .left (halved l.centre) && ringAt .right (ZetaFrac.ofZeta (proj (s.labelOf l))) &&
        !inWindowFrom cfg.r2 origin (s.labelOf l)

/-- `ringsPlacedWith` for the actors the key figures draw (`actorsAt`). -/
def ringsPlaced : Bool := cfg.ringsPlacedWith cfg.actorsAt

/-- Whether the turn centres are marked where the turns turn, decided exactly, with the actors
given by `actors`: no key shows more than one pivot ring in a panel; with `pivotMark`, every turn
step `j` shows the ring of its letter in both keys `j` and `j + 1` and in both panels, about the
declared centre of that panel's turn (`leftTurn`, `rightTurn`); without it, no key shows one. -/
def pivotsPlacedWith (actors : Panel → Nat → List Actor) : Bool :=
  let rings := fun (p : Panel) (k : Nat) => (actors p k).filter (·.id.startsWith "pivot-")
  (List.range cfg.keyCount).all (fun k =>
    [Panel.left, .right].all fun p =>
      (rings p k).length ≤ (if cfg.pivotMark then 1 else 0)) &&
  (!cfg.pivotMark ||
    (List.range (cfg.keyCount - 1)).all fun j =>
      let st := cfg.frameStepWith actors j
      if st.phase != .turn then true
      else
        let id := s!"pivot-{(cfg.keyRef (j + 1)).state - 1}"
        let ringAt := fun (p : Panel) (k : Nat) (c : ZetaFrac) =>
          (rings p k).any fun a => a.id == id && a.anchors.length == 1 &&
            a.anchors.all (ZetaFrac.same · c)
        match st.leftTurn, st.rightTurn with
        | some lt, some rt =>
          [j, j + 1].all fun k => ringAt .left k lt.centre && ringAt .right k rt.centre
        | _, _ => false)

/-- `pivotsPlacedWith` for the actors the key figures draw (`actorsAt`). -/
def pivotsPlaced : Bool := cfg.pivotsPlacedWith cfg.actorsAt

/-- The letter (from `0`) whose turn step `j` is, with the actors given by `actors`, when the step
is a turn. -/
def turnLetterWith (actors : Panel → Nat → List Actor) (j : Nat) : Option Nat :=
  if (cfg.frameStepWith actors j).phase == .turn then some ((cfg.keyRef (j + 1)).state - 1)
  else none

/-- Whether the arrows show the turns, decided exactly, with the actors given by `actors`: no key
shows more than one arrow in a panel, and an arrow shown in key `k` is the arrow of the turn of
step `k` or of step `k - 1`; with `arrowMark`, every turn step `j` shows the arrow of its letter
in both keys `j` and `j + 1` and in both panels, about the declared centre of that panel's turn
(`leftTurn`, `rightTurn`) and in its sense (the sweep has the sign of the declared fraction);
without it, no key shows one. -/
def arrowsPlacedWith (actors : Panel → Nat → List Actor) : Bool :=
  let arrows := fun (p : Panel) (k : Nat) => (actors p k).filter (·.id.startsWith "arrow-")
  let idOf := fun (i : Nat) => s!"arrow-{i}"
  (List.range cfg.keyCount).all (fun k =>
    [Panel.left, .right].all fun p =>
      (arrows p k).length ≤ (if cfg.arrowMark then 1 else 0) &&
      (arrows p k).all fun a =>
        (cfg.turnLetterWith actors k).map idOf == some a.id ||
          (k ≥ 1 && (cfg.turnLetterWith actors (k - 1)).map idOf == some a.id)) &&
  (!cfg.arrowMark ||
    (List.range (cfg.keyCount - 1)).all fun j =>
      match cfg.turnLetterWith actors j with
      | none => true
      | some i =>
        let st := cfg.frameStepWith actors j
        let arrowAt := fun (p : Panel) (k : Nat) (t : ExactTurn) =>
          (arrows p k).any fun a => a.id == idOf i &&
            (a.anchors.head?.map (ZetaFrac.same · t.centre)) == some true &&
            match a.kind with
            | .turnArrow _ q _ _ => q != 0 && t.turns != 0 && (q < 0) == (t.turns < 0)
            | _ => false
        match st.leftTurn, st.rightTurn with
        | some lt, some rt =>
          [j, j + 1].all fun k => arrowAt .left k lt && arrowAt .right k rt
        | _, _ => false)

/-- `arrowsPlacedWith` for the actors the key figures draw (`actorsAt`). -/
def arrowsPlaced : Bool := cfg.arrowsPlacedWith cfg.actorsAt

/-- Whether every declared move of the frame pair carries key `k` onto key `k + 1` exactly, for
the actors the key figures draw (`actorsAt`), and every ring sits about its letter's centre
(`ringsPlaced`), every turn centre is marked where its turn turns (`pivotsPlaced`), and every
arrow lies about its turn's centre in its turn's sense (`arrowsPlaced`); and the declared
fractions are the letters' own fifths (`turnsAreFifths`). The general statements behind it:
`TDCSG.Five.halved_genA`, `halved_genB`, `halved_permA_symm`, `halved_permB_symm` (left panel),
`TDCSG.Five.two_mul_sub_proj_genA`, `two_mul_sub_proj_genB`, `two_mul_sub_proj_permA_symm`,
`two_mul_sub_proj_permB_symm`, `frameMap_genA_halved` and `framePicture_genA_genB` (right
panel). -/
def allArrive : Bool :=
  turnsAreFifths && cfg.allArriveWith cfg.actorsAt && cfg.ringsPlaced && cfg.pivotsPlaced &&
    cfg.arrowsPlaced

/-- Whether every actor of every key, drawn (`Actor.item`), gives back its base title
(`baseTitle`). -/
def baseTitlesRecoverable : Bool :=
  (List.range cfg.keyCount).all fun k =>
    [Panel.left, .right].all fun p =>
      (cfg.actorsAt p k).all fun a => baseTitle a.item == some a.base

/-! ### Captions -/

/-- A non-breaking space. -/
def nbsp : String := " "

/-- The label `n` and the index `j` of a state, as a parenthesis that does not break inside. -/
def whereText (s : State) : String :=
  let n := ("," ++ nbsp).intercalate (s.n.toList.map fun k =>
    if k < 0 then s!"−{-k}" else toString k)
  s!"(n{nbsp}={nbsp}({n}), j{nbsp}={nbsp}{s.j})"

/-- The caption of key `j`, in plain words from the states, without a counter (a page numbers the
keys itself): at the start, what the panels show and what `n` and `j` are; after a letter that
acts, which way the point and the other centre turn, a fifth of a turn each, about which centre;
for a letter that does not act, its mark and why nothing moves, then, on the key after it, that
the state is unchanged; `n` and `j` in a trailing parenthesis. -/
def keyCaption (j : Nat) : String :=
  let r := cfg.keyRef j
  let k := r.state
  let s := cfg.stateAt k
  if let some (i, l) := (cfg.pivotOf r).filter (·.1 == k) then
    let (own, ownName) := match l with
      | .a | .aInv => ("left", "0")
      | .b | .bInv => ("right", "1")
    let (pointWay, centreWay) := match l with
      | .a | .b => ("clockwise", "counterclockwise")
      | .aInv | .bInv => ("counterclockwise", "clockwise")
    let arrows := if cfg.arrowMark then
        s!" Arrows show the turn: {pointWay} about the {own} center {ownName} on the left, " ++
          s!"{centreWay} about the {own} center in the moving frame."
      else ""
    let ring := if cfg.pivotMark then
        s!" A solid ring marks the {own} center {ownName} and, in the moving frame, the {own} " ++
          "center, about which both panels turn."
      else ""
    s!"Letter {i + 1}, {l.text}, is next: the point lies in the {own} disk, so it acts." ++
      arrows ++ ring ++ s!" {whereText s}"
  else if k == 0 then
    "Start: z = 0, so x = 1/2. Left: the disks halved, with centers 0 and 1, and the point " ++
      "(y + 1)/2. Right: the window about x, the point fixed at x, and the left and right " ++
      "centers P(n) and P(n + eⱼ) with the halved disks riding on them; n is the integer label " ++
      "of the left center, j the index of the direction from the left to the right center " ++
      s!"{whereText s}."
  else
    let l := cfg.letterOf (k - 1)
    let (own, other, ownName) := match l with
      | .a | .aInv => ("left", "right", "0")
      | .b | .bInv => ("right", "left", "1")
    let (pointWay, centreWay) := match l with
      | .a | .b => ("clockwise", "counterclockwise")
      | .aInv | .bInv => ("counterclockwise", "clockwise")
    let letter := s!"Letter {k}, {l.text},"
    if s.acted && cfg.arrowMark && r.pivot.isNone then
      s!"After letter {k}, {l.text}: the point has turned a fifth of a turn {pointWay} about " ++
        s!"the {own} center {ownName}, and in the moving frame the {other} center a fifth of a turn " ++
        s!"{centreWay} about the {own} center. {whereText s}"
    else if s.acted then
      s!"{letter} acts: the point turns a fifth of a turn {pointWay} about the {own} center " ++
        s!"{ownName}; in the moving frame the {other} center turns a fifth of a turn " ++
        s!"{centreWay} about the {own} center. {whereText s}"
    else if r.held then
      s!"{letter} does not act (held): a ring marks the {own} center in both panels, and " ++
        s!"nothing moves. {whereText s}"
    else if r.mark then
      s!"{letter} does not act: the point lies outside the {own} disk, and in the moving frame " ++
        s!"the {own} center lies outside the window; a ring marks that center in both panels, " ++
        s!"and nothing moves. {whereText s}"
    else s!"{letter} did not act: the state is unchanged. {whereText s}"

end FramePairConfig

/-! ### The key figures -/

namespace FramePairConfig

variable (cfg : FramePairConfig)

end FramePairConfig

/-- A key of a panel: the fixed items, then the actors drawn from `actorsAt`. -/
def FramePairConfig.keyFigure (cfg : FramePairConfig) (p : Panel) (fixed : Array Item)
    (k : Nat) : Plane.Figure :=
  { width := cfg.width
    narrowWidth := some cfg.narrowWidth
    padding := 16
    style := partTwoStyle
    checks := .fail
    items := fixed ++ (cfg.actorsAt p k).toArray.map Actor.item
    info := { title := cfg.keyCaption k } }

/-- Key `k` of the left panel: the fixed disks, then the actors of `leftActors`. -/
def FramePairConfig.halvedKey (cfg : FramePairConfig) (k : Nat) : Plane.Figure :=
  let fixed := (cfg.leftDisks.toArray.mapIdx fun i (name, c, ρ) =>
    Plane.Exact.disk c ρ |>.noFill |>.role (if i == 0 then leftRole else rightRole) |>.named name)
  cfg.keyFigure .left fixed k

/-- Key `k` of the right panel: the window, then the actors of `rightActors`. -/
def FramePairConfig.centreKey (cfg : FramePairConfig) (k : Nat) : Plane.Figure :=
  let fixed := #[Plane.Exact.disk windowCentre cfg.half |>.role windowRole |>.fillOpacity 0.14
    |>.width 3 |>.named "the window"
    |>.describedBy "the closed disk |w − x| ≤ r/2 about x = 1/2" |>.declRef `TDCSG.Five.InWindow]
  cfg.keyFigure .right fixed k

/-! ### Views and legends -/

/-- The world box of one view for all the figures (`Plane.commonView`). -/
def viewOf (figs : Array Plane.Figure) : Box :=
  ((commonView figs)[0]?.bind (·.view)).getD ⟨0, 0, 1, 1⟩

/-- The page padding of a panel, in pixels. -/
def panelPadding : Float := 16

/-- The height of a legend row, in pixels. -/
def legendRow : Float := 17

/-- An estimate of the width of a legend entry in pixels: swatch, gap and text. -/
def legendEntryWidth (t : String) : Float := 30 + 7.4 * t.length.toFloat

/-- A legend entry: a swatch (a dot, or a short stroke of the given width) and its text. -/
structure LegendEntry where
  /-- The text. -/
  text : String
  /-- The role of the swatch and the text; `none` for ink. -/
  role : Option String
  /-- `none` for a dot, `some w` for a stroke of width `w`. -/
  stroke : Option Float

/-- The legend as items: one row per entry from the top `top` of the box `b` down, at the unit
length `u` (pixels per world unit). -/
def legendItems (b : Box) (top u : Float) (entries : Array LegendEntry) : Array Item :=
  entries.zipIdx.flatMap fun (e, i) =>
    let y := top - (legendRow * (i.toFloat + 0.5)) / u
    let x0 := b.x0 + 2 / u
    let tone := fun (it : Item) => match e.role with
      | some r => it.role r
      | none => it
    let swatch := match e.stroke with
      | some w => tone (Plane.segment ⟨x0, y⟩ ⟨x0 + 14 / u, y⟩ |>.width w)
      | none => tone (Plane.point ⟨x0 + 7 / u, y⟩ |>.size 4)
    #[swatch.named s!"legend: {e.text}",
      tone (Plane.label e.text ⟨x0 + 14 / u, y⟩ .right (some 6))]

/-- The legend entries of the left panel. -/
def leftLegend : Array LegendEntry :=
  #[⟨"the point (y + 1)/2", none, none⟩, ⟨"left disk, center 0", some leftRole, some 2⟩,
    ⟨"right disk, center 1", some rightRole, some 2⟩]

/-- The legend entries of the right panel. -/
def rightLegend : Array LegendEntry :=
  #[⟨"P(n), the left center", some leftRole, none⟩,
    ⟨"P(n + eⱼ), the right center", some rightRole, none⟩,
    ⟨"the point, fixed at x = 1/2", none, none⟩,
    ⟨"its window, of radius r/2", some windowRole, some 3⟩]

/-- A box of width `w` with the middle of `b`. -/
def widen (b : Box) (w : Float) : Box :=
  if b.x1 - b.x0 ≥ w then b
  else
    let cx := (b.x0 + b.x1) / 2
    ⟨cx - w / 2, b.y0, cx + w / 2, b.y1⟩

/-- The keys of both panels in their views, with a legend above each: one view for all keys of a
panel, each cropped to its extent (widened to hold its legend), both at one unit length, side by
side in twice the width of one panel; stacked, each at the narrow width. -/
def FramePairConfig.keys (cfg : FramePairConfig) : Array (Plane.Figure × Plane.Figure) :=
  let ks := (List.range cfg.keyCount).toArray
  let lefts := ks.map cfg.halvedKey
  let rights := ks.map cfg.centreKey
  let lb0 := viewOf lefts
  let rb0 := viewOf rights
  let pad := panelPadding
  let legendPx := fun (es : Array LegendEntry) =>
    es.foldl (fun m e => max m (legendEntryWidth e.text)) 0
  -- the unit lengths (side by side, stacked) for the content widths `wl`, `wr`
  let units := fun (wl wr : Float) =>
    ((2 * cfg.width - 4 * pad) / (wl + wr), (cfg.narrowWidth - 2 * pad) / max wl wr)
  -- widen each box to hold its legend at the smaller unit, twice (the unit depends on the widths)
  let fit := fun (wl wr : Float) =>
    let (u, un) := units wl wr
    let m := min u un
    (max wl (legendPx leftLegend / m), max wr (legendPx rightLegend / m))
  let (w1l, w1r) := fit (lb0.x1 - lb0.x0) (rb0.x1 - rb0.x0)
  let (wl, wr) := fit w1l w1r
  let (u, un) := units wl wr
  let m := min u un
  let withLegend := fun (b : Box) (w : Float) (es : Array LegendEntry) =>
    let b := widen b w
    let band := (legendRow * es.size.toFloat + 6) / m
    (⟨b.x0, b.y0, b.x1, b.y1 + band⟩ : Box)
  let lv := withLegend lb0 wl leftLegend
  let rv := withLegend rb0 wr rightLegend
  let lItems := legendItems lv lv.y1 m leftLegend
  let rItems := legendItems rv rv.y1 m rightLegend
  let pageW := fun (w unit : Float) => w * unit + 2 * pad
  let place := fun (f : Plane.Figure) (v : Box) (legend : Array Item) (w : Float) =>
    { f with view := some v, items := legend ++ f.items, width := pageW w u,
             narrowWidth := some (pageW w un) }
  (lefts.zip rights).map fun (a, b) => (place a lv lItems wl, place b rv rItems wr)

end TDCSGFigures.Lift
