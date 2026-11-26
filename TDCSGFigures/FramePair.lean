/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import PILean.Trust.Attr
import TDCSGFigures.Lift

/-!
# The key figures of the frame pair

The two frames of chapter 4 as key figures, one per rest of a word, for an animation that turns
the moving items between consecutive keys: for any rational radius and any word in `a`, `b`,
`a⁻¹`, `b⁻¹` applied to `z = 0` (states `statesFor`), and each key `k = 0, …, |w|`,

* the left panel (`halvedKey`): the traditional view, halved: the disks of radius `r/2` about `0`
  and `1` (fixed), and the point `(y_k + 1)/2`, the actor `"point"`; or, in the full-size variant,
  the disks of radius `r` about `∓1` and the point `y_k`;
* the right panel (`centreKey`): the moving frame: the window of radius `r/2` about `x = 1/2`
  (fixed), and the rigid body of the left centre `P(n_k)` (actor `"left"`), the right centre
  `P(n_k + e_{j_k})` (actor `"right"`), the two halved disks riding on them (`"left-disk"`,
  `"right-disk"`) and the unit edge between the centres (`"edge"`).

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

**Idle letters.** The mark of a letter that does not act (`IdleMark`): a dashed ring about the
centre of its disk (left panel) and of its riding disk (right panel), by default; or a dashed
circle just outside the disk's outline (`IdleMark.outline`, `outlineGap` outside it, so that it
does not lie on the outline). It is an actor of its own, shown only in the key with the mark, so
nothing turns while it is shown.

**Trails.** Earlier points (left) and earlier centres (right) as faint dots without halo under the
strokes, shown from the state where the position is left, except while it is occupied again, for
`trailLength` letters (a short tail), or for good when `trailLength` is `none`; or, in the right
panel, as faint arcs of the paths the centres swept (`TrailStyle.arcs`), for as long.

**The centre-graph edge** (`RightStyle.bodiesGraph`) is shown while both centres lie in the window,
as one actor for each such run of states (`"graph-edge-<first state>"`, `graphRunStart`): it turns
with the body while it stays shown, and appears or vanishes only when that condition changes.

**Views** (`ViewStyle`): one view for all keys of a panel, both panels at one unit length (the
full-size left panel at half): the same width for both (`shared`), each cropped to its own extent
(`cropped`), or the two side by side in twice the panel width (`wideRight`). Each panel's height is
its own, so a narrow, stacked rendition has no empty band.

`frameSteps cfg` declares the moves between consecutive keys (`FrameStep`: a turn, or a mark that
appears or vanishes) in each panel's own coordinates, and `FramePairConfig.allArrive` checks in
exact arithmetic that each declared turn carries the actors' anchors in key `k` onto those in key
`k + 1`; the general statements are `TDCSG.Five.framePicture_genA_genB`,
`TDCSG.Five.framePicture_symm`, `TDCSG.Five.two_mul_sub_proj_genA`,
`TDCSG.Five.two_mul_sub_proj_genB`, `TDCSG.Five.halved_genA`, `TDCSG.Five.halved_genB` and
`TDCSG.Five.frameMap_genA_halved`.

Nothing here is a figure of the site; `tdcsg-figure-preview --frame-pair-keys` draws the keys, and
`TDCSGFigures.FramePairMotion` animates them.
-/

namespace TDCSGFigures.Lift

open PILean PILean.Plane PILean.Exact TDCSGFigures TDCSGFigures.Early

/-! ### The variants -/

/-- The right panel: the centres with their halved disks riding on them, the window and the point
(`bodies`); the centres and the edge only (`centres`); or `bodies` with the edge of the centre
graph shown while both centres lie in the window (`bodiesGraph`). -/
inductive RightStyle where
  /-- Centres, the halved disks riding on them, the window and the point. -/
  | bodies
  /-- Centres and the edge between them, with the window. -/
  | centres
  /-- `bodies`, and the edge of the centre graph while both centres lie in the window. -/
  | bodiesGraph
  deriving BEq, Inhabited, Repr

/-- The left panel: halved (disks of radius `r/2` about `0` and `1`, the unit length of the right
panel), or full size (disks of radius `r` about `∓1`, at half that unit length). -/
inductive LeftScale where
  /-- Halved by `w ↦ (w + 1)/2`. -/
  | halved
  /-- Full size, at half the scale. -/
  | full
  deriving BEq, Inhabited, Repr

/-- How an idle letter is marked: a dashed ring about the disk's centre, or a dashed circle just
outside the disk's outline. -/
inductive IdleMark where
  /-- A dashed circle just outside the disk's outline (`outlineGap`). -/
  | outline
  /-- A dashed ring about the centre. -/
  | ring
  deriving BEq, Inhabited, Repr

/-- The trails of the right panel: dots at earlier centres, or arcs of the paths they swept. -/
inductive TrailStyle where
  /-- Dots at earlier positions. -/
  | dots
  /-- Arcs of the paths swept. -/
  | arcs
  deriving BEq, Inhabited, Repr

/-- The views of the two panels (see the module docstring). -/
inductive ViewStyle where
  /-- Both panels of the same world width. -/
  | shared
  /-- Each panel cropped to its own extent. -/
  | cropped
  /-- Each cropped, side by side in twice the panel width. -/
  | wideRight
  deriving BEq, Inhabited, Repr

/-- A variant of the frame pair. -/
structure FramePairConfig where
  /-- The word applied to `z = 0`. -/
  word : List Letter := word
  /-- The radius `r`. -/
  radius : Rat := radius
  /-- The style of the right panel. -/
  right : RightStyle := .bodies
  /-- Whether earlier positions leave faint marks. -/
  trails : Bool := false
  /-- The trails of the right panel. -/
  trailStyle : TrailStyle := .dots
  /-- The scale of the left panel. -/
  left : LeftScale := .halved
  /-- How an idle letter is marked. -/
  idleMark : IdleMark := .ring
  /-- For how many letters a trail mark stays after its position is left; `none`: for good. -/
  trailLength : Option Nat := some 3
  /-- The views of the panels. -/
  view : ViewStyle := .shared
  /-- The page width of one panel, side by side. -/
  width : Float := figureWidth / 2
  /-- The page width of one panel, stacked. -/
  narrowWidth : Float := narrowWidth

/-- A key of the animation: the state after `state` letters, with the mark of the idle letter
before it shown (`mark`) or not. -/
structure KeyRef where
  /-- The number of letters applied. -/
  state : Nat
  /-- Whether the mark of the letter before it, which does not act, is shown. -/
  mark : Bool := false
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

/-- The number of states, `|w| + 1`. -/
def stateCount : Nat := cfg.word.length + 1

/-- Whether the right panel draws the halved disks riding on the centres and the point. -/
def riding : Bool := cfg.right != .centres

/-- The letter of step `k`, from key `k` to key `k + 1`. -/
def letterOf (k : Nat) : Letter := cfg.word.getD k .a

/-- Whether the letter before state `k` did not act (`k ≥ 1`). -/
def idleAt (k : Nat) : Bool := k ≥ 1 && !(cfg.stateAt k).acted

/-- The keys (see the module docstring): state `0`, then for each letter the state it reaches,
preceded by the same state with the letter's mark shown when the letter does not act. -/
def keyRefs : List KeyRef :=
  ⟨0, false⟩ :: (List.range cfg.word.length).flatMap fun i =>
    if cfg.idleAt (i + 1) then [⟨i + 1, true⟩, ⟨i + 1, false⟩] else [⟨i + 1, false⟩]

/-- The number of keys: one per state, and one more for each letter that does not act. -/
def keyCount : Nat := cfg.keyRefs.length

/-- Key `j`. -/
def keyRef (j : Nat) : KeyRef := cfg.keyRefs.getD j ⟨0, false⟩

/-- Whether a trail mark that appeared at state `a` is shown at state `k`: from `a` on, for
`trailLength` letters. -/
def trailShown (a k : Nat) : Bool :=
  a ≤ k && match cfg.trailLength with
    | some n => k < a + n
    | none => true

/-- Whether both centres lie in the window at key `k`. -/
def bothInWindow (k : Nat) : Bool :=
  let s := cfg.stateAt k
  inWindowFrom cfg.r2 origin s.n && inWindowFrom cfg.r2 origin s.rightLabel

/-- Whether key `k` shows the centre-graph edge (style `bodiesGraph`, both centres in the
window). -/
def showsGraphEdge (k : Nat) : Bool := cfg.right == .bodiesGraph && cfg.bothInWindow k

/-- The first state of the run of states that show the centre-graph edge and end at state `k`
(`k` itself when state `k - 1` does not show it): it names the edge's actor, so that the edge
keeps one id while it stays shown and a new run gets a new one. -/
def graphRunStart : Nat → Nat
  | 0 => 0
  | k + 1 => if cfg.showsGraphEdge k then graphRunStart k else k + 1

/-- The fixed disks of the left panel, `(title, centre, radius)`, left then right. -/
def leftDisks : List (String × ZetaFrac × Rat) :=
  match cfg.left with
  | .halved => [("the left disk, halved", ZetaFrac.ofZeta origin, cfg.half),
      ("the right disk, halved", ZetaFrac.ofZeta rightCentre, cfg.half)]
  | .full => [("the left disk", ZetaFrac.ofZeta leftCentre, cfg.radius),
      ("the right disk", ZetaFrac.ofZeta rightCentre, cfg.radius)]

/-- The point of the left panel for the point `y`: `(y + 1)/2` halved, `y` full size. -/
def leftPoint (y : Zeta5) : ZetaFrac :=
  match cfg.left with
  | .halved => halved y
  | .full => ZetaFrac.ofZeta y

/-- The name of the left panel's fixed centres: `0` and `1` halved, `−1` and `1` full size. -/
def leftNames : String × String :=
  match cfg.left with | .halved => ("0", "1") | .full => ("−1", "1")

end FramePairConfig

/-- `0` for `a` and `a⁻¹` (the left disk), `1` for `b` and `b⁻¹`. -/
def sideIndex (l : Letter) : Nat := match l with | .a | .aInv => 0 | .b | .bInv => 1

/-- The turn of the letter's point about its disk's centre, as a fraction of a full turn: `-1/5`
(clockwise) for `a` and `b`, `1/5` for their inverses. -/
def _root_.TDCSGFigures.Early.Letter.turns (l : Letter) : Rat :=
  match l with
  | .a | .b => -1 / 5
  | .aInv | .bInv => 1 / 5

/-- `ζᵏ` for a turn by `k/5` of a full turn (counter-clockwise), `none` for any other fraction. -/
def turnFactor (q : Rat) : Option Zeta5 :=
  if q.den == 5 || q.den == 1 then
    let k := (q * 5).num
    some (zeta (k % 5).toNat)
  else none

/-! ### Exact points -/

/-- The window centre `x = 1/2` as a point of `ℚ(ζ₅)`. -/
def windowCentre : ZetaFrac := ⟨Zeta5.ofInt 1, 2⟩

/-- Equality of two numbers of `ℚ(ζ₅)` given over denominators, exact. -/
def ZetaFrac.same (p q : ZetaFrac) : Bool :=
  p.num * Zeta5.ofInt q.den == q.num * Zeta5.ofInt p.den

/-- `c + τ (p - c)`: `p` turned about `c` by the factor `τ`, exact. -/
def ZetaFrac.turnAbout (c : ZetaFrac) (τ : Zeta5) (p : ZetaFrac) : ZetaFrac :=
  ⟨c.num * Zeta5.ofInt p.den + τ * (p.num * Zeta5.ofInt c.den - c.num * Zeta5.ofInt p.den),
    c.den * p.den⟩

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
  /-- A point marker at the first anchor: its size, role, whether faint (a trail mark, drawn
  without halo), whether a cross. -/
  | dot (size : Float) (role : Option String) (faint : Bool) (cross : Bool)
  /-- A circle of radius `ρ` about the first anchor: its role, stroke width, whether dashed. -/
  | outline (ρ : Rat) (role : Option String) (width : Float) (dashed : Bool)
  /-- The segment between the first two anchors: its role, stroke width, whether faint. -/
  | stroke (role : Option String) (width : Float) (faint : Bool)
  /-- The arc of radius `ρ` about the first anchor, counter-clockwise from the second anchor to
  the third, faint: a path swept. -/
  | sweep (ρ : Rat)
  deriving BEq, Inhabited, Repr

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

/-- The angle of `p` seen from `c`, in radians: for drawing an arc, never for a decision. -/
def angleOf (c p : ZetaFrac) : Float :=
  let v := PlanePoint.toPoint p - PlanePoint.toPoint c
  Float.atan2 v.y v.x

/-- The actor as an item: its geometry from its anchors only, its base title, its recorded
incidences and its id. -/
def Actor.item (a : Actor) : Item :=
  let p0 := a.anchors.getD 0 (ZetaFrac.ofZeta origin)
  let p1 := a.anchors.getD 1 p0
  let p2 := a.anchors.getD 2 p1
  let withRole := fun (r : Option String) (it : Item) => match r with
    | some r => it.role r
    | none => it
  let geom : Item := match a.kind with
    | .dot s r faint cross =>
      let it := withRole r (Plane.Exact.point p0 |>.size s)
      let it := if cross then it.marker .cross else it
      if faint then it.faint.halo false else it
    | .outline ρ r w dashed =>
      let it := withRole r (Plane.Exact.circle p0 ρ |>.width w)
      if dashed then it.dashed else it
    | .stroke r w faint =>
      let it := withRole r (Plane.Exact.segment p0 p1 |>.width w)
      if faint then it.faint else it
    | .sweep ρ =>
      let θ₀ := angleOf p0 p1
      let θ₁ := angleOf p0 p2
      let θ₁ := if θ₁ < θ₀ then θ₁ + 2 * 3.141592653589793 else θ₁
      Plane.Exact.arc p0 ρ θ₀ θ₁ |>.faint |>.width 2.5
  let named := geom.named a.base
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

/-! ### Trails -/

/-- The trail marks of a list of positions per state: each position held at state `i` and no longer
at state `i + 1` gives a mark from state `i + 1` on (once per position when `once`, else each time
it is left); the marks with their first state. -/
def trailMarks (held : Nat → List ZetaFrac) (keys : Nat) (once : Bool := true) :
    List (ZetaFrac × Nat) :=
  (List.range keys).foldl (fun acc k =>
    if k == 0 then acc
    else
      let gone := (held (k - 1)).filter fun p => !(held k).any (ZetaFrac.same p)
      gone.foldl (fun acc p =>
        if once && acc.any (ZetaFrac.same p ·.1) then acc else acc ++ [(p, k)]) acc)
    []

namespace FramePairConfig

variable (cfg : FramePairConfig)

/-- The point of the left panel at state `k`. -/
def pointAt (k : Nat) : ZetaFrac := cfg.leftPoint (cfg.stateAt k).y

/-- The centres of the right panel at state `k`. -/
def centresAt (k : Nat) : ZetaFrac × ZetaFrac :=
  let s := cfg.stateAt k
  (ZetaFrac.ofZeta s.leftCentre, ZetaFrac.ofZeta s.rightCentre)

/-- The trail marks of the left panel: earlier points. -/
def pointTrail : List (ZetaFrac × Nat) :=
  if cfg.trails then trailMarks (fun k => [cfg.pointAt k]) cfg.stateCount cfg.trailLength.isNone
  else []

/-- The trail marks of the right panel: earlier centres. -/
def centreTrail : List (ZetaFrac × Nat) :=
  if cfg.trails then
    trailMarks (fun k => [(cfg.centresAt k).1, (cfg.centresAt k).2]) cfg.stateCount
      cfg.trailLength.isNone
  else []

/-- The turn of step `k` in the right panel when its letter acts: the active centre (the centre
of the letter's disk at key `k`) and the fraction, `1/5`, or `-1/5` for an inverse. -/
def bodyTurnOf (k : Nat) : Option (ZetaFrac × Rat) :=
  let s := cfg.stateAt k
  let l := cfg.letterOf k
  if l.covers cfg.r2 s.y then some (ZetaFrac.ofZeta (proj (s.labelOf l)), -l.turns) else none

/-- The arcs swept by the centres before state `k` and still shown there (`trailShown`): for each
acting letter `i < k`, the arc of radius `1` about the active centre from the turning centre's place
at state `i` to its place at state `i + 1` (counter-clockwise, so from the later place for a
clockwise turn). -/
def sweepsBefore (k : Nat) : List (Nat × ZetaFrac × ZetaFrac × ZetaFrac) :=
  (((List.range k).filter fun i => cfg.trailShown (i + 1) k).filterMap fun i =>
    (cfg.bodyTurnOf i).map fun (c, q) =>
      let l := cfg.letterOf i
      let pick := fun (j : Nat) => if sideIndex l == 0 then (cfg.centresAt j).2
        else (cfg.centresAt j).1
      let (u, v) := if q > 0 then (pick i, pick (i + 1)) else (pick (i + 1), pick i)
      (i, c, u, v))

end FramePairConfig

/-! ### The actors of each panel -/

/-- The radius of the ring of `IdleMark.ring`, at the unit length of the right panel. -/
def ringRadius : Rat := 1 / 4

/-- How far outside the disk's outline the dashed circle of `IdleMark.outline` lies, at the unit
length of the right panel. -/
def outlineGap : Rat := 1 / 16

namespace FramePairConfig

variable (cfg : FramePairConfig)

/-- The dashed mark of the idle letter before state `k`, about the centre `c` of its disk of radius
`ρ` titled `name`: a circle `gap` outside the disk's outline, or a ring of radius `ringρ` about the
centre. -/
def idleActor (k : Nat) (c : ZetaFrac) (ρ ringρ gap : Rat) (role : String) (name : String) :
    Actor :=
  match cfg.idleMark with
  | .outline =>
    { id := s!"idle-{k}", kind := .outline (ρ + gap) (some role) 2 true,
      base := s!"a dashed circle about {name}: its letter does not act", anchors := [c] }
  | .ring =>
    { id := s!"idle-{k}", kind := .outline ringρ (some role) 2 true,
      base := s!"a ring about the center of {name}: its letter does not act", anchors := [c] }

/-- The ring radius and the outline gap of the left panel's idle mark: those of the right panel,
twice as large for a full-size left panel. -/
def leftMarkSizes : Rat × Rat :=
  match cfg.left with
  | .halved => (ringRadius, outlineGap)
  | .full => (2 * ringRadius, 2 * outlineGap)

/-- The circles of the idle mark of key `r` in the left panel, for the records of the points. -/
def leftIdleCircle (r : KeyRef) : List (String × ZetaFrac × Rat) :=
  let k := r.state
  if r.mark then
    let (name, c, ρ) := cfg.leftDisks.getD (sideIndex (cfg.letterOf (k - 1)))
      ("", ZetaFrac.ofZeta origin, 0)
    let (ringρ, gap) := cfg.leftMarkSizes
    let a := cfg.idleActor k c ρ ringρ gap "" name
    match a.kind with
    | .outline r .. => [(a.base, c, r)]
    | _ => []
  else []

/-- The actors of the left panel at key `r`, in drawing order: trail marks, the fixed centres,
the idle mark, the point. -/
def leftActors (r : KeyRef) : List Actor :=
  let k := r.state
  let disks := cfg.leftDisks
  let idle := cfg.leftIdleCircle r
  let circles := disks ++ idle
  let (n0, n1) := cfg.leftNames
  let trail := cfg.pointTrail.zipIdx.filterMap fun ((q, a), i) =>
    if cfg.trailShown a k && !(ZetaFrac.same q (cfg.pointAt k)) then
      some { id := s!"trail-point-{i}", kind := .dot 3 none true false,
             base := "an earlier point", anchors := [q], records := recordsOf q circles [] }
    else none
  let centres := (disks.zipIdx.map fun ((_, c, _), i) =>
    let (role, name) := if i == 0 then (leftRole, s!"the left center {n0}")
      else (rightRole, s!"the right center {n1}")
    ({ id := s!"center-{i}", kind := .dot 4 (some role) false false, base := name,
       anchors := [c], records := recordsOf c circles [] } : Actor))
  let idleA : List Actor :=
    if r.mark then
      let i := sideIndex (cfg.letterOf (k - 1))
      let (name, c, ρ) := disks.getD i ("", ZetaFrac.ofZeta origin, 0)
      let (ringρ, gap) := cfg.leftMarkSizes
      [cfg.idleActor k c ρ ringρ gap (if i == 0 then leftRole else rightRole) name]
    else []
  let p := cfg.pointAt k
  let pt := match cfg.left with | .halved => "(y + 1)/2" | .full => "y"
  trail ++ centres ++ idleA ++
    [{ id := "point", kind := .dot 5 none false false, base := s!"the point {pt}",
       anchors := [p], records := recordsOf p circles [] }]

/-- The title of the edge between the centres. -/
def edgeName : String := "the unit edge from the left to the right center"

/-- The title of a centre-graph edge. -/
def graphEdgeName : String := "an edge of the center graph: both centers lie in the window"

/-- The actors of the right panel at key `r`, in drawing order: trail marks, the riding disks, the
idle mark, the edge and the centre-graph edge, the point at `x`, the centres. -/
def rightActors (r : KeyRef) : List Actor :=
  let k := r.state
  let (pl, pr) := cfg.centresAt k
  let x := windowCentre
  let ρ := cfg.half
  let window : List (String × ZetaFrac × Rat) := [("the window", x, ρ)]
  let riding : List (String × ZetaFrac × Rat) :=
    if cfg.riding then [("the left disk, riding", pl, ρ), ("the right disk, riding", pr, ρ)]
    else []
  let idle : List Actor :=
    if r.mark then
      let i := sideIndex (cfg.letterOf (k - 1))
      let (c, role, name) := if i == 0 then (pl, leftRole, "the left disk, riding")
        else (pr, rightRole, "the right disk, riding")
      [{ cfg with idleMark := if cfg.riding then cfg.idleMark else .ring }.idleActor k c ρ
        ringRadius outlineGap role name]
    else []
  let idleCircles : List (String × ZetaFrac × Rat) := idle.filterMap fun a =>
    match a.kind with
    | .outline r .. => some (a.base, a.anchors.getD 0 x, r)
    | _ => none
  let circles := window ++ riding ++ idleCircles
  let segments : List (String × ZetaFrac × ZetaFrac) :=
    [(edgeName, pl, pr)] ++ (if cfg.showsGraphEdge k then [(graphEdgeName, pl, pr)] else [])
  let trail : List Actor :=
    if !cfg.trails then []
    else match cfg.trailStyle with
      | .dots => cfg.centreTrail.zipIdx.filterMap fun ((q, a), i) =>
        if cfg.trailShown a k && !(ZetaFrac.same q pl) && !(ZetaFrac.same q pr) then
          some { id := s!"trail-center-{i}", kind := .dot 3 none true false,
                 base := "an earlier center", anchors := [q], records := recordsOf q circles [] }
        else none
      | .arcs => (cfg.sweepsBefore k).map fun (i, c, u, v) =>
        { id := s!"trail-sweep-{i}", kind := .sweep 1,
          base := "the path a center swept", anchors := [c, u, v] }
  let disks : List Actor :=
    if cfg.riding then [
      { id := "left-disk", kind := .outline ρ (some leftRole) 1.5 false,
        base := "the left disk, riding", anchors := [pl] },
      { id := "right-disk", kind := .outline ρ (some rightRole) 1.5 false,
        base := "the right disk, riding", anchors := [pr] }]
    else []
  let edges : List Actor :=
    [{ id := "edge", kind := .stroke none 1.5 false, base := edgeName, anchors := [pl, pr] }] ++
    (if cfg.showsGraphEdge k then
      [{ id := s!"graph-edge-{cfg.graphRunStart k}", kind := .stroke (some windowRole) 4 false,
         base := graphEdgeName, anchors := [pl, pr], decl := some `TDCSG.Five.centerGraph }]
     else [])
  let xActor : Actor :=
    if cfg.riding then
      { id := "x", kind := .dot 5 none false false, base := "the point, fixed at x = 1/2",
        anchors := [x], records := recordsOf x riding segments }
    else
      { id := "x", kind := .dot 5 (some windowRole) false true,
        base := "the window center x = 1/2", anchors := [x], records := recordsOf x [] segments }
  let others := fun (q : ZetaFrac) => circles.filter fun (_, c, _) => !(ZetaFrac.same c q)
  let centres : List Actor := [
    { id := "left", kind := .dot 5 (some leftRole) false false, base := "the left center P(n)",
      anchors := [pl], records := recordsOf pl (others pl) [],
      decl := some `TDCSG.Five.Label.proj },
    { id := "right", kind := .dot 5 (some rightRole) false false,
      base := "the right center P(n + eⱼ)", anchors := [pr],
      records := recordsOf pr (others pr) [] }]
  trail ++ disks ++ idle ++ edges ++ [xActor] ++ centres

/-- The actors of a panel at key `j` (`leftActors`, `rightActors` of `keyRef j`): the one list
that the key figures draw and the arrival check reads. -/
def actorsAt : Panel → Nat → List Actor
  | .left, j => cfg.leftActors (cfg.keyRef j)
  | .right, j => cfg.rightActors (cfg.keyRef j)

end FramePairConfig

/-! ### The moves -/

/-- A turn about an exact centre by an exact fraction of a full turn (counter-clockwise). -/
structure ExactTurn where
  /-- The centre, in the panel's own coordinates. -/
  centre : ZetaFrac
  /-- The fraction of a full turn. -/
  turns : Rat

/-- What a step between two keys does: the turn of a letter that acts, or the mark of a letter
that does not act appearing or vanishing. -/
inductive StepPhase where
  /-- A letter acts: both panels turn. -/
  | turn
  /-- A letter does not act: its mark appears. -/
  | markAppears
  /-- The mark of a letter that does not act vanishes. -/
  | markVanishes
  deriving DecidableEq, Inhabited, Repr

/-- What happens between key `j` and key `j + 1`, in each panel's own coordinates: the letter, what
the step does, whether the letter acts, the turn of the left panel (of the actor `"point"` about the
centre of the letter's disk as drawn there: `0`, `1` halved, `−1`, `1` full size; by `-1/5` for `a`
and `b`, `1/5` for their inverses) and the turn of the right panel (about the centre of the letter's
disk before the turn, by `1/5`, or `-1/5` for an inverse), the actors each turns, and the actors
that appear and vanish in each panel. -/
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
edge, the other centre with its riding disk and the centre-graph edge when both keys show it. -/
def frameStepWith (actors : Panel → Nat → List Actor) (j : Nat) : FrameStep :=
  let r := cfg.keyRef j
  let r' := cfg.keyRef (j + 1)
  let i := r'.state - 1
  let s := cfg.stateAt i
  let l := cfg.letterOf i
  let phase : StepPhase :=
    if r.state == r'.state then .markVanishes else if r'.mark then .markAppears else .turn
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
      (("edge" :: other) ++ (ids .right j).filter (·.startsWith "graph-edge-")).filter fun id =>
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

/-- Whether every step of the variant arrives, with the actors given by `actors`. -/
def allArriveWith (actors : Panel → Nat → List Actor) : Bool :=
  (List.range (cfg.keyCount - 1)).all (cfg.arrivesWith actors)

/-- Whether every declared move of the variant carries key `k` onto key `k + 1` exactly, for the
actors the key figures draw (`actorsAt`). The general statements behind it:
`TDCSG.Five.halved_genA`, `halved_genB`, `halved_permA_symm`, `halved_permB_symm` (left panel),
`TDCSG.Five.two_mul_sub_proj_genA`, `two_mul_sub_proj_genB`, `two_mul_sub_proj_permA_symm`,
`two_mul_sub_proj_permB_symm`, `frameMap_genA_halved` and `framePicture_genA_genB` (right
panel). -/
def allArrive : Bool := cfg.allArriveWith cfg.actorsAt

/-- Whether every actor of every key, drawn (`Actor.item`), gives back its base title
(`baseTitle`). -/
def baseTitlesRecoverable : Bool :=
  (List.range cfg.keyCount).all fun k =>
    [Panel.left, .right].all fun p =>
      (cfg.actorsAt p k).all fun a => baseTitle a.item == some a.base

/-! ### Captions -/

/-- A non-breaking space. -/
def nbsp : String := " "

/-- The label `n` and the index `j` of a state, as a parenthesis that does not break inside. -/
def whereText (s : State) : String :=
  let n := ("," ++ nbsp).intercalate (s.n.toList.map fun k =>
    if k < 0 then s!"−{-k}" else toString k)
  s!"(n{nbsp}={nbsp}({n}), j{nbsp}={nbsp}{s.j})"

/-- The caption of state `k`: the start, explaining `n` and `j`, or what the letter before it did,
with the size and direction of the turns, whether the centre-graph edge appears or vanishes, and
`n` and `j` in a trailing parenthesis; plain words, from the states. -/
def stateCaption (k : Nat) : String :=
  let s := cfg.stateAt k
  let (n0, n1) := cfg.leftNames
  let total := cfg.word.length
  if k == 0 then
    let leftText := match cfg.left with
      | .halved => s!"the disks halved, with centers {n0} and {n1}, and the point (y + 1)/2"
      | .full => s!"the disks of radius r about {n0} and {n1}, and the point y"
    s!"Start: z = 0, so x = 1/2. Left: {leftText}. Right: the window about x, and the left and " ++
      "right centers P(n) and P(n + eⱼ); n is the integer label of the left center, j the " ++
      s!"index of the direction from the left to the right center {whereText s}."
  else
    let l := cfg.letterOf (k - 1)
    let (own, other, ownName) := match l with
      | .a | .aInv => ("left", "right", n0)
      | .b | .bInv => ("right", "left", n1)
    let (pointWay, centreWay) := match l with
      | .a | .b => ("clockwise", "counter-clockwise")
      | .aInv | .bInv => ("counter-clockwise", "clockwise")
    let graph :=
      if cfg.right != .bodiesGraph then ""
      else if cfg.showsGraphEdge k && !cfg.showsGraphEdge (k - 1) then
        " The center-graph edge appears: both centers lie in the window."
      else if !cfg.showsGraphEdge k && cfg.showsGraphEdge (k - 1) then
        " The center-graph edge vanishes."
      else ""
    let mark := match cfg.idleMark with
      | .outline => "marked by a dashed circle" | .ring => "ringed"
    let body := if s.acted then
      s!"{l.text} acts: the point turns a fifth of a turn {pointWay} about the {own} center " ++
        s!"{ownName}; in the moving frame the {other} center turns a fifth of a turn " ++
        s!"{centreWay} about the {own} center."
    else
      s!"{l.text} does not act: the point is outside the {own} disk ({mark}), and the {own} " ++
        "center is outside the window; nothing moves."
    s!"Step {k} of {total}: {body}{graph} {whereText s}"

/-- The caption of key `j`: that of its state (`stateCaption`), so the key that shows an idle
letter's mark and the key after it say the same; "Step k of n" counts letters. -/
def keyCaption (j : Nat) : String := cfg.stateCaption (cfg.keyRef j).state

end FramePairConfig

/-! ### The key figures -/

/-- A key of a panel: the fixed items, then the actors drawn from `actorsAt`. -/
def FramePairConfig.keyFigure (cfg : FramePairConfig) (p : Panel) (fixed : Array Item)
    (k : Nat) : Plane.Figure :=
  let actors := (cfg.actorsAt p k).toArray.map Actor.item
  -- trail marks first, under the fixed strokes
  let (trail, rest) := actors.partition fun it => match it with
    | .shape _ _ i | .group _ i => i.id.startsWith "trail-"
  { width := cfg.width
    narrowWidth := some cfg.narrowWidth
    padding := 16
    style := partTwoStyle
    checks := .fail
    items := trail ++ fixed ++ rest
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
def FramePairConfig.leftLegend (cfg : FramePairConfig) : Array LegendEntry :=
  let (n0, n1) := cfg.leftNames
  let pt := match cfg.left with | .halved => "the point (y + 1)/2" | .full => "the point y"
  #[⟨pt, none, none⟩, ⟨s!"left disk, center {n0}", some leftRole, some 2⟩,
    ⟨s!"right disk, center {n1}", some rightRole, some 2⟩]

/-- The legend entries of the right panel. -/
def FramePairConfig.rightLegend (cfg : FramePairConfig) : Array LegendEntry :=
  #[⟨"P(n), the left center", some leftRole, none⟩,
    ⟨"P(n + eⱼ), the right center", some rightRole, none⟩,
    if cfg.riding then ⟨"the point, fixed at x = 1/2", none, none⟩
    else ⟨"x = 1/2", some windowRole, none⟩,
    ⟨"its window, of radius r/2", some windowRole, some 3⟩] ++
  (if cfg.right == .bodiesGraph then #[⟨"an edge of the center graph", some windowRole, some 4⟩]
   else #[])

/-- A box of width `w` with the middle of `b`. -/
def widen (b : Box) (w : Float) : Box :=
  if b.x1 - b.x0 ≥ w then b
  else
    let cx := (b.x0 + b.x1) / 2
    ⟨cx - w / 2, b.y0, cx + w / 2, b.y1⟩

/-- The keys of both panels in their views (`ViewStyle`), with a legend above each: one view for
all keys of a panel, both panels at one unit length (a full-size left panel at half, showing the
image of its halved view under `w ↦ 2w - 1`). -/
def FramePairConfig.keys (cfg : FramePairConfig) : Array (Plane.Figure × Plane.Figure) :=
  let ks := (List.range cfg.keyCount).toArray
  let lefts := ks.map cfg.halvedKey
  let rights := ks.map cfg.centreKey
  let lb0 := viewOf (ks.map { cfg with left := .halved }.halvedKey)
  let rb0 := viewOf rights
  let pad := panelPadding
  let lLeg := cfg.leftLegend
  let rLeg := cfg.rightLegend
  let legendPx := fun (es : Array LegendEntry) =>
    es.foldl (fun m e => max m (legendEntryWidth e.text)) 0
  -- the unit lengths (wide, narrow) for the content widths `wl`, `wr`
  let units := fun (wl wr : Float) => match cfg.view with
    | .shared | .cropped =>
      ((cfg.width - 2 * pad) / max wl wr, (cfg.narrowWidth - 2 * pad) / max wl wr)
    | .wideRight =>
      ((2 * cfg.width - 4 * pad) / (wl + wr), (cfg.narrowWidth - 2 * pad) / max wl wr)
  -- widen each box to hold its legend at the smaller unit, twice (the unit depends on the widths)
  let fit := fun (wl wr : Float) =>
    let (u, un) := units wl wr
    let m := min u un
    (max wl (legendPx lLeg / m), max wr (legendPx rLeg / m))
  let w0l := lb0.x1 - lb0.x0
  let w0r := rb0.x1 - rb0.x0
  let (w1l, w1r) := fit w0l w0r
  let (wl, wr) := fit w1l w1r
  let (wl, wr) := if cfg.view == .shared then (max wl wr, max wl wr) else (wl, wr)
  let (u, un) := units wl wr
  let m := min u un
  let withLegend := fun (b : Box) (w : Float) (es : Array LegendEntry) =>
    let b := widen b w
    let band := (legendRow * es.size.toFloat + 6) / m
    (⟨b.x0, b.y0, b.x1, b.y1 + band⟩ : Box)
  let lvH := withLegend lb0 wl lLeg
  let rv := withLegend rb0 wr rLeg
  let lv : Box := if cfg.left == .halved then lvH
    else ⟨2 * lvH.x0 - 1, 2 * lvH.y0, 2 * lvH.x1 - 1, 2 * lvH.y1⟩
  let lu := if cfg.left == .halved then m else m / 2
  let lItems := legendItems lv lv.y1 lu lLeg
  let rItems := legendItems rv rv.y1 m rLeg
  let pageW := fun (w unit : Float) => w * unit + 2 * pad
  let lw := pageW wl u
  let rw := pageW wr u
  let lnw := pageW wl un
  let rnw := pageW wr un
  (lefts.zip rights).map fun (a, b) =>
    ({ a with view := some lv, items := lItems ++ a.items, width := lw, narrowWidth := some lnw },
      { b with view := some rv, items := rItems ++ b.items, width := rw, narrowWidth := some rnw })

end TDCSGFigures.Lift
