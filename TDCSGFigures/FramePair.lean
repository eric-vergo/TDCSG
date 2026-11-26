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

* `halvedKey cfg k`: the traditional view, halved: the disks of radius `r/2` about `0` and `1`
  and their centres (fixed), and the point `(y_k + 1)/2`, the actor `"point"`; or, in the
  full-size variant, the disks of radius `r` about `∓1` and the point `y_k`;
* `centreKey cfg k`: the moving frame: the window of radius `r/2` about `x = 1/2` (fixed), and the
  rigid body of the left centre `P(n_k)` (actor `"left"`), the right centre `P(n_k + e_{j_k})`
  (actor `"right"`), the two halved disks riding on them (`"left-disk"`, `"right-disk"`) and the
  unit edge between the centres (`"edge"`).

Every moving item carries the same id in every key and the same look and text: what depends on
the step is said in the caption (`keyCaption`). The names of the point and of the centres are in a
legend above each panel (`FramePairConfig.keys`), since a label riding a centre would cross a
circle in some key; the fixed centres `0` and `1` of the left panel are labelled beside them when
a side clear in every key exists (`centreLabelChoices`), else in the legend. An idle letter is
shown by a dashed ring that appears in the step of that letter and vanishes in the next, about
the centre of the letter's disk, which lies outside the window (both panels). Trails are faint
marks of earlier positions, shown from the key where the position is left on, except while it is
occupied again. Recorded incidences (`Item.incident`) are decided exactly on every key; they are
part of an item's look and title, so a point whose incidences change between keys is not the
same item in both keys.

`frameSteps cfg` declares the moves between consecutive keys (`FrameStep`) as data, and
`FramePairConfig.arrives` checks in exact arithmetic that each declared turn carries the actors'
exact positions in key `k` onto those in key `k + 1`; the general statements are
`TDCSG.Five.framePicture_genA_genB`, `TDCSG.Five.framePicture_symm`,
`TDCSG.Five.two_mul_sub_proj_genA`, `TDCSG.Five.two_mul_sub_proj_genB`, `TDCSG.Five.halved_genA`,
`TDCSG.Five.halved_genB` and `TDCSG.Five.frameMap_genA_halved`.

Nothing here is a figure of the site; `tdcsg-figure-preview --frame-pair-keys` draws the keys.
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
panel), or full size (disks of radius `r` about `∓1`, drawn at half that unit length so that the
panel keeps its width). -/
inductive LeftScale where
  /-- Halved by `w ↦ (w + 1)/2`. -/
  | halved
  /-- Full size, at half the scale. -/
  | full
  deriving BEq, Inhabited, Repr

/-- A variant of the frame pair: the word, the rational radius, the right panel's style, trails,
the left panel's scale, and the page widths of one panel (wide, and narrow, where the two panels
are stacked). -/
structure FramePairConfig where
  /-- The word applied to `z = 0`. -/
  word : List Letter := word
  /-- The radius `r`. -/
  radius : Rat := radius
  /-- The style of the right panel. -/
  right : RightStyle := .bodies
  /-- Whether earlier positions leave faint marks. -/
  trails : Bool := false
  /-- The scale of the left panel. -/
  left : LeftScale := .halved
  /-- The page width of one panel, side by side. -/
  width : Float := figureWidth / 2
  /-- The page width of one panel, stacked. -/
  narrowWidth : Float := narrowWidth
  /-- The sides of the labels of the two fixed centres of the left panel, or `none` to name them
  in the legend; `keys` chooses them for the word among `centreLabelChoices`. -/
  centreLabels : Option (Plane.Placement × Plane.Placement) := some (.left, .right)

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

/-- The number of keys, `|w| + 1`. -/
def keyCount : Nat := cfg.word.length + 1

/-- Whether the right panel draws the halved disks riding on the centres and the point. -/
def riding : Bool := cfg.right != .centres

end FramePairConfig

/-! ### Exact positions -/

/-- The window centre `x = 1/2` as a point of `ℚ(ζ₅)`. -/
def windowCentre : ZetaFrac := ⟨Zeta5.ofInt 1, 2⟩

/-- The actors of the rigid body of the right panel at a state, each with the exact points that fix
its drawing: the centres, the centres of the riding disks, the ends of the edge. -/
def bodyAnchors (riding : Bool) (s : State) : List (String × List Zeta5) :=
  let pl := s.leftCentre
  let pr := s.rightCentre
  (if riding then [("left-disk", [pl]), ("right-disk", [pr])] else []) ++
    [("edge", [pl, pr]), ("left", [pl]), ("right", [pr])]

/-- The actors of the body that turn when the letter acts: all but the centre of the letter's disk
and the disk riding on it. -/
def turningActors (riding : Bool) (l : Letter) : List String :=
  let rest := match l with
    | .a | .aInv => ["right", "right-disk"]
    | .b | .bInv => ["left", "left-disk"]
  ("edge" :: rest).filter fun id => riding || !(id.endsWith "-disk")

/-- `ζᵏ` for a turn by `k/5` of a full turn (counter-clockwise), `none` for any other fraction. -/
def turnFactor (q : Rat) : Option Zeta5 :=
  if q.den == 5 || q.den == 1 then
    let k := (q * 5).num
    some (zeta (k % 5).toNat)
  else none

/-! ### The moves -/

/-- A turn about an exact centre by an exact fraction of a full turn (counter-clockwise). -/
structure ExactTurn (α : Type) where
  /-- The centre. -/
  centre : α
  /-- The fraction of a full turn. -/
  turns : Rat

/-- What happens between key `k` and key `k + 1`: the letter, whether it acts, the turn of the
actor `"point"` of the left panel (about the halved centre of the letter's disk, by `-1/5` for
`a` and `b` and `1/5` for their inverses), the turn of the body of the right panel (about the
centre of the letter's disk at key `k`, by `1/5`, or `-1/5` for an inverse) and the actors it
turns, and the actors that appear and vanish in each panel. -/
structure FrameStep where
  /-- The letter. -/
  letter : Letter
  /-- Whether it acts. -/
  acts : Bool
  /-- The turn of the point in the halved left panel, when the letter acts. -/
  pointTurn : Option (ExactTurn ZetaFrac)
  /-- The turn of the body in the right panel, when the letter acts. -/
  bodyTurn : Option (ExactTurn Zeta5)
  /-- The actors of the body that turn. -/
  turning : List String
  /-- The actors of the left panel that appear in this step. -/
  appearLeft : List String
  /-- The actors of the left panel that vanish in this step. -/
  vanishLeft : List String
  /-- The actors of the right panel that appear in this step. -/
  appearRight : List String
  /-- The actors of the right panel that vanish in this step. -/
  vanishRight : List String

/-- The halved centre `0` or `1` of the letter's disk. -/
def halvedCentreOf (l : Letter) : ZetaFrac :=
  match l with
  | .a | .aInv => ZetaFrac.ofZeta origin
  | .b | .bInv => ZetaFrac.ofZeta rightCentre

/-- The turn of the letter in the halved frame, as a fraction of a full turn: `-1/5` (clockwise)
for `a` and `b`, `1/5` for their inverses. -/
def _root_.TDCSGFigures.Early.Letter.turns (l : Letter) : Rat :=
  match l with
  | .a | .b => -1 / 5
  | .aInv | .bInv => 1 / 5

/-! ### Trails, idle markers and centre-graph edges -/

/-- The trail marks of a list of positions per key: each position held at key `i` and no longer at
key `i + 1` gives a mark appearing at key `i + 1`, once; the marks with their first key. -/
def trailMarks {α : Type} [BEq α] (held : Nat → List α) (keys : Nat) : List (α × Nat) :=
  (List.range keys).foldl (fun acc k =>
    if k == 0 then acc
    else
      let gone := (held (k - 1)).filter fun p => !(held k).contains p
      gone.foldl (fun acc p => if acc.any (·.1 == p) then acc else acc ++ [(p, k)]) acc) []

/-- Whether the letter before key `k` did not act (`k ≥ 1`). -/
def FramePairConfig.idleAt (cfg : FramePairConfig) (k : Nat) : Bool :=
  k ≥ 1 && !(cfg.stateAt k).acted

/-- The letter before key `k`. -/
def FramePairConfig.letterAt (cfg : FramePairConfig) (k : Nat) : Letter :=
  cfg.word.getD (k - 1) .a

/-- Whether both centres lie in the window at key `k`. -/
def FramePairConfig.bothInWindow (cfg : FramePairConfig) (k : Nat) : Bool :=
  let s := cfg.stateAt k
  inWindowFrom cfg.r2 origin s.n && inWindowFrom cfg.r2 origin s.rightLabel

/-- Whether key `k` shows the centre-graph edge (style `bodiesGraph`, both centres in the
window). -/
def FramePairConfig.showsGraphEdge (cfg : FramePairConfig) (k : Nat) : Bool :=
  cfg.right == .bodiesGraph && cfg.bothInWindow k

/-- The trail marks of the left panel: earlier points, by the point `y`. -/
def FramePairConfig.pointTrail (cfg : FramePairConfig) : List (Zeta5 × Nat) :=
  if cfg.trails then trailMarks (fun k => [(cfg.stateAt k).y]) cfg.keyCount else []

/-- The trail marks of the right panel: earlier centres. -/
def FramePairConfig.centreTrail (cfg : FramePairConfig) : List (Zeta5 × Nat) :=
  if cfg.trails then
    trailMarks (fun k => [(cfg.stateAt k).leftCentre, (cfg.stateAt k).rightCentre]) cfg.keyCount
  else []

/-- Whether the trail mark of the point `y`, first left at key `a`, is shown at key `k`: from key
`a` on, except while the point is there again (the mark would sit under it). -/
def FramePairConfig.pointMarkShown (cfg : FramePairConfig) (y : Zeta5) (a k : Nat) : Bool :=
  a ≤ k && !((cfg.stateAt k).y == y)

/-- Whether the trail mark of the centre position `p`, first left at key `a`, is shown at key `k`:
from key `a` on, except while a centre is there again. -/
def FramePairConfig.centreMarkShown (cfg : FramePairConfig) (p : Zeta5) (a k : Nat) : Bool :=
  let s := cfg.stateAt k
  a ≤ k && !(s.leftCentre == p) && !(s.rightCentre == p)

/-- The ids of the actors of the left panel at key `k` that are not there at key `k - 1` and the
other way round, apart from the point and the fixed items. -/
def FramePairConfig.leftExtras (cfg : FramePairConfig) (k : Nat) : List String :=
  (cfg.pointTrail.zipIdx.filterMap fun ((y, a), i) =>
      if cfg.pointMarkShown y a k then some s!"trail-point-{i}" else none) ++
    (if cfg.idleAt k then [s!"idle-disk-{k}"] else [])

/-- The ids of the extra actors of the right panel at key `k`: trail marks, the idle marker and
the centre-graph edge. -/
def FramePairConfig.rightExtras (cfg : FramePairConfig) (k : Nat) : List String :=
  (cfg.centreTrail.zipIdx.filterMap fun ((p, a), i) =>
      if cfg.centreMarkShown p a k then some s!"trail-center-{i}" else none) ++
    (if cfg.idleAt k then [s!"idle-center-{k}"] else []) ++
    (if cfg.showsGraphEdge k then [s!"graph-edge-{k}"] else [])

/-- The moves of step `k`, from key `k` to key `k + 1`. -/
def FramePairConfig.frameStep (cfg : FramePairConfig) (k : Nat) : FrameStep :=
  let s := cfg.stateAt k
  let l := cfg.word.getD k .a
  let acts := l.covers cfg.r2 s.y
  let diff := fun (xs ys : List String) => ys.filter fun id => !xs.contains id
  { letter := l, acts
    pointTurn := if acts then some ⟨halvedCentreOf l, l.turns⟩ else none
    bodyTurn := if acts then some ⟨proj (s.labelOf l), -l.turns⟩ else none
    turning := if acts then turningActors cfg.riding l else []
    appearLeft := diff (cfg.leftExtras k) (cfg.leftExtras (k + 1))
    vanishLeft := diff (cfg.leftExtras (k + 1)) (cfg.leftExtras k)
    appearRight := diff (cfg.rightExtras k) (cfg.rightExtras (k + 1))
    vanishRight := diff (cfg.rightExtras (k + 1)) (cfg.rightExtras k) }

/-- The steps of the word, one fewer than the keys. -/
def FramePairConfig.frameSteps (cfg : FramePairConfig) : List FrameStep :=
  (List.range cfg.word.length).map cfg.frameStep

/-! ### Exact arrival -/

/-- Whether the declared moves of step `k` carry the actors' exact positions in key `k` onto those
in key `k + 1`, in `ℤ[ζ₅]`:
* left panel: when the letter acts, the halved point turned about the declared centre by the
  declared fraction (`turnFactor`) is the next halved point (doubled: `(y' + 1) - 2c =
  τ ((y + 1) - 2c)`); otherwise the point stays;
* right panel: every actor of the body that the step turns, turned about the declared centre by
  the declared fraction, lands on its next position; every other actor of the body stays.
The general statements behind it: `TDCSG.Five.halved_genA`, `halved_genB`, `halved_permA_symm`,
`halved_permB_symm` (left), `TDCSG.Five.two_mul_sub_proj_genA`, `two_mul_sub_proj_genB`,
`two_mul_sub_proj_permA_symm`, `two_mul_sub_proj_permB_symm`, `frameMap_genA_halved` and
`framePicture_genA_genB` (right). -/
def FramePairConfig.arrives (cfg : FramePairConfig) (k : Nat) : Bool :=
  let st := cfg.frameStep k
  let s := cfg.stateAt k
  let t := cfg.stateAt (k + 1)
  let left : Bool := match st.pointTurn with
    | none => !st.acts && t.y == s.y
    | some tn =>
      match turnFactor tn.turns with
      | none => false
      | some τ =>
        -- `2c` for the halved centre `c`: the turn of `(y + 1)/2` about `c`, doubled
        let c2 := tn.centre.num * Zeta5.ofInt (2 / tn.centre.den : Nat)
        tn.centre.den ∣ 2 &&
          t.y + Zeta5.ofInt 1 - c2 == τ * (s.y + Zeta5.ofInt 1 - c2)
  let before := bodyAnchors cfg.riding s
  let after := bodyAnchors cfg.riding t
  let right : Bool := match st.bodyTurn with
    | none => !st.acts && before == after
    | some tn =>
      match turnFactor tn.turns with
      | none => false
      | some σ =>
        (before.zip after).all fun ((id, ps), (id', qs)) =>
          id == id' && ps.length == qs.length &&
            if st.turning.contains id then
              (ps.zip qs).all fun (p, q) => tn.centre + σ * (p - tn.centre) == q
            else ps == qs
  left && right

/-- Whether every step of the variant arrives (`FramePairConfig.arrives`). -/
def FramePairConfig.allArrive (cfg : FramePairConfig) : Bool :=
  (List.range cfg.word.length).all cfg.arrives

/-! ### Captions -/

/-- The label of a state's left centre as text. -/
def labelString (n : Label) : String :=
  "(" ++ ", ".intercalate (n.toList.map fun k => if k < 0 then s!"−{-k}" else toString k) ++ ")"

/-- The caption of key `k`: the start, or what the letter before it did, with the label `n` and the
direction index `j` reached; plain words, from the states. -/
def FramePairConfig.keyCaption (cfg : FramePairConfig) (k : Nat) : String :=
  let s := cfg.stateAt k
  let where_ := s!"n = {labelString s.n}, j = {s.j}"
  let total := cfg.word.length
  if k == 0 then
    s!"Start: z = 0, so x = 1/2; the left and right centers are 0 and 1 ({where_})."
  else
    let l := cfg.letterAt k
    let (own, other) := match l with
      | .a | .aInv => ("left", "right")
      | .b | .bInv => ("right", "left")
    let back := match l with | .a | .b => "" | .aInv | .bInv => " back"
    let head := s!"Step {k} of {total}: "
    if s.acted then
      head ++ s!"{l.text} acts: the point turns{back} about the {own} center; in the moving " ++
        s!"frame the {other} center turns{back} about the {own} center ({where_})."
    else
      head ++ s!"{l.text} does not act: the point is outside the {own} disk, and the {own} " ++
        s!"center is outside the window ({where_})."

/-! ### The key figures -/

/-- Whether the point `x` of `ℚ(ζ₅)` lies on the segment from `a` to `b`, where `|b - a| = 1`:
`(x - a) (b - a)‾` is real and between `0` and `1`, decided exactly. -/
def onSegment (x : ZetaFrac) (a b : Zeta5) : Bool :=
  let w := (x.num - Zeta5.ofInt x.den * a) * (b - a).conj
  w == w.conj && QSqrt.le (rat 0) w.realPart && QSqrt.le w.realPart (rat x.den)

/-- Where a point stands relative to the closed disk of radius `ρ` about `c`, decided exactly. -/
def sideTo (p c : ZetaFrac) (ρ : Rat) : Plane.Incidence :=
  (sideOfSq (p - c).normSq (rat (ρ * ρ))).incidence

/-- A point item with where it stands relative to each named disk `(title, centre, radius)`,
decided exactly. -/
def pointAmong (p : ZetaFrac) (disks : List (String × ZetaFrac × Rat)) (it : Item) : Item :=
  disks.foldl (fun it (name, c, ρ) => it.incident (sideTo p c ρ) name) it

/-- The radius of the ring that marks the centre of an idle letter's disk, at the unit length of
the right panel (twice that in a full-size left panel). -/
def ringRadius : Rat := 1 / 8

/-- A placeholder disk, for a missing entry. -/
def noDisk : String × ZetaFrac × Rat := ("", ZetaFrac.ofZeta origin, 0)

/-- The fixed disks of the left panel, with their titles, centres and radii. -/
def FramePairConfig.leftDisks (cfg : FramePairConfig) : List (String × ZetaFrac × Rat) :=
  match cfg.left with
  | .halved => [("the left disk, halved", ZetaFrac.ofZeta origin, cfg.half),
      ("the right disk, halved", ZetaFrac.ofZeta rightCentre, cfg.half)]
  | .full => [("the left disk", ZetaFrac.ofZeta leftCentre, cfg.radius),
      ("the right disk", ZetaFrac.ofZeta rightCentre, cfg.radius)]

/-- The point of the left panel for the point `y`: `(y + 1)/2` halved, `y` full size. -/
def FramePairConfig.leftPoint (cfg : FramePairConfig) (y : Zeta5) : ZetaFrac :=
  match cfg.left with
  | .halved => halved y
  | .full => ZetaFrac.ofZeta y

/-- Key `k` of the left panel (see the module docstring). -/
def FramePairConfig.halvedKey (cfg : FramePairConfig) (k : Nat) : Plane.Figure :=
  let disks := cfg.leftDisks
  let s := cfg.stateAt k
  let p := cfg.leftPoint s.y
  let (cl, cr, tl, tr, pt) := match cfg.left with
    | .halved => ("0", "1", "the left center −1, halved to 0", "the right center 1, halved to 1",
        "(y + 1)/2")
    | .full => ("−1", "1", "the left center −1", "the right center 1", "y")
  let fixed : Array Item := (disks.toArray.mapIdx fun i (name, c, ρ) =>
      Plane.Exact.disk c ρ |>.noFill |>.role (if i == 0 then leftRole else rightRole)
        |>.named name) ++ #[
    pointAmong (disks.getD 0 noDisk).2.1 disks
      (Plane.Exact.point (disks.getD 0 noDisk).2.1 |>.role leftRole |>.named tl),
    pointAmong (disks.getD 1 noDisk).2.1 disks
      (Plane.Exact.point (disks.getD 1 noDisk).2.1 |>.role rightRole |>.named tr)] ++
    (match cfg.centreLabels with
      | some (sl, sr) => #[
        Plane.Exact.label cl (disks.getD 0 noDisk).2.1 sl (some 11) |>.role leftRole,
        Plane.Exact.label cr (disks.getD 1 noDisk).2.1 sr (some 11) |>.role rightRole]
      | none => #[])
  let trail : Array Item := (cfg.pointTrail.zipIdx.filterMap fun ((y, a), i) =>
      if cfg.pointMarkShown y a k then
        let q := cfg.leftPoint y
        some (pointAmong q disks (Plane.Exact.point q |>.faint |>.size 3
          |>.named "an earlier point") |>.withId s!"trail-point-{i}")
      else none).toArray
  let idle : Array Item :=
    if cfg.idleAt k then
      let l := cfg.letterAt k
      let i := match l with | .a | .aInv => 0 | .b | .bInv => 1
      let (name, c, _) := disks.getD i noDisk
      let ring : Rat := match cfg.left with | .halved => ringRadius | .full => 2 * ringRadius
      #[Plane.Exact.circle c ring |>.dashed |>.width 2
          |>.role (if i == 0 then leftRole else rightRole)
          |>.named s!"the center of {name}, which does not hold the point"
          |>.withId s!"idle-disk-{k}"]
    else #[]
  let point : Item :=
    pointAmong p disks (Plane.Exact.point p |>.size 5 |>.named s!"the point {pt}") |>.withId "point"
  { width := cfg.width
    narrowWidth := some cfg.narrowWidth
    padding := 16
    style := partTwoStyle
    checks := .fail
    items := fixed ++ trail ++ idle ++ #[point]
    info := { title := cfg.keyCaption k } }

/-- Key `k` of the right panel (see the module docstring). -/
def FramePairConfig.centreKey (cfg : FramePairConfig) (k : Nat) : Plane.Figure :=
  let s := cfg.stateAt k
  let pl := ZetaFrac.ofZeta s.leftCentre
  let pr := ZetaFrac.ofZeta s.rightCentre
  let x := windowCentre
  let ρ := cfg.half
  let window : List (String × ZetaFrac × Rat) := [("the window", x, ρ)]
  -- the riding disks are part of the body: every centre's place relative to them is fixed
  let bodyDisks : List (String × ZetaFrac × Rat) :=
    if cfg.riding then [("the left disk, riding", pl, ρ), ("the right disk, riding", pr, ρ)]
    else []
  let fixed : Array Item := #[
    Plane.Exact.disk x ρ |>.role windowRole |>.fillOpacity 0.07 |>.named "the window"
      |>.describedBy "the closed disk |w − x| ≤ r/2 about x = 1/2" |>.declRef `TDCSG.Five.InWindow]
  let trail : Array Item := (cfg.centreTrail.zipIdx.filterMap fun ((p, a), i) =>
      if cfg.centreMarkShown p a k then
        let q := ZetaFrac.ofZeta p
        some (pointAmong q (window ++ bodyDisks) (Plane.Exact.point q |>.faint |>.size 3
          |>.named "an earlier center") |>.withId s!"trail-center-{i}")
      else none).toArray
  let disks : Array Item :=
    if cfg.riding then #[
      Plane.Exact.disk pl ρ |>.noFill |>.role leftRole |>.named "the left disk, riding"
        |>.withId "left-disk",
      Plane.Exact.disk pr ρ |>.noFill |>.role rightRole |>.named "the right disk, riding"
        |>.withId "right-disk"]
    else #[]
  let edgeName := "the unit edge from the left to the right center"
  let edge : Item := Plane.Exact.segment pl pr |>.width 1.5 |>.named edgeName |>.withId "edge"
  let graphEdge : Array Item :=
    if cfg.showsGraphEdge k then #[Plane.Exact.segment pl pr |>.width 4 |>.role windowRole
      |>.named "an edge of the center graph: both centers lie in the window"
      |>.declRef `TDCSG.Five.centerGraph |>.withId s!"graph-edge-{k}"]
    else #[]
  let centre := fun (q : ZetaFrac) (role id name : String) =>
    pointAmong q (window ++ (bodyDisks.filter fun (_, c, _) => !(c.num == q.num)))
      (Plane.Exact.point q |>.role role |>.size 5 |>.named name) |>.withId id
  let idle : Array Item :=
    if cfg.idleAt k then
      let q := match cfg.letterAt k with | .a | .aInv => pl | .b | .bInv => pr
      #[Plane.Exact.circle q ringRadius |>.dashed |>.width 2
        |>.named "the center of the letter that does not act, outside the window"
        |>.withId s!"idle-center-{k}"]
    else #[]
  let pointAtX : Item :=
    if cfg.riding then
      pointAmong x bodyDisks (Plane.Exact.point x |>.size 5
        |>.named "the point, fixed at x = 1/2")
    else Plane.Exact.point x |>.role windowRole |>.marker .cross
      |>.named "the window center x = 1/2"
  let edgeOn : Item :=
    if onSegment x s.leftCentre s.rightCentre then
      let it := pointAtX.incident .on edgeName
      if cfg.showsGraphEdge k then
        it.incident .on "an edge of the center graph: both centers lie in the window"
      else it
    else pointAtX
  { width := cfg.width
    narrowWidth := some cfg.narrowWidth
    padding := 16
    style := partTwoStyle
    checks := .fail
    items := fixed ++ trail ++ disks ++ #[edge] ++ graphEdge ++ #[edgeOn,
      centre pl leftRole "left" "the left center P(n)",
      centre pr rightRole "right" "the right center P(n + eⱼ)"] ++ idle
    info := { title := cfg.keyCaption k } }

/-! ### One view per panel -/

/-- A box of width `w` and height `h` with the centre of `b`. -/
def recentre (b : Box) (w h : Float) : Box :=
  let cx := (b.x0 + b.x1) / 2
  let cy := (b.y0 + b.y1) / 2
  ⟨cx - w / 2, cy - h / 2, cx + w / 2, cy + h / 2⟩

/-- The world box of one view for all the figures (`Plane.commonView`). -/
def viewOf (figs : Array Plane.Figure) : Box :=
  ((commonView figs)[0]?.bind (·.view)).getD ⟨0, 0, 1, 1⟩

/-- The legend of a panel: what its marks are, in a band above the view `b`, at the height `y`. -/
def legendItems (b : Box) (y : Float) (entries : Array (String × Option String)) : Array Item :=
  let n := entries.size.toFloat
  entries.mapIdx fun i (t, role) =>
    let it := Plane.label t ⟨b.x0 + (b.x1 - b.x0) * (2 * i.toFloat + 1) / (2 * n), y⟩ .center
    match role with
    | some r => it.role r
    | none => it

/-- The height of the band of the legends, in world units. -/
def legendBand : Float := 0.5

/-- The sides tried for the labels of the fixed centres of the left panel, in order. -/
def centreLabelChoices : List (Plane.Placement × Plane.Placement) :=
  [(.left, .right), (.left, .belowRight), (.left, .aboveRight), (.belowLeft, .belowRight),
    (.aboveLeft, .aboveRight), (.belowLeft, .right), (.aboveLeft, .right), (.left, .above),
    (.above, .above), (.left, .below), (.below, .below), (.left, .belowLeft),
    (.left, .aboveLeft)]

/-- Whether a figure has no layout problem at its width and at its narrow width. -/
def clean (f : Plane.Figure) : Bool :=
  f.problems.isEmpty && (f.narrow.map (·.problems.isEmpty)).getD true

/-- The keys of both panels in their views: one view for all keys of a panel, the two views of the
same size, so that a halved left panel and the right panel have one unit length, with a band
above for the legend of each panel; a full-size left panel shows the image of the halved view
under `w ↦ 2w - 1`, at half that unit length. -/
def FramePairConfig.keys (cfg : FramePairConfig) : Array (Plane.Figure × Plane.Figure) :=
  let ks := (List.range cfg.keyCount).toArray
  let rights := ks.map cfg.centreKey
  let halvedCfg := { cfg with left := .halved }
  let lb := viewOf (ks.map halvedCfg.halvedKey)
  let rb := viewOf rights
  let w := max (lb.x1 - lb.x0) (rb.x1 - rb.x0)
  let h := max (lb.y1 - lb.y0) (rb.y1 - rb.y0)
  let banded := fun (b : Box) =>
    let c := recentre b w h
    (⟨c.x0, c.y0, c.x1, c.y1 + legendBand⟩ : Box)
  let lv := banded lb
  let lv := if cfg.left == .halved then lv
    else ⟨2 * lv.x0 - 1, 2 * lv.y0, 2 * lv.x1 - 1, 2 * lv.y1⟩
  let rv := banded rb
  let pointText := match cfg.left with | .halved => "the point (y + 1)/2" | .full => "the point y"
  let pointShort := match cfg.left with | .halved => "(y + 1)/2" | .full => "y"
  let lLegendY := lv.y1 - (lv.y1 - lv.y0) * legendBand / (2 * (h + legendBand))
  let lLegend := legendItems lv lLegendY #[(pointText, none)]
  let rLegend := legendItems rv (rv.y1 - legendBand / 2)
    #[("P(n)", some leftRole), ("P(n + eⱼ)", some rightRole),
      ("x = 1/2", if cfg.riding then none else some windowRole)]
  -- the first sides of the centre labels with which every key of the left panel is clean
  let (cl, cr) := match cfg.left with | .halved => ("0", "1") | .full => ("−1", "1")
  let leftsWith := fun (sides : Option (Plane.Placement × Plane.Placement)) =>
    let legend := if sides.isSome then lLegend
      else legendItems lv lLegendY #[(s!"center {cl}", some leftRole),
        (pointShort, none), (s!"center {cr}", some rightRole)]
    ks.map fun k =>
      let a := { cfg with centreLabels := sides }.halvedKey k
      { a with view := some lv, items := legend ++ a.items }
  -- the first sides with which every key of the left panel is clean, else the legend
  let lefts := ((centreLabelChoices.find? fun sides => (leftsWith (some sides)).all clean).map
    fun sides => leftsWith (some sides)).getD (leftsWith none)
  (lefts.zip rights).map fun (a, b) =>
    (a, { b with view := some rv, items := rLegend ++ b.items })

end TDCSGFigures.Lift
