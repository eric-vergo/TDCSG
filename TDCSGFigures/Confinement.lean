/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.PartTwo
import TDCSGFigures.Style

/-!
# The figures of chapter 7, confinement

* `componentOfZero`: the 18 labels reachable from `0` in the centre graph at `r = 1.95`,
  `x = 1/2`, each drawn at its projection `P(n)` (a dot for weight zero, a square for weight one),
  with the edges of the graph, the window, and for each coordinate `j` the good levels nearest the
  gap `|m| ≤ 2`, the candidates for the walls `lo` and `hi` of the confinement proof.
* `walkToLeaf`: a stepper along a path of the centre graph at `r = 2.13`, `x = 1/5`, found by a
  breadth-first search from `0`: it lowers the coordinate `n₂` from `0` to `-4`, crosses the good
  level `-5` into the label `n = (0, 3, -5, 4, -2)`, whose other candidates `n + eₖ` all lie
  outside the window, and can only step back.
-/

namespace TDCSGFigures.Confinement

open PILean PILean.Plane PILean.Exact TDCSGFigures

/-- The integer vector of a label, as text. -/
def labelText (n : Label) : String :=
  "(" ++ ", ".intercalate (n.toList.map fun k => if k < 0 then s!"−{-k}" else toString k) ++ ")"

/-- The subscript digit `k`. -/
def sub (k : Nat) : String := #["₀", "₁", "₂", "₃", "₄"].getD k ""

/-- An integer with a true minus sign. -/
def intText (k : Int) : String := if k < 0 then s!"−{-k}" else toString k

/-- The edges `n — n + eⱼ` among `labels`, `n` of weight zero, in the order of `labels` and `j`. -/
def edgesAmong (labels : List Label) : List (Label × Label) :=
  labels.flatMap fun n =>
    if weight n == 0 then
      (List.range 5).filterMap fun j =>
        let m := shift n j 1
        if labels.contains m then some (n, m) else none
    else []

/-- A label drawn at its projection: a dot in the colour of left centres for weight zero, a square
in the colour of right centres for weight one, titled with its integer vector, recording that it
lies in the window `title`. -/
def labelPoint (n : Label) (rel : Incidence) (window : String) : Item :=
  let it := Plane.Exact.point (proj n) |>.size 4.5
    |>.named s!"the label {labelText n}, weight {weight n}"
    |>.incident rel window
  if weight n == 0 then it.role leftRole else it.role rightRole |>.marker .square

/-- The edge from `n` to `m`, linked to the centre graph. -/
def edgeItem (n m : Label) : Item :=
  Plane.Exact.segment (proj n) (proj m) |>.width 1.5
    |>.named s!"the edge from {labelText n} to {labelText m}"
    |>.declRef `TDCSG.Five.centerGraph

/-! ### The component of `0` -/

/-- `r = 1.95`. -/
def compRadius : Rat := 39 / 20

/-- `r²`. -/
def compRadiusSq : QSqrt5 := rat (compRadius * compRadius)

/-- The window centre `x = 1/2`. -/
def compX : Rat := 1 / 2

/-- The component of `0`, as the search found it (empty if it did not finish). -/
def compLabels : List Label := ((component compRadiusSq compX).getD #[]).toList

/-- The edges of the component. -/
def compEdges : List (Label × Label) := edgesAmong compLabels

/-- The good levels of coordinate `j` nearest the gap `|m| ≤ 2`: the largest good level at most
`-3` and the least at least `3`, among `|m| ≤ 20`. -/
def nearestWalls (j : Nat) : Option Int × Option Int :=
  let good := fun m => isGoodLevel compRadiusSq compX j m == some true
  (((List.range 18).map fun (i : Nat) => -(i : Int) - 3).find? good,
    ((List.range 18).map fun (i : Nat) => (i : Int) + 3).find? good)

/-- The walls of coordinate `j` as text. -/
def wallText (j : Nat) : String :=
  let (lo, hi) := nearestWalls j
  s!"n{sub j}: {(lo.map intText).getD "none"}, {(hi.map intText).getD "none"}"

/-- The 18 labels reachable from 0 in the centre graph at r = 1.95, x = 1/2, at their projections:
dots for weight 0 (left centres), squares for weight 1 (right centres), with the edges, the
window, and the good levels nearest the gap |m| ≤ 2 in each coordinate. -/
@[figure]
def componentOfZero : Plane.Figure where
  width := figureWidth
  height := some 600
  narrowWidth := some narrowWidth
  padding := 16
  style := partTwoStyle
  checks := .fail
  items := #[
    Plane.Exact.disk ((compX, 0) : Rat × Rat) (39 / 40 : Rat) |>.role windowRole
      |>.fillOpacity 0.07 |>.named "the window"
      |>.describedBy "the closed disk |w − x| ≤ r/2, r = 1.95, x = 1/2"
      |>.declRef `TDCSG.Five.InWindow] ++
    (compEdges.toArray.map fun (n, m) => edgeItem n m) ++
    (compLabels.toArray.map fun n => labelPoint n .inside "the window") ++ #[
    Plane.Exact.point ((compX, 0) : Rat × Rat) |>.role windowRole |>.marker .cross
      |>.named "the window centre x = 1/2" |>.incident .inside "the window"
      |>.incident .on "the edge from (0, 0, 0, 0, 0) to (1, 0, 0, 0, 0)",
    Plane.Exact.label "0" origin (.toward (Plane.deg 200)) |>.role leftRole,
    Plane.Exact.label "e₀" rightCentre .auto |>.role rightRole,
    Plane.Exact.label "dots: weight 0 (left centres)" ((1 / 2 : Rat), (-9 / 8 : Rat))
      |>.role leftRole,
    Plane.Exact.label "squares: weight 1 (right centres)" ((1 / 2 : Rat), (-5 / 4 : Rat))
      |>.role rightRole,
    Plane.Exact.label "good levels lo ≤ −3, hi ≥ 3 nearest 0:" ((1 / 2 : Rat), (-11 / 8 : Rat))
      |>.role goodRole |>.declRef `TDCSG.Five.exists_abs_le_of_centerReach,
    Plane.Exact.label s!"{wallText 0}   {wallText 1}   {wallText 2}"
      ((1 / 2 : Rat), (-3 / 2 : Rat)) |>.role goodRole,
    Plane.Exact.label s!"{wallText 3}   {wallText 4}" ((1 / 2 : Rat), (-13 / 8 : Rat))
      |>.role goodRole,
    Plane.Exact.label "every coordinate here is −1, 0 or 1" ((1 / 2 : Rat), (-7 / 4 : Rat)),
    Plane.Exact.label "×: the window centre x = 1/2" ((1 / 2 : Rat), (-15 / 8 : Rat))
      |>.role windowRole]
  info := { title := "The component of 0 in the centre graph at r = 1.95, x = 1/2" }

/-! ### A walk forced back at a leaf -/

/-- `r = 2.13`. -/
def walkRadius : Rat := 213 / 100

/-- `r²`. -/
def walkRadiusSq : QSqrt5 := rat (walkRadius * walkRadius)

/-- The window centre `x = 1/5`. -/
def walkX : Rat := 1 / 5

/-- A path of the centre graph from `0` to `n = (0, 3, -5, 4, -2)`, as a breadth-first search
from `0` found it: each step adds `±eₖ`, and the coordinate `n₂` falls from `0` to `-5`. -/
def path : List Label := [#[0, 0, 0, 0, 0], #[0, 1, 0, 0, 0], #[0, 1, -1, 0, 0],
  #[0, 1, -1, 1, 0], #[0, 1, -1, 1, -1], #[0, 1, -1, 2, -1], #[0, 1, -2, 2, -1],
  #[0, 2, -2, 2, -1], #[0, 2, -3, 2, -1], #[0, 2, -3, 3, -1], #[0, 2, -3, 3, -2],
  #[0, 2, -3, 4, -2], #[0, 2, -4, 4, -2], #[0, 3, -4, 4, -2], #[0, 3, -5, 4, -2]]

/-- The leaf `n = (0, 3, -5, 4, -2)`, of weight zero, at the good level `n₂ = -5`. -/
def leafN : Label := #[0, 3, -5, 4, -2]

/-- Its only neighbour `n + e₂`. -/
def beforeLeaf : Label := shift leafN 2 1

/-- Where a label stands relative to the window of the walk. -/
def walkSide (n : Label) : Incidence :=
  if inWindow walkRadiusSq walkX n then .inside else .outside

/-- The world box of the walk's frames. -/
def walkView : Box := ⟨-1.0, -1.65, 2.3, 1.3⟩

/-- The frame of `walkToLeaf` that draws the first `k` labels of the path, numbered in the order
of the walk, with the candidates `n + eₖ` of the leaf when `candidates`, and the step back when
`back`. -/
def walkFrame (k : Nat) (candidates back : Bool) (title : String) : Plane.Figure :=
  let ps := path.take k
  let steps := ps.zip ps.tail
  let window := "the window"
  { width := figureWidth
    view := some walkView
    padding := 16
    style := partTwoStyle
    checks := .fail
    items := #[
      Plane.Exact.disk ((walkX, 0) : Rat × Rat) (213 / 200 : Rat) |>.role windowRole
        |>.fillOpacity 0.07 |>.named window
        |>.describedBy "the closed disk |w − x| ≤ r/2, r = 2.13, x = 1/5"
        |>.declRef `TDCSG.Five.InWindow,
      Plane.Exact.point ((walkX, 0) : Rat × Rat) |>.role windowRole |>.marker .cross
        |>.named "the window centre x = 1/5" |>.incident .inside window] ++
      (steps.toArray.map fun (a, b) =>
        let last := b == leafN
        Plane.Exact.segment (proj a) (proj b) |>.width (if last then 3.5 else 1.5)
          |>.named (if last then
              "the step from n + e₂ to n: it lowers n₂ from −4 to the good level −5"
            else s!"the step from {labelText a} to {labelText b}")
          |>.declRef (if last then `TDCSG.Five.leaf_of_crossing else `TDCSG.Five.centerGraph)) ++
      (if candidates then (List.range 5).toArray.filterMap fun j =>
        if j == 2 then none else
          some (Plane.Exact.segment (proj leafN) (proj (shift leafN j 1)) |>.faint |>.dashed
            |>.named s!"the rejected step from n to n + e{sub j}") else #[]) ++
      (ps.toArray.map fun n => labelPoint n (walkSide n) window) ++
      (if candidates then (List.range 5).toArray.filterMap fun j =>
        if j == 2 then none else
          let m := shift leafN j 1
          some (Plane.Exact.point (proj m) |>.faint |>.marker .ring |>.size 4.5
            |>.named s!"n + e{sub j} = {labelText m}, outside the window"
            |>.incident (walkSide m) window) else #[]) ++
      (if back then #[Plane.Exact.arrow (proj leafN) (proj beforeLeaf) |>.width 2
          |>.named "the only step from n: back to n + e₂"
          |>.declRef `SimpleGraph.Reachable.mem_or_exists_adj_of_leaf] else #[]) ++ #[
      Plane.Exact.label "0" origin (.toward (Plane.deg 200)) |>.role leftRole,
      Plane.Exact.label "x = 1/5" ((walkX, 0) : Rat × Rat) .auto |>.role windowRole,
      Plane.Exact.label "window" ((rat (1 / 5), rat (23 / 20)) : QSqrt5 × QSqrt5)
        |>.role windowRole,
      Plane.Exact.label "dots: weight 0   squares: weight 1"
        ((rat (2 / 5), rat (-3 / 2)) : QSqrt5 × QSqrt5)] ++
      (ps.toArray.mapIdx fun i n => if i == 0 || n == leafN || n == beforeLeaf then #[] else
        #[Plane.Exact.label s!"{i}" (proj n) .auto |>.size 11]).flatten ++
      (if k ≥ path.length - 1 then #[Plane.Exact.label "n + e₂" (proj beforeLeaf) .auto
        |>.role rightRole] else #[]) ++
      (if k ≥ path.length then #[Plane.Exact.label "n" (proj leafN) .auto |>.role leftRole,
        Plane.Exact.label "n₂ = −5 at n: a good level"
          ((rat (2 / 5), rat (-13 / 8)) : QSqrt5 × QSqrt5) |>.role goodRole] else #[]) ++
      (if candidates then (List.range 5).toArray.filterMap fun j =>
        if j == 2 then none else
          some (Plane.Exact.label s!"n + e{sub j}" (proj (shift leafN j 1)) .auto |>.faint)
        else #[])
    info := { title } }

/-- The steps of `walkToLeaf`, with their captions. -/
def walkFrames : Array (String × Plane.Figure) := #[
  ("the walk from 0 lowers n₂ from 0 to −4", walkFrame (path.length - 1) false false
    "A path of the centre graph from 0 to n + e₂ = (0, 3, −4, 4, −2)"),
  ("it crosses the good level n₂ = −5 into n", walkFrame path.length false false
    "The step into n = (0, 3, −5, 4, −2) crosses the good level −5 of n₂"),
  ("n is a leaf: its other candidates lie outside the window", walkFrame path.length true false
    "The other candidates n + eₖ of n lie outside the window"),
  ("the walk can only step back", walkFrame path.length true true
    "From the leaf n the only step leads back to n + e₂")]

/-- A path of the centre graph at r = 2.13, x = 1/5 from 0 lowers n₂ to −4, crosses the good level
−5 into a leaf and is forced back. -/
@[figure]
def walkToLeaf : Explorer := Plane.stepper walkFrames

/-! ### The facts the figures show -/

-- The component of `0` at `r = 1.95`, `x = 1/2` has 18 labels, every coordinate of each is
-- `-1`, `0` or `1`, and each lies strictly between the walls of every coordinate.
#guard compLabels.length == 18 &&
  compLabels.all (fun n => n.all fun c => -1 ≤ c && c ≤ 1) &&
  (List.range 5).all fun j => match nearestWalls j with
    | (some lo, some hi) => compLabels.all fun n => lo < n[j]! && n[j]! ≤ hi
    | _ => false

-- The walls nearest the gap: `(-4, 4)`, `(-3, 10)`, `(-7, 6)`, `(-7, 6)`, `(-3, 10)`.
#guard (List.range 5).map nearestWalls ==
  [(some (-4), some 4), (some (-3), some 10), (some (-7), some 6), (some (-7), some 6),
    (some (-3), some 10)]

-- The path is a path of the centre graph at `r = 2.13`, `x = 1/5`: consecutive labels differ by
-- one unit vector, the weights alternate, every label lies in the window.
#guard path.all (fun n => inWindow walkRadiusSq walkX n) &&
  (path.zip path.tail).all (fun (a, b) => (List.range 5).any fun j =>
    b == shift a j 1 || b == shift a j (-1)) &&
  path.head? == some zeroLabel && path.getLast? == some leafN

-- The level `n₂ = -5` of the leaf is good, and `-4` is not; every other candidate `n + eₖ` of
-- the leaf lies outside the window, so `n + e₂` is its only neighbour.
#guard isGoodLevel walkRadiusSq walkX 2 (-5) == some true &&
  isGoodLevel walkRadiusSq walkX 2 (-4) == some false &&
  [0, 1, 3, 4].all (fun j => !inWindow walkRadiusSq walkX (shift leafN j 1)) &&
  weight leafN == 0

set_option maxHeartbeats 4000000 in
/-- What `componentOfZero` draws, and why its records are right. The items are the window, then
an edge `edgeItem n m` for each edge of `compEdges`, a point `labelPoint n` for each label of
`compLabels`, the window centre and the labels, in this order; the builders' definitions are
stated. The component of `0` found by the exact search (`component`, every window test decided
in `ℚ(√5)`) is the list of 18 labels written out, and its edges are the 18 written out, each
from a weight-zero label `n` to `n + eⱼ`; every label lies inside the window, so each point's
record holds. Every coordinate of every label is `-1`, `0` or `1`, and in each coordinate `j` the
good levels nearest the gap `|m| ≤ 2` are those the labels show (`wallText`), with every label
strictly inside the slab `lo < nⱼ ≤ hi` they bound. Not stated: how the builders and modifiers
draw, the layout, the lettering, the style's colour values and the pixels. -/
theorem componentOfZero_spec :
    (∀ n m, edgeItem n m = (Plane.Exact.segment (proj n) (proj m) |>.width 1.5
      |>.named s!"the edge from {labelText n} to {labelText m}"
      |>.declRef `TDCSG.Five.centerGraph)) ∧
    (∀ n rel w, labelPoint n rel w = (if weight n == 0 then
      (Plane.Exact.point (proj n) |>.size 4.5
        |>.named s!"the label {labelText n}, weight {weight n}"
        |>.incident rel w |>.role "left")
      else (Plane.Exact.point (proj n) |>.size 4.5
        |>.named s!"the label {labelText n}, weight {weight n}" |>.incident rel w |>.role "right"
        |>.marker .square))) ∧
    componentOfZero.items = #[
      Plane.Exact.disk ((compX, 0) : Rat × Rat) (39 / 40 : Rat) |>.role "window"
        |>.fillOpacity 0.07 |>.named "the window"
        |>.describedBy "the closed disk |w − x| ≤ r/2, r = 1.95, x = 1/2"
        |>.declRef `TDCSG.Five.InWindow] ++
      (compEdges.toArray.map fun (n, m) => edgeItem n m) ++
      (compLabels.toArray.map fun n => labelPoint n .inside "the window") ++ #[
      Plane.Exact.point ((compX, 0) : Rat × Rat) |>.role "window" |>.marker .cross
        |>.named "the window centre x = 1/2" |>.incident .inside "the window"
        |>.incident .on "the edge from (0, 0, 0, 0, 0) to (1, 0, 0, 0, 0)",
      Plane.Exact.label "0" origin (.toward (Plane.deg 200)) |>.role "left",
      Plane.Exact.label "e₀" rightCentre .auto |>.role "right",
      Plane.Exact.label "dots: weight 0 (left centres)" ((1 / 2 : Rat), (-9 / 8 : Rat))
        |>.role "left",
      Plane.Exact.label "squares: weight 1 (right centres)" ((1 / 2 : Rat), (-5 / 4 : Rat))
        |>.role "right",
      Plane.Exact.label "good levels lo ≤ −3, hi ≥ 3 nearest 0:"
        ((1 / 2 : Rat), (-11 / 8 : Rat)) |>.role "good"
        |>.declRef `TDCSG.Five.exists_abs_le_of_centerReach,
      Plane.Exact.label s!"{wallText 0}   {wallText 1}   {wallText 2}"
        ((1 / 2 : Rat), (-3 / 2 : Rat)) |>.role "good",
      Plane.Exact.label s!"{wallText 3}   {wallText 4}" ((1 / 2 : Rat), (-13 / 8 : Rat))
        |>.role "good",
      Plane.Exact.label "every coordinate here is −1, 0 or 1" ((1 / 2 : Rat), (-7 / 4 : Rat)),
      Plane.Exact.label "×: the window centre x = 1/2" ((1 / 2 : Rat), (-15 / 8 : Rat))
        |>.role "window"] ∧
    compLabels = [#[0, 0, 0, 0, 0], #[1, 0, 0, 0, 0], #[0, 1, 0, 0, 0], #[0, 0, 0, 0, 1],
      #[0, 0, 0, -1, 1], #[0, 0, 1, -1, 1], #[0, -1, 1, -1, 1], #[1, -1, 1, -1, 1],
      #[1, -1, 1, -1, 0], #[1, -1, 1, 0, 0], #[1, -1, 0, 0, 0], #[0, 1, -1, 0, 0],
      #[0, 1, -1, 1, 0], #[0, 1, -1, 1, -1], #[1, 1, -1, 1, -1], #[1, 0, -1, 1, -1],
      #[1, 0, 0, 1, -1], #[1, 0, 0, 0, -1]] ∧
    compEdges = [(#[0, 0, 0, 0, 0], #[1, 0, 0, 0, 0]), (#[0, 0, 0, 0, 0], #[0, 1, 0, 0, 0]),
      (#[0, 0, 0, 0, 0], #[0, 0, 0, 0, 1]), (#[0, 0, 0, -1, 1], #[0, 0, 1, -1, 1]),
      (#[0, 0, 0, -1, 1], #[0, 0, 0, 0, 1]), (#[0, -1, 1, -1, 1], #[1, -1, 1, -1, 1]),
      (#[0, -1, 1, -1, 1], #[0, 0, 1, -1, 1]), (#[1, -1, 1, -1, 0], #[1, -1, 1, 0, 0]),
      (#[1, -1, 1, -1, 0], #[1, -1, 1, -1, 1]), (#[1, -1, 0, 0, 0], #[1, 0, 0, 0, 0]),
      (#[1, -1, 0, 0, 0], #[1, -1, 1, 0, 0]), (#[0, 1, -1, 0, 0], #[0, 1, 0, 0, 0]),
      (#[0, 1, -1, 0, 0], #[0, 1, -1, 1, 0]), (#[0, 1, -1, 1, -1], #[1, 1, -1, 1, -1]),
      (#[0, 1, -1, 1, -1], #[0, 1, -1, 1, 0]), (#[1, 0, -1, 1, -1], #[1, 1, -1, 1, -1]),
      (#[1, 0, -1, 1, -1], #[1, 0, 0, 1, -1]), (#[1, 0, 0, 0, -1], #[1, 0, 0, 1, -1]),
      (#[1, 0, 0, 0, -1], #[1, 0, 0, 0, 0])] ∧
    compLabels.all (fun n => inWindow compRadiusSq compX n) = true ∧
    compEdges.all (fun (n, m) => weight n == 0 &&
      (List.range 5).any fun j => m == shift n j 1) = true ∧
    compLabels.all (fun n => n.all fun c => -1 ≤ c && c ≤ 1) = true ∧
    [wallText 0, wallText 1, wallText 2, wallText 3, wallText 4] =
      ["n₀: −4, 4", "n₁: −3, 10", "n₂: −7, 6", "n₃: −7, 6", "n₄: −3, 10"] ∧
    (List.range 5).all (fun j => match nearestWalls j with
      | (some lo, some hi) => compLabels.all fun n => lo < n[j]! && n[j]! ≤ hi
      | _ => false) = true := by
  refine ⟨fun _ _ => rfl, fun n _ _ => ?_, rfl, ?_⟩
  · unfold labelPoint
    split <;> rfl
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves componentOfZero componentOfZero_spec

/-- What `walkToLeaf` shows. It is the stepper of `walkFrames`: four frames, built by `walkFrame`,
that draw the path `path` of 15 labels up to `n + e₂ = (0, 3, -4, 4, -2)`, then up to the leaf
`n = (0, 3, -5, 4, -2)`, then with the candidates `n + eₖ` (`k ≠ 2`), then with the step back.
The data are checked exactly at `r = 2.13`, `x = 1/5`: the path starts at `0`, consecutive labels
differ by one unit vector, every label lies in the window, so the path is a path of the centre
graph; `n` has weight zero, its level `n₂ = -5` is good, and its candidates `n + e₀`, `n + e₁`,
`n + e₃`, `n + e₄` lie outside the window, so `n + e₂` is its only neighbour. Not stated: the
items of each frame, the layout and the pixels. -/
theorem walkToLeaf_spec :
    walkToLeaf = Plane.stepper walkFrames ∧ walkFrames.map (·.1) = #[
      "the walk from 0 lowers n₂ from 0 to −4", "it crosses the good level n₂ = −5 into n",
      "n is a leaf: its other candidates lie outside the window", "the walk can only step back"] ∧
    leafN = #[0, 3, -5, 4, -2] ∧ path.length = 15 ∧
    path.head? = some zeroLabel ∧ path.getLast? = some leafN ∧
    path.all (fun n => inWindow walkRadiusSq walkX n) = true ∧
    (path.zip path.tail).all (fun (a, b) => (List.range 5).any fun j =>
      b == shift a j 1 || b == shift a j (-1)) = true ∧
    weight leafN = 0 ∧ isGoodLevel walkRadiusSq walkX 2 (-5) = some true ∧
    [0, 1, 3, 4].all (fun j => !inWindow walkRadiusSq walkX (shift leafN j 1)) = true := by
  refine ⟨rfl, by simp [walkFrames], rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves walkToLeaf walkToLeaf_spec

end TDCSGFigures.Confinement
