/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.PartTwo
import TDCSGFigures.Style
import TDCSGFigures.Data.Moves

/-!
# The figures of chapter 7, confinement

* `componentOfZero`: the 18 labels reachable from `0` in the center graph at `r = 1.95`,
  `x = 1/2`, each drawn at its projection `P(n)` (a dot for weight zero, a square for weight one),
  with the edges of the graph and the window. For each coordinate `j` the good levels nearest the
  gap `|m| ≤ 2`, the candidates for the walls `lo` and `hi` of the confinement proof, are computed
  (`nearestWalls`) and stated with the figure, for its caption.
* `walkToLeaf`: an animation of a walk along a path of the center graph at `r = 2.13`, `x = 1/5`,
  found by a breadth-first search from `0` (an illustration): a circle slides from label to label,
  one step `±eⱼ` at a time (a slide by `±ζʲ`), and the edges and labels appear as it reaches them;
  it lowers the coordinate `n₂` from `0` to `-4`, crosses the good level `-5` into the label
  `n = (0, 3, -5, 4, -2)`, whose other candidates `n + eₖ` all lie outside the window, and steps
  back. Every slide is checked exactly (`walkArrives`).
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

/-- A label drawn at its projection, a marker of radius `size`: a dot in the colour of left centres
for weight zero, a square in the colour of right centres for weight one, titled with its integer
vector, recording that it lies in the window `title`. -/
def labelPoint (n : Label) (rel : Incidence) (window : String) (size : Float := 4.5) : Item :=
  let it := Plane.Exact.point (proj n) |>.size size
    |>.named s!"the label {labelText n}, weight {weight n}"
    |>.incident rel window
  if weight n == 0 then it.role leftRole else it.role rightRole |>.marker .square

/-- The edge from `n` to `m`, linked to the center graph. -/
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

/-- The 18 labels reachable from 0 in the center graph at r = 1.95, x = 1/2, at their projections:
dots for weight 0 (left centres), squares for weight 1 (right centres), with the edges, the
window and its centre. -/
@[figure]
def componentOfZero : Plane.Figure where
  width := figureWidth
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
      |>.named "the window center x = 1/2" |>.incident .inside "the window"
      |>.incident .on "the edge from (0, 0, 0, 0, 0) to (1, 0, 0, 0, 0)",
    Plane.Exact.label "0" origin (.toward (Plane.deg 200)) |>.role leftRole,
    Plane.Exact.label "e₀" rightCentre .auto |>.role rightRole,
    Plane.Exact.label "dots: weight 0 (left centers)" ((1 / 2 : Rat), (-9 / 8 : Rat))
      |>.role leftRole,
    Plane.Exact.label "squares: weight 1 (right centers)" ((1 / 2 : Rat), (-5 / 4 : Rat))
      |>.role rightRole,
    Plane.Exact.label "×: the window center x = 1/2" ((1 / 2 : Rat), (-11 / 8 : Rat))
      |>.role windowRole]
  info := { title := "The component of 0 in the center graph at r = 1.95, x = 1/2" }

/-! ### A walk forced back at a leaf -/

/-- `r = 2.13`. -/
def walkRadius : Rat := 213 / 100

/-- `r²`. -/
def walkRadiusSq : QSqrt5 := rat (walkRadius * walkRadius)

/-- The window centre `x = 1/5`. -/
def walkX : Rat := 1 / 5

/-- A path of the center graph from `0` to `n = (0, 3, -5, 4, -2)`, as a breadth-first search
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
def walkView : Box := ⟨-1.0, -1.95, 2.3, 1.3⟩

/-- The radius of the circle that marks where the walk is. -/
def walkerRadius : Rat := 1 / 20

/-- The radius of the markers of the labels of the walk, in pixels, small enough that the markers
of `n + e₂` and of the window centre stay apart at the narrow width. -/
def walkMarkerSize : Float := 3.5

/-- The label where the walk is at key `k` of `walkToLeaf`: `path[k]` up to the leaf (`k ≤ 14`),
the leaf at key `15`, and `n + e₂` at key `16`, after the step back. -/
def walkAt (k : Nat) : Label :=
  if k ≤ path.length - 1 then path.getD k zeroLabel
  else if k == path.length then leafN
  else beforeLeaf

/-- The number of labels of the path drawn at key `k`: `k + 1` up to the leaf, all after. -/
def walkShown (k : Nat) : Nat := min (k + 1) path.length

/-- The unit vector of the step from `a` to `b` and its sign, `(j, s)` with `b = a + s eⱼ`. -/
def stepDir (a b : Label) : Nat × Int :=
  ((List.range 5).find? (fun j => b == shift a j 1 || b == shift a j (-1))).elim (0, 0) fun j =>
    (j, if b == shift a j 1 then 1 else -1)

/-- The circle that marks where the walk is (actor `"walker"`), about `P(walkAt k)`. -/
def walker (k : Nat) : Item :=
  Plane.Exact.circle (proj (walkAt k)) walkerRadius |>.width 2
    |>.named "a circle about the label where the walk is" |>.withId "walker"

/-- The items of key `k` of `walkToLeaf` (`k ≤ 16`): the window, the edges and labels of the path up
to `path[k]` (all of it from key `14` on); from key `15` on the
candidates `n + eₖ` of the leaf, `k ≠ 2`, outside the window; at key `16` the step back; the
circle about the label where the walk is. Each part of the path, each candidate and the step back
is an actor that appears with the key that first shows it. -/
def walkKey (k : Nat) : Plane.Figure :=
  let shown := walkShown k
  let ps := path.take shown
  let steps := ps.zip ps.tail
  let candidates := decide (path.length ≤ k)
  let back := decide (path.length + 1 ≤ k)
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
        |>.named "the window center x = 1/5" |>.incident .inside window] ++
      (steps.toArray.mapIdx fun i (a, b) =>
        let last := b == leafN
        Plane.Exact.segment (proj a) (proj b) |>.width (if last then 3.5 else 1.5)
          |>.named (if last then
              "the step from n + e₂ to n: it lowers n₂ from −4 to the good level −5"
            else s!"the step from {labelText a} to {labelText b}")
          |>.declRef (if last then `TDCSG.Five.leaf_of_crossing else `TDCSG.Five.centerGraph)
          |>.withId s!"edge-{i}") ++
      (if candidates then (List.range 5).toArray.filterMap fun j =>
        if j == 2 then none else
          some (Plane.Exact.segment (proj leafN) (proj (shift leafN j 1)) |>.faint |>.dashed
            |>.named s!"the rejected step from n to n + e{sub j}" |>.withId s!"reject-{j}")
        else #[]) ++
      (ps.toArray.mapIdx fun i n =>
        labelPoint n (walkSide n) window walkMarkerSize |>.withId s!"label-{i}") ++
      (if candidates then (List.range 5).toArray.filterMap fun j =>
        if j == 2 then none else
          let m := shift leafN j 1
          some (Plane.Exact.point (proj m) |>.faint |>.marker .ring |>.size walkMarkerSize
            |>.named s!"n + e{sub j} = {labelText m}, outside the window"
            |>.incident (walkSide m) window |>.withId s!"candidate-{j}") else #[]) ++
      (if back then #[Plane.Exact.arrow (proj leafN) (proj beforeLeaf) |>.width 2
          |>.named "the only step from n: back to n + e₂"
          |>.declRef `SimpleGraph.Reachable.mem_or_exists_adj_of_leaf |>.withId "back"]
        else #[]) ++
      #[walker k] ++ #[
      Plane.Exact.label "0" origin (.toward (Plane.deg 200)) (some 14) |>.role leftRole,
      Plane.Exact.label "window" ((rat (1 / 5), rat (23 / 20)) : QSqrt5 × QSqrt5)
        |>.role windowRole,
      Plane.Exact.label "dots: weight 0 (left centers)"
        ((rat (2 / 5), rat (-29 / 20)) : QSqrt5 × QSqrt5) |>.role leftRole,
      Plane.Exact.label "squares: weight 1 (right centers)"
        ((rat (2 / 5), rat (-8 / 5)) : QSqrt5 × QSqrt5) |>.role rightRole,
      Plane.Exact.label "×: the window center x = 1/5"
        ((rat (2 / 5), rat (-7 / 4)) : QSqrt5 × QSqrt5) |>.role windowRole] ++
      (if shown ≥ path.length - 1 then #[Plane.Exact.label "n + e₂" (proj beforeLeaf) .auto
        |>.role rightRole |>.withId "name-before"] else #[]) ++
      (if shown ≥ path.length then #[Plane.Exact.label "n" (proj leafN)
          (.toward (Plane.deg (-36))) (some 14) |>.role leftRole
          |>.withId "name-leaf",
        Plane.Exact.label "n₂ = −5 at n: a good level"
          ((rat (2 / 5), rat (-19 / 10)) : QSqrt5 × QSqrt5) |>.role goodRole
          |>.withId "good-level"] else #[]) ++
      (if candidates then (List.range 5).toArray.filterMap fun j =>
        if j == 2 then none else
          some (Plane.Exact.label s!"n + e{sub j}" (proj (shift leafN j 1)) .auto |>.faint
            |>.withId s!"candidate-label-{j}")
        else #[])
    info := { title := s!"The walk at key {k}" } }

/-- The step `k` of the walk as text: its unit vector with its sign. -/
def stepText (k : Nat) : String :=
  let (j, sgn) := stepDir (path.getD k zeroLabel) (path.getD (k + 1) zeroLabel)
  s!"{if sgn == 1 then "+" else "−"} e{sub j}"

/-- The caption of key `k` of `walkToLeaf`. -/
def walkCaption (k : Nat) : String :=
  let n := path.getD k zeroLabel
  if k == 0 then
    "A walk in the center graph at r = 2.13, x = 1/5, from the label 0, along a path that a \
      breadth-first search found; the circle marks where the walk is. Each step adds or removes \
      one unit vector eⱼ, and every label lies in the window."
  else if k + 2 < path.length then
    s!"Move {k}: {stepText (k - 1)}, to {labelText n}; n₂ = {intText (n.getD 2 0)}."
  else if k + 2 == path.length then
    s!"Move {k}: {stepText (k - 1)}, to n + e₂ = {labelText n}: n₂ has fallen from 0 to −4."
  else if k + 1 == path.length then
    s!"Move {k}: {stepText (k - 1)}, into n = {labelText n}: the step crosses the good level −5 \
      of n₂."
  else if k == path.length then
    "n is a leaf: its other candidates n + eₖ, k ≠ 2, lie outside the window (open rings at the \
      ends of dashed spokes)."
  else
    "From the leaf n the only step leads back to n + e₂, as the one-step lemma requires."

/-- The ids of the labels of text that key `k` of `walkToLeaf` shows and that appear during the
walk: the names `n + e₂` (from key `13` on), `n` and its good level (from key `14` on), and the
names of the candidates (from key `15` on). -/
def walkNameIds (k : Nat) : List String :=
  (if path.length - 2 ≤ k then ["name-before"] else []) ++
    (if path.length - 1 ≤ k then ["name-leaf", "good-level"] else []) ++
    (if path.length ≤ k then [0, 1, 3, 4].map (s!"candidate-label-{·}") else [])

/-- The declared moves from key `k` to key `k + 1` of `walkToLeaf`: along the path, the circle
slides from `P(path[k])` to `P(path[k + 1])`, by `±ζʲ` for a step `±eⱼ`, while the edge and the
label it reaches appear, with the names that key `k + 1` shows first; at the leaf, the candidates,
their spokes and their names appear; then the circle slides back to `P(n + e₂)` while the step
back appears. -/
def walkMoves (k : Nat) : List (String × ExactMove ZetaFrac) :=
  let slide :=
    ("walker", ExactMove.slide (ZetaFrac.ofZeta (proj (walkAt (k + 1)) - proj (walkAt k))))
  let names := ((walkNameIds (k + 1)).filter (!(walkNameIds k).contains ·)).map (·, .appear)
  if k + 1 < path.length then
    [slide, (s!"edge-{k}", .appear), (s!"label-{k + 1}", .appear)] ++ names
  else if k + 1 == path.length then
    ([0, 1, 3, 4].map (s!"reject-{·}", .appear)) ++
      ([0, 1, 3, 4].map (s!"candidate-{·}", .appear)) ++ names
  else [slide, ("back", .appear)]

/-- The exact anchors of the actors of key `k` of `walkToLeaf` that move or carry a meaning by
their place: the circle about `P(walkAt k)`, the labels of the path shown (`P(path[i])`), the
ends of the edges, the candidates and their spokes, and the ends of the step back; the labels of
text are listed without anchors. -/
def walkActors (k : Nat) : List (ExactActor ZetaFrac) :=
  let z := ZetaFrac.ofZeta
  let ps := path.take (walkShown k)
  let cands := if path.length ≤ k then [0, 1, 3, 4] else []
  [⟨"walker", [z (proj (walkAt k))]⟩] ++
    ((ps.zip ps.tail).zipIdx.map fun ((a, b), i) => ⟨s!"edge-{i}", [z (proj a), z (proj b)]⟩) ++
    (ps.zipIdx.map fun (n, i) => ⟨s!"label-{i}", [z (proj n)]⟩) ++
    (cands.map fun j => ⟨s!"reject-{j}", [z (proj leafN), z (proj (shift leafN j 1))]⟩) ++
    (cands.map fun j => ⟨s!"candidate-{j}", [z (proj (shift leafN j 1))]⟩) ++
    (if path.length + 1 ≤ k then [⟨"back", [z (proj leafN), z (proj beforeLeaf)]⟩] else []) ++
    (walkNameIds k).map fun id => ⟨id, []⟩

/-- Whether every declared move of `walkToLeaf` carries the actors of one key onto those of the
next, exactly in `ℚ(ζ₅)`. -/
def walkArrives : Bool := allArrive (path.length + 1) walkMoves walkActors

/-- The number of keys of `walkToLeaf`: one per label of the path, the candidates, the step
back. -/
def walkKeyCount : Nat := path.length + 2

/-- A path of the center graph at r = 2.13, x = 1/5 from 0, walked step by step: it lowers n₂ to
−4, crosses the good level −5 into a leaf, finds the other candidates outside the window and is
forced back. It has no narrow rendition: at the narrow width the marker of n + e₂ would touch the
window center and the legend would cover the candidate n + e₄, so on a small screen the picture
is scaled down as a whole. -/
@[figure illustration]
def walkToLeaf : MotionPanels where
  panels := #[{ motion := { keys := ((List.range walkKeyCount).map walkKey).toArray,
                            steps := ((List.range (walkKeyCount - 1)).map fun k =>
                              exactStep (walkMoves k)).toArray } }]
  captions := ((List.range walkKeyCount).map walkCaption).toArray
  pacing := motionPacing
  timing := ((List.range (walkKeyCount - 1)).map fun k => moveTiming (walkMoves k)).toArray
  info := { title := "A walk meets a wall"
            description := "A path of the center graph at r = 2.13, x = 1/5, inside the \
              circular window, walked from the label 0 one step at a time, a circle marking \
              where the walk is and each label drawn as it is reached (dots for weight zero, \
              squares for weight one). It lowers n₂ from 0 to −4 and crosses the good level −5 \
              into the label n at the window's edge; the other candidates of n appear outside \
              the window, and the walk steps back to n + e₂." }
  checks := .fail
  width := figureWidth

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

-- The path is a path of the center graph at `r = 2.13`, `x = 1/5`: consecutive labels differ by
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

end TDCSGFigures.Confinement
