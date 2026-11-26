/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2, Claude Opus 5.5
-/
import PILean.Trust.Attr
import TDCSGFigures.Data.Early
import TDCSGFigures.Data.Moves
import TDCSGFigures.Style

/-!
# The figures of chapter 1, compound symmetry

* `extensionJump`: an animation of a turn of one closed disk `B`, extended by the identity. A bar
  from `8` to `12` crosses the boundary circle of `B` (radius `10` about `0`); the turn carries
  the part in `B` with the point `p = 9` a fifth of a turn clockwise and leaves the part outside
  with the point `q = 11` where it is: the bar is torn at the circle, so the extension is not
  continuous, and the group it generates lives among the permutations of the plane, not its
  isometries. Its last key frame is the figure of the jump (`extensionJumpFinal`), which keeps its
  linked theorem.
* `disjointDisks`: an animation of two disjoint closed disks, each turned by its own generator, in
  two panels on one clock: `a` then `b` beside `b` then `a`. Both end in the same picture, the
  figure of the two turns (`disjointDisksFinal`), which keeps its linked theorem: the two turns
  move disjoint sets of points and commute, and the group is the product of the two cyclic groups.

Every point is exact in `ℤ[ζ₅]`, every radius rational, every incidence the figures record is
decided exactly in `ℚ(√5)`, and every declared turn is checked exactly (`jumpArrives`,
`disjointArrives`). The statements are `extensionJump_spec`, `extensionJump_keys`,
`disjointDisks_spec` and `disjointDisks_keys`.
-/

namespace TDCSGFigures

open PILean PILean.Plane PILean.Exact TDCSGFigures.Early

/-! ### One disk turned, the identity outside -/

/-- The disk `B`. -/
def jumpDisk : Item :=
  Plane.Exact.disk origin ballRadius |>.noFill |>.role leftRole |>.named "the disk B"
    |>.describedBy "the closed disk of radius 10 about c = 0" |>.declRef `TDCSG.ballPerm

/-- The arc of the turn of `p` (actor `"arc"`). -/
def jumpArc : Item :=
  Plane.Exact.arc origin (9 : Rat) 0 (-deg 72) |>.withArrow |>.role leftRole |>.width 1.5
    |>.named "the turn of p through 72° clockwise about c"
    |>.declRef `TDCSG.ballPerm_apply_of_mem |>.withId "arc"

/-- The drawn radius of `B` and its label. -/
def jumpRadius : Array Item := #[
  Plane.Exact.segment origin ballSpoke |>.role leftRole |>.width 1.5 |>.dashed
    |>.named "a radius of B, length 10",
  Plane.Exact.labelBeside "radius 10" origin ballSpoke |>.role leftRole]

/-- The angle of the turn (actor `"angle"`). -/
def jumpAngle : Item :=
  Plane.Exact.angleMark origin 0 (-deg 72) (some 30) |>.role leftRole
    |>.named "the angle of the turn, 72° clockwise" |>.withId "angle"

/-- The segment from `p` to `q` (actor `"gap"`). -/
def jumpGap : Item :=
  Plane.Exact.segment nearInside nearOutside |>.faint |>.dashed |>.named "p to q, length 2"
    |>.withId "gap"

/-- The segment from `ĥ(p)` to `ĥ(q) = q` (actor `"image-gap"`). -/
def jumpImageGap : Item :=
  Plane.Exact.segment nearInsideImage nearOutside |>.faint |>.dashed
    |>.named "ĥ(p) to ĥ(q), length about 11.9" |>.withId "image-gap"

/-- The label of the length of the segment from `p` to `q` (actor `"gap-label"`). -/
def jumpGapLabel : Item := Plane.label "2" ⟨21 / 2, 0⟩ .above |>.withId "gap-label"

/-- The label of the length from `ĥ(p)` to `q` (actor `"image-gap-label"`). -/
def jumpImageGapLabel : Item :=
  Plane.label "≈ 11.9" ((PlanePoint.toPoint nearInsideImage).lerp
    (PlanePoint.toPoint nearOutside) 0.62) (.toward (deg 136)) (some 4) |>.withId "image-gap-label"

/-- The centre `c`. -/
def jumpCentre : Item := Plane.Exact.point origin |>.role leftRole |>.named "the center c"

/-- The point `p` (actor `"p"`). -/
def jumpP : Item :=
  Plane.Exact.point nearInside |>.role leftRole |>.named "p" |>.incident .inside "the disk B"
    |>.declRef `TDCSG.ballPerm_apply_of_mem |>.withId "p"

/-- The point `q` (actor `"q"`). -/
def jumpQ : Item :=
  Plane.Exact.point nearOutside |>.named "q = ĥ(q)" |>.incident .outside "the disk B"
    |>.declRef `TDCSG.ballPerm_apply_of_notMem |>.withId "q"

/-- The point `ĥ(p)` (actor `"image"`). -/
def jumpImage : Item :=
  Plane.Exact.point nearInsideImage |>.role leftRole |>.named "ĥ(p)"
    |>.incident .inside "the disk B" |>.withId "image"

/-- The label of `c`. -/
def jumpCentreLabel : Item := Plane.Exact.label "c" origin .auto |>.role leftRole

/-- The label of `p` (actor `"p-label"`). -/
def jumpPLabel : Item :=
  Plane.Exact.label "p" nearInside .above |>.role leftRole |>.withId "p-label"

/-- The labels of `p` and `q`, the image of `p` and the angle (actors `"p-label"`, `"q-label"`,
`"image-label"`, `"angle-label"`). -/
def jumpLabels : Array Item := #[
  jumpPLabel,
  Plane.Exact.label "q, fixed" nearOutside .belowRight |>.withId "q-label",
  Plane.Exact.label "image of p" nearInsideImage .auto |>.role leftRole |>.withId "image-label",
  Plane.Exact.label "72°" origin (.toward (-deg 36)) (some 42) |>.role leftRole
    |>.withId "angle-label"]

/-- The name of `B`. -/
def jumpName : Item := Plane.Exact.label "disk B" ((-6 : Rat), (-5 : Rat)) |>.role leftRole

/-- The figure of the jump, the last key frame of `extensionJump`: a closed disk B of radius 10
about c = 0, turned through 72° clockwise and extended by the identity: the point p = 9 just
inside B moves to ĥ(p) = 9ζ⁴, the point q = 11 just outside stays where it is. Two points 2 apart
end up about 11.9 apart. -/
def extensionJumpFinal : Plane.Figure where
  width := figureWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := #[jumpDisk, jumpArc] ++ jumpRadius ++ #[jumpAngle, jumpGap, jumpImageGap, jumpGapLabel,
    jumpImageGapLabel, jumpCentre, jumpP, jumpQ, jumpImage, jumpCentreLabel] ++ jumpLabels ++
    #[jumpName]
  info := { title := "A turn of one disk, extended by the identity, is not continuous" }

/-- The ends of the bar and the point where it crosses the boundary circle: `8`, `10`, `12`. -/
def barInner : Zeta5 := Zeta5.ofInt 8

/-- The point of the bar on the boundary circle of `B`, `10`. -/
def barCut : Zeta5 := Zeta5.ofInt 10

/-- The outer end of the bar, `12`. -/
def barOuter : Zeta5 := Zeta5.ofInt 12

/-- The part of the bar in `B` with `p` (actor `"inner"`), turned by the factor `τ`
about `0` (`τ = 1` before the turn, `ζ⁴` after). -/
def jumpInner (τ : Zeta5) : Item :=
  (group #[Plane.Exact.segment (barInner * τ) (barCut * τ) |>.role leftRole |>.width 4
        |>.named "the part of the bar in B, from 8 to 10",
      Plane.Exact.point (nearInside * τ) |>.role leftRole |>.incident .inside "the disk B"
        |>.incident .on "the part of the bar in B, from 8 to 10"])
    |>.named "the part of the bar in B and the point p, turned by ĥ" |>.withId "inner"

/-- The part of the bar outside `B` with `q` and its label (actor `"outer"`), which stays. -/
def jumpOuter : Item :=
  (group #[Plane.Exact.segment barCut barOuter |>.width 4
        |>.named "the part of the bar outside B, from 10 to 12",
      Plane.Exact.point nearOutside |>.incident .outside "the disk B"
        |>.incident .on "the part of the bar outside B, from 10 to 12",
      Plane.Exact.label "q, fixed" nearOutside .belowRight])
    |>.named "the part of the bar outside B and the point q, fixed by ĥ" |>.withId "outer"

/-- The items of key `k` of `extensionJump`, `k ≤ 1`: the disk, its radius, the bar before
(`k = 0`, with the segment from `p` to `q`, its length and the label of `p`) or after the turn, the
centre and the names. -/
def jumpKeyItems (k : Nat) : Array Item :=
  #[jumpDisk] ++ jumpRadius ++ (if k == 0 then #[jumpGap, jumpGapLabel] else #[]) ++
    #[jumpCentre, jumpInner (if k == 0 then Zeta5.ofInt 1 else zeta 4), jumpOuter,
      jumpCentreLabel] ++ (if k == 0 then #[jumpPLabel] else #[]) ++ #[jumpName]

/-- The captions of the keys of `extensionJump`. -/
def jumpCaptions : Array String := #[
  "A closed disk B of radius 10 about c = 0, to be turned through 72° clockwise and extended by \
    the identity. A bar from 8 to 12 crosses the boundary circle at 10: p = 9 lies inside B, \
    q = 11 outside, 2 apart.",
  "The extension ĥ turns the part of the bar in B, its point 10 on the circle included, about c \
    and fixes the part outside: the bar is torn at the circle. p went to ĥ(p) = 9ζ⁴, q stayed.",
  "p and q were 2 apart; ĥ(p) and ĥ(q) = q are about 11.9 apart. However close to the circle p \
    and q are taken, the jump stays, so ĥ is not continuous and is no isometry of the plane."]

/-- Key `k` of `extensionJump`, `k ≤ 1`: the items `jumpKeyItems k` in the frame of
`extensionJumpFinal`. -/
def jumpKey (k : Nat) : Plane.Figure :=
  { extensionJumpFinal with items := jumpKeyItems k, info := { title := jumpCaptions.getD k "" } }

/-- The turn of `B`: about `0`, by `-1/5` of a full turn (clockwise). -/
def jumpTurn : ExactTurn := ⟨ZetaFrac.ofZeta origin, -1 / 5⟩

/-- The declared moves of the steps of `extensionJump`: the part of the bar in `B` turns while the
segment from `p` to `q` and its length fade; then the bar vanishes while the marks of the
figure of the jump appear. -/
def jumpMoves : Nat → List (String × ExactMove ZetaFrac)
  | 0 => [("inner", .turn jumpTurn), ("gap", .vanish), ("gap-label", .vanish),
      ("p-label", .vanish)]
  | _ => [("inner", .vanish), ("outer", .vanish), ("arc", .appear), ("angle", .appear),
      ("gap", .appear), ("image-gap", .appear), ("gap-label", .appear),
      ("image-gap-label", .appear), ("p", .appear), ("q", .appear), ("image", .appear),
      ("p-label", .appear), ("q-label", .appear), ("image-label", .appear),
      ("angle-label", .appear)]

/-- The exact anchors of the actors of key `k` of `extensionJump`: at keys `0` and `1` the part of
the bar in `B` (its ends and `p`), turned by `ζ⁴` at key `1`, and the part outside (its ends, `q`
and its label); at key `0` the segment from `p` to `q`, the point of its length and the label of
`p`; at key `2` the marks of the figure of the jump, the labels of the lengths
(placed in floating point) without anchors. -/
def jumpActors (k : Nat) : List (ExactActor ZetaFrac) :=
  let z := ZetaFrac.ofZeta
  let τ := if k == 0 then Zeta5.ofInt 1 else zeta 4
  if k ≤ 1 then
    [⟨"inner", [z (barInner * τ), z (barCut * τ), z (nearInside * τ)]⟩,
      ⟨"outer", [z barCut, z barOuter, z nearOutside, z nearOutside]⟩] ++
    (if k == 0 then [⟨"gap", [z nearInside, z nearOutside]⟩, ⟨"gap-label", []⟩,
      ⟨"p-label", [z nearInside]⟩] else [])
  else
    [⟨"arc", [z nearInside, z nearInsideImage]⟩, ⟨"angle", [z origin]⟩,
      ⟨"gap", [z nearInside, z nearOutside]⟩, ⟨"image-gap", [z nearInsideImage, z nearOutside]⟩,
      ⟨"gap-label", []⟩, ⟨"image-gap-label", []⟩, ⟨"p", [z nearInside]⟩, ⟨"q", [z nearOutside]⟩,
      ⟨"image", [z nearInsideImage]⟩, ⟨"p-label", [z nearInside]⟩,
      ⟨"q-label", [z nearOutside]⟩, ⟨"image-label", [z nearInsideImage]⟩,
      ⟨"angle-label", [z origin]⟩]

/-- Whether every declared move of `extensionJump` carries the actors of one key onto those of the
next, exactly in `ℚ(ζ₅)`. -/
def jumpArrives : Bool := allArrive 2 jumpMoves jumpActors

/-- A closed disk B of radius 10 about c = 0, turned through 72° clockwise and extended by the
identity: a bar across its boundary circle is torn, its part in B, with p = 9, turned to ĥ(p) =
9ζ⁴, its part outside, with q = 11, fixed; two points 2 apart end up about 11.9 apart. The last
key frame is the figure of the jump, `extensionJumpFinal`. -/
@[figure]
def extensionJump : MotionPanels where
  panels := #[{ motion := { keys := #[jumpKey 0, jumpKey 1, extensionJumpFinal],
                            steps := ((List.range 2).map (exactStep ∘ jumpMoves)).toArray } }]
  captions := jumpCaptions
  pacing := motionPacing
  timing := ((List.range 2).map fun k => moveTiming (jumpMoves k)).toArray
  info := { title := "A turn of one disk, extended by the identity, is not continuous"
            description := "A closed disk B of radius 10 about c = 0 and a bar from 8 to 12 \
              across its boundary circle, with p = 9 inside B and q = 11 outside, 2 apart. The \
              turn of B through 72° clockwise, extended by the identity, carries the part of the \
              bar in B about c and leaves the part outside where it is: the bar is torn at the \
              circle. Then p and its image ĥ(p) = 9ζ⁴ are shown with q = ĥ(q), about 11.9 from \
              ĥ(p)." }
  checks := .fail
  poster := 2
  width := figureWidth
  narrowWidth := some narrowWidth

/-! ### Two disjoint disks -/

/-- The disks `B₁` and `B₂` and the gap between them. -/
def disjointBase : Array Item := #[
  Plane.Exact.disk leftCentre disjointLeft |>.noFill |>.role leftRole |>.named "the disk B₁"
    |>.describedBy "the closed disk of radius 4/5 about −1",
  Plane.Exact.disk rightCentre disjointRight |>.noFill |>.role rightRole |>.named "the disk B₂"
    |>.describedBy "the closed disk of radius 7/10 about 1",
  Plane.Exact.segment ((-1 / 5 : Rat), (0 : Rat)) ((3 / 10 : Rat), (0 : Rat)) |>.faint |>.dashed
    |>.named "the gap between B₁ and B₂, of length 1/2"
    |>.declRef `TDCSG.leftDisk_disjoint_rightDisk,
  Plane.label "gap" ⟨1 / 20, 0⟩ .below]

/-- The arcs of the two turns (actors `"arc-a"`, `"arc-b"`). -/
def disjointArcs : Array Item := #[
  Plane.Exact.arc leftCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role leftRole
    |>.width 1.5 |>.named "the turn a of B₁, 72° clockwise about −1" |>.declRef `TDCSG.genA
    |>.withId "arc-a",
  Plane.Exact.arc rightCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role rightRole
    |>.width 1.5 |>.named "the turn b of B₂, 72° clockwise about 1" |>.declRef `TDCSG.genB
    |>.withId "arc-b"]

/-- The centres. -/
def disjointCentres : Array Item := #[
  Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1"]

/-- `x`, `a(x)`, `y` and `b(y)` (actors `"x"`, `"ax"`, `"y"`, `"by"`). -/
def disjointPoints : Array Item := #[
  Plane.Exact.point leftSample |>.role leftRole |>.named "x" |>.incident .inside "the disk B₁"
    |>.incident .outside "the disk B₂" |>.withId "x",
  Plane.Exact.point (leftCentre + phiInv * zeta 1) |>.role leftRole |>.named "a(x)"
    |>.incident .inside "the disk B₁" |>.withId "ax",
  Plane.Exact.point rightSample |>.role rightRole |>.named "y" |>.incident .inside "the disk B₂"
    |>.incident .outside "the disk B₁" |>.withId "y",
  Plane.Exact.point (rightCentre + phiInv * zeta 1) |>.role rightRole |>.named "b(y)"
    |>.incident .inside "the disk B₂" |>.withId "by"]

/-- The labels of the centres. -/
def disjointCentreLabels : Array Item := #[
  Plane.Exact.label "−1" leftCentre .below |>.role leftRole,
  Plane.Exact.label "+1" rightCentre .below |>.role rightRole]

/-- The labels of `x`, `a(x)`, `y`, `b(y)` (actors `"x-label"`, `"ax-label"`, `"y-label"`,
`"by-label"`). -/
def disjointPointLabels : Array Item := #[
  Plane.Exact.label "x" leftSample .auto |>.role leftRole |>.withId "x-label",
  Plane.Exact.label "a(x)" (leftCentre + phiInv * zeta 1) .auto |>.role leftRole
    |>.withId "ax-label",
  Plane.Exact.label "y" rightSample .auto |>.role rightRole |>.withId "y-label",
  Plane.Exact.label "b(y)" (rightCentre + phiInv * zeta 1) .auto |>.role rightRole
    |>.withId "by-label"]

/-- The names of the disks. -/
def disjointNames : Array Item := #[
  Plane.Exact.label "B₁, radius 4/5" ((-1 : Rat), (-1 : Rat)) |>.role leftRole
    |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two,
  Plane.Exact.label "B₂, radius 7/10" ((1 : Rat), (-1 : Rat)) |>.role rightRole
    |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two]

/-- The figure of the two turns, the last key frame of both panels of `disjointDisks`: two
disjoint closed disks, B₁ of radius 4/5 about −1 and B₂ of radius 7/10 about 1, each turned
through 72° clockwise by its own generator: a turns x in B₁ and fixes everything outside B₁, b
turns y in B₂ and fixes everything outside B₂. -/
def disjointDisksFinal : Plane.Figure where
  width := figureWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := disjointBase ++ disjointArcs ++ disjointCentres ++ disjointPoints ++
    disjointCentreLabels ++ disjointPointLabels ++ disjointNames
  info := { title := "Two disjoint disks, each turned by its own generator" }

/-- The point of `B₁` that `a` turns, with its label (actor `"x-moving"`), at `w`. -/
def disjointMoverX (w : Zeta5) : Item :=
  (group #[Plane.Exact.point w |>.role leftRole |>.incident .inside "the disk B₁"
        |>.incident .outside "the disk B₂",
      Plane.Exact.label "x" w (.toward (-deg 72)) |>.role leftRole])
    |>.named "the point x of B₁, turned by a" |>.withId "x-moving"

/-- The point of `B₂` that `b` turns, with its label (actor `"y-moving"`), at `w`. -/
def disjointMoverY (w : Zeta5) : Item :=
  (group #[Plane.Exact.point w |>.role rightRole |>.incident .inside "the disk B₂"
        |>.incident .outside "the disk B₁",
      Plane.Exact.label "y" w (.toward (-deg 72)) |>.role rightRole])
    |>.named "the point y of B₂, turned by b" |>.withId "y-moving"

/-- Whether `x` has been turned at key `k` of the panel `aFirst` (`a` then `b`) or of the other
(`b` then `a`): after step `0` in the first, after step `1` in the second. -/
def disjointXTurned (aFirst : Bool) (k : Nat) : Bool := if aFirst then 1 ≤ k else 2 ≤ k

/-- Whether `y` has been turned at key `k`: after step `1` in the panel `aFirst`, after step `0`
in the other. -/
def disjointYTurned (aFirst : Bool) (k : Nat) : Bool := if aFirst then 2 ≤ k else 1 ≤ k

/-- `x` at key `k` of a panel: `x` or `a(x) = -1 + φ⁻¹ ζ`. -/
def disjointX (aFirst : Bool) (k : Nat) : Zeta5 :=
  if disjointXTurned aFirst k then Letter.a.rotate leftSample else leftSample

/-- `y` at key `k` of a panel: `y` or `b(y) = 1 + φ⁻¹ ζ`. -/
def disjointY (aFirst : Bool) (k : Nat) : Zeta5 :=
  if disjointYTurned aFirst k then Letter.b.rotate rightSample else rightSample

/-- The items of key `k ≤ 2` of the panel `aFirst`: the disks, the gap, the centres, the two moving
points and the names. -/
def disjointKeyItems (aFirst : Bool) (k : Nat) : Array Item :=
  disjointBase ++ disjointCentres ++
    #[disjointMoverX (disjointX aFirst k), disjointMoverY (disjointY aFirst k)] ++
    disjointCentreLabels ++ disjointNames

/-- The captions of the keys of `disjointDisks`. -/
def disjointCaptions : Array String := #[
  "Two disjoint closed disks, B₁ of radius 4/5 about −1 and B₂ of radius 7/10 about 1, a point x \
    in B₁ and a point y in B₂. Left: a, then b. Right: b, then a.",
  "Left: a turns B₁ a fifth of a turn clockwise about −1, carrying x, and fixes y. Right: b turns \
    B₂ a fifth of a turn clockwise about +1, carrying y, and fixes x.",
  "Left: b turns y; right: a turns x. Both orders end in the same picture: the two turns move \
    disjoint sets of points, so they commute.",
  "The turn a of B₁ and the turn b of B₂, each through 72° clockwise: a moves x to a(x) and fixes \
    y, b moves y to b(y) and fixes x."]

/-- Key `k` of the panel `aFirst`: the items `disjointKeyItems aFirst k` in the frame of
`disjointDisksFinal` for `k ≤ 2`, the figure `disjointDisksFinal` for `k = 3`. -/
def disjointKey (aFirst : Bool) (k : Nat) : Plane.Figure :=
  if k == 3 then disjointDisksFinal
  else { disjointDisksFinal with items := disjointKeyItems aFirst k,
                                 info := { title := disjointCaptions.getD k "" } }

/-- The turn of `a`: about `-1` by `-1/5` of a full turn. -/
def disjointTurnA : ExactTurn := ⟨ZetaFrac.ofZeta leftCentre, -1 / 5⟩

/-- The turn of `b`: about `1` by `-1/5` of a full turn. -/
def disjointTurnB : ExactTurn := ⟨ZetaFrac.ofZeta rightCentre, -1 / 5⟩

/-- The declared moves of step `k` of the panel `aFirst`: in the panel `a` then `b`, `x` turns by
`a` and then `y` by `b`; in the other, `y` by `b` and then `x` by `a`; at the last step the
moving points vanish while the marks of the figure of the two turns appear. -/
def disjointMoves (aFirst : Bool) : Nat → List (String × ExactMove ZetaFrac)
  | 0 => if aFirst then [("x-moving", .turn disjointTurnA)] else [("y-moving", .turn disjointTurnB)]
  | 1 => if aFirst then [("y-moving", .turn disjointTurnB)] else [("x-moving", .turn disjointTurnA)]
  | _ => [("x-moving", .vanish), ("y-moving", .vanish), ("arc-a", .appear), ("arc-b", .appear),
      ("x", .appear), ("ax", .appear), ("y", .appear), ("by", .appear), ("x-label", .appear),
      ("ax-label", .appear), ("y-label", .appear), ("by-label", .appear)]

/-- The exact anchors of the actors of key `k` of the panel `aFirst`: up to key `2`, the moving
points (the point and its label); at key `3`, the marks of the figure of the two turns (the ends
of the arcs, the points and their labels). -/
def disjointActors (aFirst : Bool) (k : Nat) : List (ExactActor ZetaFrac) :=
  let z := ZetaFrac.ofZeta
  let ax := leftCentre + phiInv * zeta 1
  let byy := rightCentre + phiInv * zeta 1
  if k ≤ 2 then
    [⟨"x-moving", [z (disjointX aFirst k), z (disjointX aFirst k)]⟩,
      ⟨"y-moving", [z (disjointY aFirst k), z (disjointY aFirst k)]⟩]
  else
    [⟨"arc-a", [z leftSample, z ax]⟩, ⟨"arc-b", [z rightSample, z byy]⟩, ⟨"x", [z leftSample]⟩,
      ⟨"ax", [z ax]⟩, ⟨"y", [z rightSample]⟩, ⟨"by", [z byy]⟩, ⟨"x-label", [z leftSample]⟩,
      ⟨"ax-label", [z ax]⟩, ⟨"y-label", [z rightSample]⟩, ⟨"by-label", [z byy]⟩]

/-- Whether every declared move of both panels of `disjointDisks` carries the actors of one key
onto those of the next, exactly in `ℚ(ζ₅)`. -/
def disjointArrives : Bool :=
  allArrive 3 (disjointMoves true) (disjointActors true) &&
    allArrive 3 (disjointMoves false) (disjointActors false)

/-- The panel `aFirst` of `disjointDisks`: titled by its order, its keys `disjointKey aFirst k`
and its steps `disjointMoves aFirst k`. -/
def disjointPanel (aFirst : Bool) : MotionPanel :=
  { title := if aFirst then "a, then b" else "b, then a"
    motion :=
      { keys := ((List.range 4).map (disjointKey aFirst)).toArray,
        steps := ((List.range 3).map fun k => exactStep (disjointMoves aFirst k)).toArray } }

/-- Two disjoint closed disks, B₁ of radius 4/5 about −1 and B₂ of radius 7/10 about 1, each turned
through 72° clockwise by its own generator, in two panels on one clock: a then b on the left, b
then a on the right; both end in the same picture. The last key frame of both panels is the
figure of the two turns, `disjointDisksFinal`. -/
@[figure]
def disjointDisks : MotionPanels where
  panels := #[disjointPanel true, disjointPanel false]
  captions := disjointCaptions
  pacing := motionPacing
  timing := ((List.range 3).map fun k => moveTiming (disjointMoves true k)).toArray
  info := { title := "Two disjoint disks, each turned by its own generator"
            description := "Two panels on one clock, each with the disjoint closed disks B₁ of \
              radius 4/5 about −1 and B₂ of radius 7/10 about 1, a point x in B₁ and a point y \
              in B₂. Left: a turns x a fifth of a turn clockwise about −1, then b turns y about \
              +1. Right: b first, then a. Both panels end in the same picture, with the arcs of \
              the two turns." }
  checks := .fail
  poster := 3
  width := figureWidth
  narrowWidth := some narrowWidth

end TDCSGFigures
