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
* `disjointDisks`: an animation of two disjoint closed disks, each turned by its own generator:
  copies of the two disks at two fifths of the size, `a` then `b` beside `b` then `a`, on one clock.
  Both end in the same picture, which gives way to the figure of the two turns at full size
  (`disjointDisksFinal`), the last key frame, which keeps its linked theorem: the two turns move
  disjoint sets of points and commute, and the group is the product of the two cyclic groups.

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

/-- The anchors of the part of the bar in `B`, turned by the factor `τ` about `0` (`τ = 1` before
the turn, `ζ⁴` after): its ends `8τ`, `10τ` and `p τ = 9τ`. The drawing (`jumpInner`) and the
exact arrival check read these same points. -/
def jumpInnerAnchors (τ : Zeta5) : List ZetaFrac :=
  [barInner * τ, barCut * τ, nearInside * τ].map ZetaFrac.ofZeta

/-- The part of the bar in `B` with `p` (actor `"inner"`), drawn at `jumpInnerAnchors τ`. -/
def jumpInner (τ : Zeta5) : Item :=
  let a := fun (i : Nat) => (jumpInnerAnchors τ).getD i (ZetaFrac.ofZeta origin)
  (group #[Plane.Exact.segment (a 0) (a 1) |>.role leftRole |>.width 4
        |>.named "the part of the bar in B, from 8 to 10",
      Plane.Exact.point (a 2) |>.role leftRole |>.incident .inside "the disk B"
        |>.incident .on "the part of the bar in B, from 8 to 10"])
    |>.named "the part of the bar in B and the point p, turned by ĥ" |>.withId "inner"

/-- The anchors of the part of the bar outside `B`: its ends `10` and `12`, `q = 11` and the point
of its label. -/
def jumpOuterAnchors : List ZetaFrac :=
  [barCut, barOuter, nearOutside, nearOutside].map ZetaFrac.ofZeta

/-- The part of the bar outside `B` with `q` and its label (actor `"outer"`), which stays, drawn at
`jumpOuterAnchors`. -/
def jumpOuter : Item :=
  let a := fun (i : Nat) => jumpOuterAnchors.getD i (ZetaFrac.ofZeta origin)
  (group #[Plane.Exact.segment (a 0) (a 1) |>.width 4
        |>.named "the part of the bar outside B, from 10 to 12",
      Plane.Exact.point (a 2) |>.incident .outside "the disk B"
        |>.incident .on "the part of the bar outside B, from 10 to 12",
      Plane.Exact.label "q, fixed" (a 3) .belowRight])
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
  "The extension turns the part of the bar in B, its point 10 on the circle included, about c and \
    fixes the part outside: the bar is torn at the circle. p went to its image 9ζ⁴, q stayed.",
  "p and q were 2 apart; their images, 9ζ⁴ and q itself, are about 11.9 apart. However close to \
    the circle p and q are taken, the jump stays, so the extension is not continuous and is no \
    isometry of the plane."]

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
    [⟨"inner", jumpInnerAnchors τ⟩, ⟨"outer", jumpOuterAnchors⟩] ++
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

/-- The disks `B₁` and `B₂` and the gap between them (actors `"B1"`, `"B2"`, `"gap"`,
`"gap-label"`). -/
def disjointBase : Array Item := #[
  Plane.Exact.disk leftCentre disjointLeft |>.noFill |>.role leftRole |>.named "the disk B₁"
    |>.describedBy "the closed disk of radius 4/5 about −1" |>.withId "B1",
  Plane.Exact.disk rightCentre disjointRight |>.noFill |>.role rightRole |>.named "the disk B₂"
    |>.describedBy "the closed disk of radius 7/10 about 1" |>.withId "B2",
  Plane.Exact.segment ((-1 / 5 : Rat), (0 : Rat)) ((3 / 10 : Rat), (0 : Rat)) |>.faint |>.dashed
    |>.named "the gap between B₁ and B₂, of length 1/2"
    |>.declRef `TDCSG.leftDisk_disjoint_rightDisk |>.withId "gap",
  Plane.label "gap" ⟨1 / 20, 0⟩ .below |>.withId "gap-label"]

/-- The arcs of the two turns (actors `"arc-a"`, `"arc-b"`). -/
def disjointArcs : Array Item := #[
  Plane.Exact.arc leftCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role leftRole
    |>.width 1.5 |>.named "the turn a of B₁, 72° clockwise about −1" |>.declRef `TDCSG.genA
    |>.withId "arc-a",
  Plane.Exact.arc rightCentre phiInvReal (deg 144) (deg 72) |>.withArrow |>.role rightRole
    |>.width 1.5 |>.named "the turn b of B₂, 72° clockwise about 1" |>.declRef `TDCSG.genB
    |>.withId "arc-b"]

/-- The centres (actors `"centre-left"`, `"centre-right"`). -/
def disjointCentres : Array Item := #[
  Plane.Exact.point leftCentre |>.role leftRole |>.named "the center −1" |>.withId "centre-left",
  Plane.Exact.point rightCentre |>.role rightRole |>.named "the center 1"
    |>.withId "centre-right"]

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

/-- The labels of the centres (actors `"centre-label-left"`, `"centre-label-right"`). -/
def disjointCentreLabels : Array Item := #[
  Plane.Exact.label "−1" leftCentre .below |>.role leftRole |>.withId "centre-label-left",
  Plane.Exact.label "+1" rightCentre .below |>.role rightRole |>.withId "centre-label-right"]

/-- The labels of `x`, `a(x)`, `y`, `b(y)` (actors `"x-label"`, `"ax-label"`, `"y-label"`,
`"by-label"`). -/
def disjointPointLabels : Array Item := #[
  Plane.Exact.label "x" leftSample .auto |>.role leftRole |>.withId "x-label",
  Plane.Exact.label "a(x)" (leftCentre + phiInv * zeta 1) .auto |>.role leftRole
    |>.withId "ax-label",
  Plane.Exact.label "y" rightSample .auto |>.role rightRole |>.withId "y-label",
  Plane.Exact.label "b(y)" (rightCentre + phiInv * zeta 1) .auto |>.role rightRole
    |>.withId "by-label"]

/-- The names of the disks (actors `"name-B1"`, `"name-B2"`). -/
def disjointNames : Array Item := #[
  Plane.Exact.label "B₁, radius 4/5" ((-1 : Rat), (-1 : Rat)) |>.role leftRole
    |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two |>.withId "name-B1",
  Plane.Exact.label "B₂, radius 7/10" ((1 : Rat), (-1 : Rat)) |>.role rightRole
    |>.declRef `TDCSG.nonempty_mulEquiv_of_add_lt_two |>.withId "name-B2"]

/-- The figure of the two turns, the last key frame of `disjointDisks`: two disjoint closed disks,
B₁ of radius 4/5 about −1 and B₂ of radius 7/10 about 1, each turned through 72° clockwise by its
own generator: a turns x in B₁ and fixes everything outside B₁, b turns y in B₂ and fixes
everything outside B₂. -/
def disjointDisksFinal : Plane.Figure where
  width := figureWidth
  padding := 16
  style := houseStyle
  checks := .fail
  items := disjointBase ++ disjointArcs ++ disjointCentres ++ disjointPoints ++
    disjointCentreLabels ++ disjointPointLabels ++ disjointNames
  info := { title := "Two disjoint disks, each turned by its own generator" }

/-! The two orders side by side: each a copy of the two disks at two fifths of the size, the copy of
the order `a`, then `b` on the left and that of `b`, then `a` on the right, inside the frame of the
figure of the two turns. -/

/-- The shift of the copy of the order `aFirst`, in twentieths: `-19` (`-19/20`) for `a`, then
`b`, `19` for `b`, then `a`. -/
def disjointShift (aFirst : Bool) : Int := if aFirst then -19 else 19

/-- The point `p` in the copy of the order `aFirst`: `2p/5` moved by the shift,
`(8 p + s) / 20`. -/
def disjointHalf (aFirst : Bool) (p : Zeta5) : ZetaFrac :=
  ⟨Zeta5.ofInt 8 * p + Zeta5.ofInt (disjointShift aFirst), 20⟩

/-- The tag of the order `aFirst` in ids and titles. -/
def disjointTag (aFirst : Bool) : String := if aFirst then "ab" else "ba"

/-- The anchors of the copy of the disks of the order `aFirst`: the centres of the two disks and
the two centres as points. -/
def disjointSceneAnchors (aFirst : Bool) : List ZetaFrac :=
  [leftCentre, rightCentre, leftCentre, rightCentre].map (disjointHalf aFirst)

/-- The copy of the disks of the order `aFirst` (actor `"scene-ab"` or `"scene-ba"`), drawn at
`disjointSceneAnchors aFirst`: `B₁` of radius `8/25` and `B₂` of radius `7/25`, and their
centres. -/
def disjointScene (aFirst : Bool) : Item :=
  let a := fun (i : Nat) => (disjointSceneAnchors aFirst).getD i (ZetaFrac.ofZeta origin)
  let t := disjointTag aFirst
  (group #[Plane.Exact.disk (a 0) (8 / 25 : Rat) |>.noFill |>.role leftRole
        |>.named s!"the disk B₁, order {t}",
      Plane.Exact.disk (a 1) (7 / 25 : Rat) |>.noFill |>.role rightRole
        |>.named s!"the disk B₂, order {t}",
      Plane.Exact.point (a 2) |>.role leftRole, Plane.Exact.point (a 3) |>.role rightRole])
    |>.named s!"the two disks, {if aFirst then "a, then b" else "b, then a"}"
    |>.withId s!"scene-{t}"

/-- The title above the copy of the order `aFirst` (actor `"title-ab"` or `"title-ba"`). -/
def disjointTitle (aFirst : Bool) : Item :=
  Plane.Exact.label (if aFirst then "a, then b" else "b, then a")
    (((if aFirst then -97 / 100 else 93 / 100 : Rat)), (1 / 2 : Rat))
    |>.withId s!"title-{disjointTag aFirst}"

/-- Whether `x` has been turned at key `k` in the copy of the order `aFirst`: after step `0` for
`a`, then `b`, after step `1` for `b`, then `a`. -/
def disjointXTurned (aFirst : Bool) (k : Nat) : Bool := if aFirst then 1 ≤ k else 2 ≤ k

/-- Whether `y` has been turned at key `k` in the copy of the order `aFirst`. -/
def disjointYTurned (aFirst : Bool) (k : Nat) : Bool := if aFirst then 2 ≤ k else 1 ≤ k

/-- `x` at key `k` in the copy of the order `aFirst`: `x` or `a(x) = -1 + φ⁻¹ ζ`. -/
def disjointX (aFirst : Bool) (k : Nat) : Zeta5 :=
  if disjointXTurned aFirst k then Letter.a.rotate leftSample else leftSample

/-- `y` at key `k` in the copy of the order `aFirst`: `y` or `b(y) = 1 + φ⁻¹ ζ`. -/
def disjointY (aFirst : Bool) (k : Nat) : Zeta5 :=
  if disjointYTurned aFirst k then Letter.b.rotate rightSample else rightSample

/-- The anchors of the moving point `x` (`isX`) or `y` at key `k` in the copy of the order
`aFirst`: the point and its label. -/
def disjointMoverAnchors (aFirst isX : Bool) (k : Nat) : List ZetaFrac :=
  let p := disjointHalf aFirst (if isX then disjointX aFirst k else disjointY aFirst k)
  [p, p]

/-- The moving point `x` (`isX`) or `y` with its label in the copy of the order `aFirst` (actors
`"ab-x"`, `"ab-y"`, `"ba-x"`, `"ba-y"`), drawn at `disjointMoverAnchors aFirst isX k`. -/
def disjointMover (aFirst isX : Bool) (k : Nat) : Item :=
  let a := fun (i : Nat) => (disjointMoverAnchors aFirst isX k).getD i (ZetaFrac.ofZeta origin)
  let t := disjointTag aFirst
  let role := if isX then leftRole else rightRole
  (group #[Plane.Exact.point (a 0) |>.role role
        |>.incident .inside s!"the disk {if isX then "B₁" else "B₂"}, order {t}",
      Plane.Exact.label (if isX then "x" else "y") (a 1) (.toward (-deg 72)) |>.role role])
    |>.named s!"the point {if isX then "x" else "y"}, order {t}"
    |>.withId s!"{t}-{if isX then "x" else "y"}"

/-- The items of key `k ≤ 2` of `disjointDisks`: the two copies, their titles and their moving
points. -/
def disjointKeyItems (k : Nat) : Array Item :=
  #[true, false].flatMap fun b =>
    #[disjointScene b, disjointTitle b, disjointMover b true k, disjointMover b false k]

/-- The captions of the keys of `disjointDisks`. -/
def disjointCaptions : Array String := #[
  "Two disjoint closed disks, B₁ of radius 4/5 about −1 and B₂ of radius 7/10 about 1, with a \
    point x in B₁ and a point y in B₂, drawn twice at two fifths of the size: on the left a, \
    then b; on the right b, then a.",
  "Left: a turns B₁ a fifth of a turn clockwise about −1, carrying x, and fixes y. Right: b turns \
    B₂ a fifth of a turn clockwise about +1, carrying y, and fixes x.",
  "Left: b turns y; right: a turns x. Both orders end in the same picture: the two turns move \
    disjoint sets of points, so they commute.",
  "Both orders give this: the turn a of B₁ and the turn b of B₂, each through 72° clockwise; a \
    moves x to a(x) and fixes y, b moves y to b(y) and fixes x."]

/-- Key `k` of `disjointDisks`: the items `disjointKeyItems k` in the frame of `disjointDisksFinal`
for `k ≤ 2`. -/
def disjointKey (k : Nat) : Plane.Figure :=
  { disjointDisksFinal with
    items := disjointKeyItems k
    info := { title := disjointCaptions.getD k "" } }

/-- The keys of `disjointDisks`: three keys with the two orders side by side, then the figure of
the two turns, `disjointDisksFinal`, at full size. -/
def disjointKeys : Array Plane.Figure :=
  #[disjointKey 0, disjointKey 1, disjointKey 2, disjointDisksFinal]

/-- The turn of `a` in the copy of the order `aFirst`: about the copy of `-1` by the fraction of
`a`, `-1/5`. -/
def disjointTurnA (aFirst : Bool) : ExactTurn := ⟨disjointHalf aFirst leftCentre, Letter.a.turns⟩

/-- The turn of `b` in the copy of the order `aFirst`: about the copy of `1` by the fraction of
`b`, `-1/5`. -/
def disjointTurnB (aFirst : Bool) : ExactTurn :=
  ⟨disjointHalf aFirst rightCentre, Letter.b.turns⟩

/-- The ids of the items of the figure of the two turns, which appear at the last step. -/
def disjointFinalIds : List String :=
  ["B1", "B2", "gap", "gap-label", "arc-a", "arc-b", "centre-left", "centre-right", "x", "ax",
    "y", "by", "centre-label-left", "centre-label-right", "x-label", "ax-label", "y-label",
    "by-label", "name-B1", "name-B2"]

/-- The declared moves of step `k` of `disjointDisks`: step `0` turns `x` by `a` in the copy of
`a`, then `b` and `y` by `b` in the other; step `1` the other point of each; step `2` fades the
copies out and the figure of the two turns in. -/
def disjointMoves : Nat → List (String × ExactMove ZetaFrac)
  | 0 => [("ab-x", .turn (disjointTurnA true)), ("ba-y", .turn (disjointTurnB false))]
  | 1 => [("ab-y", .turn (disjointTurnB true)), ("ba-x", .turn (disjointTurnA false))]
  | _ => (["scene-ab", "title-ab", "ab-x", "ab-y", "scene-ba", "title-ba", "ba-x", "ba-y"].map
      (·, .vanish)) ++ disjointFinalIds.map (·, .appear)

/-- The exact anchors of the actors of key `k` of `disjointDisks`: up to key `2`, the copies of the
disks (`disjointSceneAnchors`), their titles (placed by rationals, without exact anchors) and the
moving points (`disjointMoverAnchors`), the points the key draws; at key `3`, the items of the
figure of the two turns, which only appear, without anchors. -/
def disjointActors (k : Nat) : List (ExactActor ZetaFrac) :=
  if k ≤ 2 then
    [true, false].flatMap fun b =>
      let t := disjointTag b
      [⟨s!"scene-{t}", disjointSceneAnchors b⟩, ⟨s!"title-{t}", []⟩,
        ⟨s!"{t}-x", disjointMoverAnchors b true k⟩, ⟨s!"{t}-y", disjointMoverAnchors b false k⟩]
  else disjointFinalIds.map fun id => ⟨id, []⟩

/-- Whether every declared move of `disjointDisks` carries the actors of one key onto those of the
next, exactly in `ℚ(ζ₅)`. -/
def disjointArrives : Bool := allArrive 3 disjointMoves disjointActors

/-- Two disjoint closed disks, B₁ of radius 4/5 about −1 and B₂ of radius 7/10 about 1, each turned
through 72° clockwise by its own generator, in both orders side by side on one clock: a then b on
the left, b then a on the right; both end in the same picture, which gives way to the figure of
the two turns at full size, `disjointDisksFinal`, the last key frame. -/
@[figure]
def disjointDisks : MotionPanels where
  panels := #[{ motion := { keys := disjointKeys,
                            steps := ((List.range 3).map (exactStep ∘ disjointMoves)).toArray } }]
  captions := disjointCaptions
  pacing := motionPacing
  timing := ((List.range 3).map fun k => moveTiming (disjointMoves k)).toArray
  info := { title := "Two disjoint disks, each turned by its own generator"
            description := "The disjoint closed disks B₁ of radius 4/5 about −1 and B₂ of radius \
              7/10 about 1, with a point x in B₁ and a point y in B₂, drawn twice at two \
              fifths of the size. \
              On the left a turns x a fifth of a turn clockwise about −1, then b turns y about \
              +1; on the right b first, then a. Both copies end in the same picture, which gives \
              way to the figure of the two turns at full size." }
  checks := .fail
  poster := 3
  width := figureWidth
  narrowWidth := some narrowWidth

end TDCSGFigures
