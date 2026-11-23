/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import PILean.Svg
import PILean.Trust.Sha256

/-!
# Figures of the blueprint

Seven plates for the fivefold critical radius, written as SVG; the front page's figures are
drawn by PILean in `TDCSGFigures`. Every coordinate is computed in floating point from the
definitions it illustrates (the disks, the generators, the label projection, the good levels and
the chord words); floating point is used for illustration only.
Where a figure shows a particular instance (a component, a good level, a terminal crossing), the
instance is recomputed here and the build stops if it no longer has the property the caption
states.

All plates share one palette: the left disk, its centre `−1` and the weight-zero labels (the
left centres) are blue; the right disk, its centre `+1` and the weight-one labels are vermilion;
the window disk is grey. The two hues are the Okabe–Ito pair, which stays distinguishable under
the common colour-vision deficiencies.
-/

namespace TDCSGBlueprint.Figures

open PILean Svg

/-! ### Palette -/

/-- Text and main strokes. -/
private def ink := Rgba.rgb 31 42 51
/-- Secondary text, axes and rejected candidates. -/
private def muted := Rgba.rgb 96 108 116
/-- Faint guides. -/
private def faint := Rgba.rgb 172 182 188
/-- The left disk, its centre `−1` and the weight-zero labels (Okabe–Ito blue). -/
private def leftC := Rgba.rgb 0 114 178
/-- The right disk, its centre `+1` and the weight-one labels (Okabe–Ito vermilion). -/
private def rightC := Rgba.rgb 213 94 0
/-- The good phases of a level (Okabe–Ito bluish green). -/
private def goodC := Rgba.rgb 0 158 115
/-- The window disk of the centre graph. -/
private def windowC := Rgba.rgb 84 96 104
/-- The plate background; dark mode inverts it with the rest of the image. -/
private def paper := Rgba.rgb 251 250 246

/-- `c` with opacity `a` out of 255. -/
private def tint (c : Rgba) (a : UInt8) : Rgba := { c with a := a }

/-! ### Constants of the problem -/

/-- `π`. -/
private def pi : Float := 2 * Float.acos 0
/-- The golden ratio `φ = (1 + √5) / 2`. -/
private def phi : Float := (1 + Float.sqrt 5) / 2
/-- The critical radius `R = √(3 + φ)`. -/
private def critical : Float := Float.sqrt (3 + phi)
/-- The period `L = φ − 1/2` of the level phases. -/
private def period : Float := phi - 1 / 2
/-- The cut `κ = (1 + L) / 2 = (2φ + 1) / 4` of the lens estimate. -/
private def kappa : Float := (1 + period) / 2
/-- The margin `η = (3 + φ − r²) / 16` at radius `r`. -/
private def margin (r : Float) : Float := (3 + phi - r * r) / 16
/-- The phase step `α = 1 + φ/2` between consecutive levels. -/
private def slope : Float := 1 + phi / 2

/-! ### Complex arithmetic on points -/

/-- The product of two complex numbers written as points. -/
private def cmul (p q : Point) : Point := ⟨p.x * q.x - p.y * q.y, p.x * q.y + p.y * q.x⟩

/-- `exp(iθ)`. -/
private def cis (θ : Float) : Point := ⟨Float.cos θ, Float.sin θ⟩

/-- `ζʲ`, where `ζ = exp(2πi/5)`. -/
private def zpow (j : Nat) : Point := cis (2 * pi * j.toFloat / 5)

/-- The disk rotation about `c` of radius `r`, clockwise by `2π/5`, as in `TDCSG.diskRotation`. -/
private def diskRot (c : Point) (r : Float) (z : Point) : Point :=
  if (z - c).norm ≤ r then c + cmul (cis (-2 * pi / 5)) (z - c) else z

/-! ### Integer labels -/

/-- An integer label `n = (n₀, …, n₄)`, as `TDCSG.Five.Label`. -/
private abbrev Label := Array Int

/-- The projection `P(n) = ∑ⱼ nⱼ ζʲ`. -/
private def proj (n : Label) : Point :=
  (List.range 5).foldl (fun p j => p + (Float.ofInt n[j]!) * zpow j) ⟨0, 0⟩

/-- The weight `∑ⱼ nⱼ`. -/
private def weight (n : Label) : Int := n.foldl (· + ·) 0

/-- `n + k eⱼ`. -/
private def shift (n : Label) (j : Nat) (k : Int) : Label := n.modify j (· + k)

/-- `TDCSG.Five.InWindow`: `|P(n) − x| ≤ r/2`. -/
private def inWindow (r : Float) (x : Point) (n : Label) : Bool := (proj n - x).norm ≤ r / 2

/-- How far the phase `(1 + φ/2) m + 1/2 − Re(x ζ⁻ʲ)` of level `m` lies beyond `L/2 − η` from
`L ℤ`; the level is good (`TDCSG.Five.IsGoodLevel`) exactly when this is positive. -/
private def goodness (r : Float) (x : Point) (j : Nat) (m : Int) : Float :=
  let p := phaseOf x j m
  let red := p - period * Float.floor (p / period + 0.5)
  red.abs - (period / 2 - margin r)
where
  /-- The phase of level `m`. -/
  phaseOf (x : Point) (j : Nat) (m : Int) : Float :=
    slope * Float.ofInt m + 1 / 2 - (cmul x ⟨(zpow j).x, -(zpow j).y⟩).x

/-- The phase of level `m` reduced to `[−L/2, L/2)`. -/
private def reducedPhase (x : Point) (j : Nat) (m : Int) : Float :=
  let p := goodness.phaseOf x j m
  p - period * Float.floor (p / period + 0.5)

/-! ### Drawing primitives -/

/-- The width of every plate in SVG user units. At the narrowest rendering (a 360 px screen) a
plate is about 330 px wide, so a font size of 18 user units renders at about 12 px. -/
private def width : Float := 480

/-- A map from the mathematical plane (`y` up) to the plate (`y` down). -/
private structure Frame where
  /-- Where the mathematical origin lands. -/
  origin : Point
  /-- Plate units per mathematical unit. -/
  scale : Float

/-- The plate position of a mathematical point. -/
private def Frame.at (f : Frame) (p : Point) : Point :=
  ⟨f.origin.x + f.scale * p.x, f.origin.y - f.scale * p.y⟩

/-- A run of label text: prose (sans serif, upright) or mathematics (serif), possibly italic,
on the baseline (`0`), lowered as a subscript (`-1`) or raised as a superscript (`1`). -/
private structure Run where
  /-- The text. -/
  s : String
  /-- Whether the run is mathematics. -/
  math : Bool := false
  /-- Whether the run is italic. -/
  italic : Bool := false
  /-- The vertical position. -/
  level : Int := 0

/-- Prose label text. -/
private def txt (s : String) : Array Run := #[{ s }]

/-- Whether a character is set in italic in mathematics: Latin and lowercase Greek letters. -/
private def italicChar (c : Char) : Bool :=
  c.isAlpha || (0x3B1 ≤ c.val && c.val ≤ 0x3C9)

/-- Mathematical label text with TeX conventions: letters italic, everything else upright;
`_c` or `_{…}` is a subscript and `^c` or `^{…}` a superscript. -/
private def math (s : String) : Array Run := Id.run do
  let mut out : Array Run := #[]
  let mut cs := s.toList
  let push := fun (out : Array Run) (c : Char) (lvl : Int) =>
    let it := italicChar c
    match out.back? with
    | some r => if r.italic == it && r.level == lvl then out.pop.push { r with s := r.s.push c }
                else out.push { s := c.toString, math := true, italic := it, level := lvl }
    | none => out.push { s := c.toString, math := true, italic := it, level := lvl }
  while true do
    match cs with
    | [] => break
    | c :: rest =>
      if c == '_' || c == '^' then
        let lvl : Int := if c == '_' then -1 else 1
        match rest with
        | '{' :: body =>
          let inner := body.takeWhile (· ≠ '}')
          for d in inner do out := push out d lvl
          cs := (body.dropWhile (· ≠ '}')).drop 1
        | d :: rest' => out := push out d lvl; cs := rest'
        | [] => cs := []
      else
        out := push out c 0
        cs := rest
  return out

/-- Upright mathematical text, such as an operator name. -/
private def mathUp (s : String) : Array Run := #[{ s, math := true }]

/-- A decimal with at most `d` decimals, trailing zeros dropped, with a true minus sign. -/
private def dec (x : Float) (d : Nat := 3) : String :=
  let s := fmtNum x d
  if s.startsWith "-" then "−" ++ (s.drop 1).toString else s

/-- Sans-serif font stack for prose labels. -/
private def sans := "system-ui, -apple-system, 'Segoe UI', Roboto, 'Helvetica Neue', sans-serif"
/-- Serif font stack for mathematics. -/
private def serif := "'STIX Two Text', 'STIX Two Math', 'Cambria Math', Cambria, 'Times New Roman', serif"

/-- A label with baseline at plate position `p`. Text is haloed in the background colour so
that it stays legible where it meets a line. -/
private def label (p : Point) (runs : Array Run) (c : Rgba := ink) (anchor : Anchor := .middle)
    (size : Float := 19) (extra : Array (String × String) := #[]) : Node := Id.run do
  let mut kids : Array Node := #[.text ""]
  let mut off : Float := 0
  for r in runs do
    let target := if r.level < 0 then 0.3 * size else if r.level > 0 then -0.42 * size else 0
    let mut attrs : Array (String × String) := #[]
    if target != off then attrs := attrs.push ("dy", fmtNum (target - off))
    off := target
    if r.math then attrs := attrs.push ("font-family", serif)
    if r.italic then attrs := attrs.push ("font-style", "italic")
    if r.level != 0 then attrs := attrs.push ("font-size", "72%")
    kids := kids.push (el "tspan" attrs #[.text r.s])
  return el "text" (#[("x", fmtNum p.x), ("y", fmtNum p.y), ("font-size", fmtNum size),
    ("font-family", sans), ("text-anchor", anchor.name)] ++ paint "fill" (some c) ++
    #[("stroke", rgbHex paper), ("stroke-width", "4"), ("stroke-linejoin", "round"),
      ("paint-order", "stroke")] ++ extra) kids

/-- A label offset by `(dx, dy)` plate units from the image of a mathematical point. -/
private def labelAt (f : Frame) (p : Point) (dx dy : Float) (runs : Array Run)
    (c : Rgba := ink) (anchor : Anchor := .middle) (size : Float := 19) : Node :=
  let q := f.at p
  label ⟨q.x + dx, q.y + dy⟩ runs c anchor size

/-- Dash attributes, empty for a solid stroke. -/
private def dashed (d : String) : Array (String × String) :=
  if d.isEmpty then #[] else #[("stroke-dasharray", d)]

/-- A circle of mathematical radius `r`. -/
private def circle (f : Frame) (c : Point) (r : Float) (stroke : Rgba) (fill : Option Rgba := none)
    (w : Float := 2) (dash := "") : Node :=
  Svg.path (Path.ellipse (f.at c) (r * f.scale) (r * f.scale)) fill stroke w (dashed dash)

/-- A filled dot. -/
private def dot (f : Frame) (p : Point) (c : Rgba := ink) (rad : Float := 4.5) : Node :=
  Svg.path (Path.ellipse (f.at p) rad rad) c (some paper) 1.5

/-- A hollow dot. -/
private def ring (f : Frame) (p : Point) (c : Rgba := muted) (rad : Float := 4.5) : Node :=
  Svg.path (Path.ellipse (f.at p) rad rad) paper c 2

/-- A small cross marking a point that is not a vertex (a window centre). -/
private def cross (f : Frame) (p : Point) (c : Rgba := ink) : Node :=
  let q := f.at p
  Svg.path ((Path.empty.moveTo ⟨q.x - 5, q.y - 5⟩).lineTo ⟨q.x + 5, q.y + 5⟩
    |>.moveTo ⟨q.x - 5, q.y + 5⟩ |>.lineTo ⟨q.x + 5, q.y - 5⟩) none c 2

/-- A segment between mathematical points. -/
private def seg (f : Frame) (a b : Point) (c : Rgba := ink) (w : Float := 2) (dash := "") : Node :=
  Svg.line (f.at a) (f.at b) c w (dashed dash)

/-- An open polyline through plate points. -/
private def poly (ps : Array Point) (c : Rgba) (w : Float := 2) (dash := "") : Node :=
  Svg.path (Path.polyline ps) none c w (dashed dash ++ #[("stroke-linejoin", "round")])

/-- A filled arrowhead with its tip at plate point `tip`, pointing along `dir`. -/
private def arrowHead (tip dir : Point) (c : Rgba) (size : Float := 11) : Node :=
  let u := (1 / dir.norm) * dir
  let n : Point := ⟨-u.y, u.x⟩
  let base := tip - size * u
  Svg.path ((((Path.empty.moveTo tip).lineTo (base + (0.42 * size) * n)).lineTo
    (base - (0.42 * size) * n)).close) c none

/-- An arrow between plate points. -/
private def arrow (a b : Point) (c : Rgba) (w : Float := 2) (dash := "") : Array Node :=
  let d := b - a
  #[Svg.line a (b - (8 / d.norm) * d) c w (dashed dash), arrowHead b d c]

/-- Plate points along the circle of mathematical centre `c` and radius `r` from angle `θ₀` to
`θ₁` (radians, counterclockwise positive). -/
private def arcPts (f : Frame) (c : Point) (r θ₀ θ₁ : Float) (steps : Nat := 48) : Array Point :=
  (Array.range (steps + 1)).map fun i =>
    f.at (c + r * cis (θ₀ + (θ₁ - θ₀) * i.toFloat / steps.toFloat))

/-- An arc ending in an arrowhead. -/
private def arcArrow (f : Frame) (c : Point) (r θ₀ θ₁ : Float) (col : Rgba) (w : Float := 2)
    (dash := "") : Array Node :=
  let ps := arcPts f c r θ₀ θ₁
  let tip := ps.back!
  let d := tip - ps[ps.size - 3]!
  #[poly (ps.pop.pop) col w dash, Svg.line ps[ps.size - 3]! (tip - (6 / d.norm) * d) col w,
    arrowHead tip d col]

/-- A horizontal axis at plate height `y` from `x₀` to `x₁`, with ticks at plate abscissae and
their labels, and an axis title centred below. -/
private def xAxis (y x₀ x₁ : Float) (ticks : Array (Float × Array Run)) (title : Array Run) :
    Array Node := Id.run do
  let mut xs := #[Svg.line ⟨x₀, y⟩ ⟨x₁, y⟩ muted 1.5]
  for (x, s) in ticks do
    xs := xs ++ #[Svg.line ⟨x, y⟩ ⟨x, y + 6⟩ muted 1.5, label ⟨x, y + 25⟩ s muted (size := 18)]
  return xs.push (label ⟨(x₀ + x₁) / 2, y + 52⟩ title)

/-- A vertical axis at plate abscissa `x` from `y₀` to `y₁`, with ticks and labels on its left
and a rotated title further left. -/
private def yAxis (x y₀ y₁ : Float) (ticks : Array (Float × Array Run)) (title : Array Run) :
    Array Node := Id.run do
  let mut xs := #[Svg.line ⟨x, y₀⟩ ⟨x, y₁⟩ muted 1.5]
  for (y, s) in ticks do
    xs := xs ++ #[Svg.line ⟨x - 6, y⟩ ⟨x, y⟩ muted 1.5, label ⟨x - 9, y + 6⟩ s muted .finish 18]
  let mid := (y₀ + y₁) / 2
  return xs.push (label ⟨22, mid⟩ title ink .middle 19
    #[("transform", s!"rotate(-90 22 {fmtNum mid})")])

/-- Legend rows starting at plate point `(x, y)`, one row every 25 units: a swatch drawn at the
row's swatch centre, then its text. -/
private def legend (x y : Float) (rows : Array ((Point → Array Node) × Array Run)) :
    Array Node := Id.run do
  let mut xs := #[]
  let mut yy := y
  for (sw, s) in rows do
    xs := xs ++ sw ⟨x, yy - 6⟩ |>.push (label ⟨x + 18, yy⟩ s ink .start 18)
    yy := yy + 25
  return xs

/-- A legend swatch: a filled dot. -/
private def swDot (c : Rgba) (p : Point) : Array Node :=
  #[Svg.path (Path.ellipse p 5 5) c (some paper) 1.5]

/-- A legend swatch: a hollow dot. -/
private def swRing (c : Rgba) (p : Point) : Array Node :=
  #[Svg.path (Path.ellipse p 5 5) paper c 2]

/-- A legend swatch: a short line. -/
private def swLine (c : Rgba) (dash := "") (p : Point) : Array Node :=
  #[Svg.line ⟨p.x - 8, p.y⟩ ⟨p.x + 8, p.y⟩ c 2.5 (dashed dash)]

/-- A whole plate: a title and a description for assistive technology, the background, and the
drawing; or an error naming the first property of the drawn instance that fails. -/
private def plate (title desc : String) (h : Float) (checks : Array (String × Bool))
    (xs : Array Node) : Except String String :=
  match checks.find? (!·.2) with
  | some (what, _) => .error s!"figure check failed: {what}"
  | none => .ok <| Svg.document width h (#[el "title" #[] #[.text title],
      el "desc" #[] #[.text desc], Svg.rect 0 0 width h (some paper) #[("rx", "8")]] ++ xs)


/-! ### Figure 3: one generator step -/

/-- The disks of radius `1.5` about `∓1`, the origin and its image `a(0)` under the left
generator, a clockwise turn by `72°` about `−1`. -/
private def disks : Except String String := Id.run do
  let mut checks : Array (String × Bool) := #[]
  let f : Frame := ⟨⟨240, 152⟩, 80⟩
  let rad := 1.5
  let l : Point := ⟨-1, 0⟩
  let r : Point := ⟨1, 0⟩
  let z : Point := ⟨0, 0⟩
  -- `a(0) = −1 + e^{−2πi/5}(0 + 1) = −1 + ζ⁴`.
  let a := diskRot l rad z
  checks := checks.push ("a(0) = −1 + ζ⁴", ((a - (l + zpow 4)).norm < 1e-12))
  let spoke := r + rad * cis (-50 * pi / 180)
  return plate "One step of the left generator"
    "Two disks of radius 1.5 about −1 and +1. The left generator turns the origin clockwise by 72 degrees about −1 to a(0)."
    300 checks (#[
    circle f l rad leftC (tint leftC 26), circle f r rad rightC (tint rightC 26),
    labelAt f ⟨-1.55, 0.95⟩ 0 0 (txt "left disk") leftC,
    labelAt f ⟨1.55, 0.95⟩ 0 0 (txt "right disk") rightC,
    seg f r spoke rightC 1.5 "5 4",
    labelAt f (Point.mid r spoke) 8 4 (math "r = 1.5") rightC .start,
    seg f l z leftC 2, seg f l a leftC 2]
    ++ #[poly (arcPts f l 0.4 0 (-2 * pi / 5)) leftC 1.5,
      labelAt f (l + 0.66 * cis (-pi / 5)) 0 7 (math "72°") leftC]
    ++ arcArrow f l 1 0.08 (-2 * pi / 5 + 0.02) leftC 2 "6 4"
    ++ #[dot f l leftC, dot f r rightC, dot f z, dot f a leftC 5.5,
      labelAt f l 0 (-12) (math "−1") leftC, labelAt f r 0 (-12) (math "+1") rightC,
      labelAt f z 8 (-10) (math "0") ink .start,
      labelAt f a (-9) 21 (math "a(0)") leftC .finish])

/-! ### Figure 4: the chord words -/

/-- The word used at parameter `t` and the parameter it moves `tE` to (`TDCSG.Five.word₁`,
`word₂`, `word₃`): the first two add `2φ − 2`, the third adds `2φ − 4`. -/
private def chordStep (t : Float) : Nat × Float :=
  if t ≤ 1 - phi then (1, t + 2 * phi - 2)
  else if t ≤ 3 - 2 * phi then (2, t + 2 * phi - 2)
  else (3, t + 2 * phi - 4)

/-- Four successive returns `t₀ = 0, t₁, t₂, t₃` of the orbit of zero to the chord, drawn on
the parameter line `t ↦ tE`, with the three pieces of the chord and the word applied at each
step. -/
private def chord : Except String String := Id.run do
  let mut checks : Array (String × Bool) := #[]
  let x0 := 132.0
  let x1 := 452.0
  let xPos := fun (t : Float) => x0 + (t + 1) / 2 * (x1 - x0)
  let rowY := fun (k : Nat) => 78 + 58 * k.toFloat
  let cuts := #[1 - phi, 3 - 2 * phi]
  let mut xs : Array Node := #[]
  -- Pieces of the chord and the word each one uses.
  let ends := #[-1, 1 - phi, 3 - 2 * phi, 1]
  for i in [:3] do
    xs := xs.push (label ⟨xPos ((ends[i]! + ends[i + 1]!) / 2), 30⟩ (txt s!"{i + 1}") muted)
  xs := xs.push (label ⟨14, 30⟩ (txt "piece of word") muted .start)
  for c in cuts do
    xs := xs.push (Svg.line ⟨xPos c, 40⟩ ⟨xPos c, rowY 3 + 14⟩ faint 1.5 #[("stroke-dasharray", "4 4")])
  let mut t := 0.0
  let mut pts : Array (Float × Nat) := #[(0, 0)]
  for _ in [:3] do
    let (w, t') := chordStep t
    checks := checks.push ("chord step is a rotation by 2φ − 2 modulo 2", (t' ≥ -1 && t' < 1 &&
      ((t' - t - (2 * phi - 2)) / 2 - Float.round ((t' - t - (2 * phi - 2)) / 2)).abs < 1e-12))
    pts := pts.push (t', w)
    t := t'
  for k in [:4] do
    let y := rowY k
    xs := xs ++ #[Svg.line ⟨x0, y⟩ ⟨x1, y⟩ faint 4,
      Svg.path (Path.ellipse ⟨x0, y⟩ 4 4) rightC none, Svg.path (Path.ellipse ⟨x1, y⟩ 4 4) leftC none,
      label ⟨14, y + 6⟩ (math s!"k = {k}") muted .start]
  for k in [:4] do
    let (tk, w) := pts[k]!
    let p : Point := ⟨xPos tk, rowY k⟩
    if k > 0 then
      xs := xs ++ arrow ⟨30, rowY (k - 1) + 14⟩ ⟨30, rowY k - 18⟩ muted 1.5 ++
        #[label ⟨40, (rowY (k - 1) + rowY k) / 2 + 6⟩ (txt s!"word {w}") muted .start 18]
    xs := xs ++ #[Svg.path (Path.ellipse p 6 6) ink (some paper) 1.5,
      label ⟨p.x, p.y - 12⟩ (math s!"t_{k} ≈ {dec tk}") ink]
  xs := xs ++ xAxis (rowY 3 + 24) x0 x1
    #[(xPos (-1), math "−1"), (xPos (1 - phi), math "1−φ"), (xPos (3 - 2 * phi), math "3−2φ"),
      (xPos 0.5, math "1/2"), (xPos 1, math "1")] (txt "parameter " ++ math "t" ++ txt " of the point " ++ math "tE")
  xs := xs ++ #[label ⟨x0, rowY 0 - 16⟩ (math "−E") rightC, label ⟨x1, rowY 0 - 16⟩ (math "E") leftC]
  return plate "The first returns of the orbit of zero to the chord"
    "Four copies of the chord from −E to E, one per step. Each step applies the word of the piece containing the current point and moves it by 2φ − 2 modulo 2."
    360 checks xs

/-! ### Figure 5: the five possible centre changes -/

/-- From the current left centre `0`, the five candidate right centres `ζʲ` and the window
`|w − x| ≤ r/2` that decides which of them can act, at `x = 1/2`, `r = 1.95`. -/
private def moving : Except String String := Id.run do
  let mut checks : Array (String × Bool) := #[]
  let f : Frame := ⟨⟨205, 160⟩, 105⟩
  let r := 1.95
  let x : Point := ⟨0.5, 0⟩
  let mut nodes := #[circle f x (r / 2) windowC (tint windowC 18) 2,
    labelAt f ⟨1.22, 0.86⟩ 0 0 (txt "window") windowC .start]
  let rEnd := x + (r / 2) * cis (-0.22 * pi)
  nodes := nodes ++ #[seg f x rEnd windowC 1.5 "5 4",
    labelAt f (Point.mid x rEnd) 6 18 (math "r/2") windowC .start]
  let names := #["1", "ζ", "ζ²", "ζ³", "ζ⁴"]
  for j in [:5] do
    let p := zpow j
    let active := (p - x).norm ≤ r / 2
    nodes := nodes ++ (if active then #[seg f ⟨0, 0⟩ p rightC 2.5, dot f p rightC 5.5]
      else #[seg f ⟨0, 0⟩ p muted 1.5 "5 4", ring f p muted 5])
    let off := if j == 0 then (1.2 : Float) else 1.24
    nodes := nodes.push (labelAt f (off * p) (if j == 0 then 4 else 0) 7 (math names[j]!)
      (if active then rightC else muted))
  checks := checks.push ("exactly 1, ζ and ζ⁴ lie in the window", ((List.range 5).filter (fun j => (zpow j - x).norm ≤ r / 2) == [0, 1, 4]))
  nodes := nodes ++ #[dot f ⟨0, 0⟩ leftC 5.5, labelAt f ⟨0, 0⟩ (-10) 6 (math "0") leftC .finish,
    cross f x, labelAt f x 0 24 (math "x")]
  nodes := nodes ++ legend 40 312 #[(swDot rightC, txt "inside the window: can act"),
    (swRing muted, txt "outside the window"),
    (fun _ => #[], math "r = 1.95,  x = 1/2")]
  return plate "Five possible center changes in the moving frame"
    "From the current center 0, the five unit steps ζ^j. Those ending inside the window of radius r/2 about x (1, ζ, ζ⁴) can act; ζ² and ζ³ cannot."
    380 checks nodes

/-! ### Figure 6: the lens estimate -/

/-- Plate points of the lens `|v| ≤ a`, `|v − u| ≤ a` (convex), ordered around its centre. -/
private def lensPts (f : Frame) (u : Point) (a : Float) : Array Point := Id.run do
  let n := 240
  let mut ps : Array Point := #[]
  for i in [:n] do
    let θ := 2 * pi * i.toFloat / n.toFloat
    let p := a * cis θ
    if (p - u).norm ≤ a then ps := ps.push p
    let q := u + a * cis θ
    if q.norm ≤ a then ps := ps.push q
  let c := (0.5 : Float) * u
  let ang := fun (p : Point) => Float.atan2 (p.y - c.y) (p.x - c.x)
  return (ps.qsort (fun p q => ang p < ang q)).map f.at

/-- The lens of two disks of radius `r/2` about `0` and `u = ζ` and the vertical cut
`Re v = κ − η`, at `r = R` and at `r = 1.8`. -/
private def lenses : Except String String := Id.run do
  let mut checks : Array (String × Bool) := #[]
  let u := zpow 1
  let mut nodes := #[]
  for (cx, r, crit) in [(120.0, critical, true), (360.0, 1.8, false)] do
    let f : Frame := ⟨⟨cx - 0.155 * 78, 212⟩, 78⟩
    let a := r / 2
    -- The rightmost point of the lens: the circles meet at `u/2 ± t·(−iu)`, `t = √(a² − 1/4)`.
    let t := Float.sqrt (a * a - 0.25)
    let tip : Point := ⟨u.x / 2 + t * u.y, u.y / 2 - t * u.x⟩
    let cut := kappa - margin r
    checks := checks.push ("the lens touches the cut at R and misses it below", (if crit then (tip.x - kappa).abs < 1e-9 else tip.x < cut))
    let lens := lensPts f u a
    nodes := nodes ++ #[
      label ⟨cx, 26⟩ (if crit then math "r = R = √(3 + φ)" else math "r = 1.8"),
      circle f ⟨0, 0⟩ a windowC (tint windowC 14) 2, circle f u a windowC none 2 "6 4",
      Svg.path ((Path.polyline lens).close) (some (tint windowC 60)) none,
      seg f ⟨cut, -1.16⟩ ⟨cut, 2.1⟩ ink 2 "3 3",
      label ⟨(f.at ⟨cut, 0⟩).x, 324⟩ (mathUp "Re " ++ (if crit then math "v = κ" else math "v = κ − η")),
      labelAt f ((0.5 : Float) * u) 0 6 (txt "lens") ink,
      dot f ⟨0, 0⟩ windowC, dot f u windowC, dot f tip ink 5,
      labelAt f ⟨0, 0⟩ (-8) 20 (math "0") ink .finish, labelAt f u 8 (-6) (math "u") ink .start,
      if crit then labelAt f tip 8 22 (math "v_*") ink .start else labelAt f tip (-6) 26 (txt "tip") ink .finish]
  nodes := nodes ++ legend 40 356 #[(swLine windowC, math "|v| ≤ r/2"),
    (swLine windowC "6 4", math "|v − u| ≤ r/2,  u = ζ")]
  return plate "The lens reaches the cut at the critical radius and misses it below"
    "Two disks of radius r/2 about 0 and u = ζ and their lens. At r = √(3+φ) the tip of the lens lies on the cut Re v = κ; at r = 1.8 it lies strictly left of the moved cut Re v = κ − η."
    395 checks nodes

/-! ### Figure 7: a terminal crossing -/

/-- The window, radius and label of the terminal crossing: `r = 2.12`, `x = 0.472`, direction
`j = 0`, and `n = (4, −3, 1, 1, −3)`, of weight zero, with `P(n) = 7 − 4φ`. The level `n₀ = 4`
is good, `n` and `n + e₀` lie in the window, and `n + e₀` has no other neighbour. -/
private def terminalInstance : Float × Point × Label := (2.12, ⟨0.472, 0⟩, #[4, -3, 1, 1, -3])

/-- An edge of the centre graph at a good level ending in a leaf, with the window and the cut
`Re w = Re x + κ − η` that the lens estimate uses, and an enlargement near the leaf. -/
private def terminal : Except String String := Id.run do
  let mut checks : Array (String × Bool) := #[]
  let (r, x, n) := terminalInstance
  let leaf := shift n 0 1
  let others := [1, 2, 3, 4]
  checks := checks.push ("level 4 is good and the crossing edge ends in the leaf n + e₀", (weight n == 0 && goodness r x 0 n[0]! > 0 && inWindow r x n &&
      inWindow r x leaf && others.all (fun k => inWindow r x (shift n k 1)) &&
      others.all (fun k => !inWindow r x (shift leaf k (-1)))))
  let f : Frame := ⟨⟨80, 148⟩, 105⟩
  let pn := proj n
  let pl := proj leaf
  let cut := x.x + kappa - margin r
  checks := checks.push ("the leaf lies beyond the cut", (pl.x > cut))
  let mut xs := #[circle f x (r / 2) windowC (tint windowC 18) 2,
    labelAt f ⟨-0.12, 0.74⟩ 0 0 (txt "window") windowC]
  let rEnd := x + (r / 2) * cis (-0.2 * pi)
  xs := xs ++ #[seg f x rEnd windowC 1.5 "5 4",
    labelAt f (Point.mid x rEnd) 4 22 (math "r/2") windowC .start]
  for k in others do
    let q := proj (shift n k 1)
    xs := xs ++ #[seg f pn q rightC 2, dot f q rightC 5]
    let q' := proj (shift leaf k (-1))
    xs := xs ++ #[seg f pl q' muted 1.5 "5 4", ring f q' muted 5]
  xs := xs ++ #[seg f pn pl ink 3.5, cross f x, dot f pn leftC 6, dot f pl rightC 6,
    labelAt f x 0 28 (math "x") ink, labelAt f pn (-9) (-20) (math "n") leftC,
    labelAt f pl 18 (-38) (math "n + e_0") rightC]
  -- The enlargement: plate box around the leaf and the same neighbourhood scaled up.
  let lp := f.at pl
  xs := xs.push (Svg.rect (lp.x - 8) (lp.y - 8) 16 16 none
    (#[("stroke", rgbHex ink), ("stroke-width", "1.2")]))
  let zoom := 6000.0
  let g : Frame := ⟨⟨406 - zoom * pl.x, 100⟩, zoom⟩
  let bx := 342.0
  let bw := 128.0
  let edgePts := (Array.range 41).map fun i =>
    g.at (x + (r / 2) * cis (-0.0095 + 0.019 * i.toFloat / 40))
  xs := xs ++ #[Svg.rect bx 42 bw 116 (some paper) #[("stroke", rgbHex ink), ("stroke-width", "1.2")],
    label ⟨bx + bw / 2, 32⟩ (txt s!"enlarged ×{(zoom / f.scale).round.toUInt64}") muted,
    Svg.line ⟨bx, g.origin.y⟩ (g.at pl) ink 3.5, poly edgePts windowC 2,
    Svg.line (g.at ⟨cut, 0.0093⟩) (g.at ⟨cut, -0.0093⟩) ink 2 #[("stroke-dasharray", "3 3")],
    dot g pl rightC 6,
    label ⟨(g.at ⟨cut, 0⟩).x, 180⟩ (txt "cut") ink, label ⟨(g.at ⟨x.x + r / 2, 0⟩).x + 6, 180⟩ (txt "edge") windowC]
  xs := xs ++ legend 32 290 #[(swDot rightC, math "n + e_k" ++ txt ": other neighbors of " ++ math "n"),
    (swRing muted, math "n + e_0 − e_k" ++ txt ": outside the window"),
    (fun _ => #[], math "r = 2.12,  x = 0.472,  n = (4, −3, 1, 1, −3)"),
    (fun _ => #[], txt "the level " ++ math "n_0 = 4" ++ txt " is good")]
  return plate "A crossing at a good level ends in a leaf"
    "At r = 2.12 and x = 0.472 the label n = (4, −3, 1, 1, −3) sits at the good level n₀ = 4. Its edge to n + e₀ ends beyond the cut Re w = Re x + κ − η, so the four other candidate neighbors n + e₀ − e_k of n + e₀ lie outside the window and n + e₀ is a leaf."
    385 checks xs

/-! ### Figure 8: good levels -/

/-- The phases of the levels `m = −13, …, 9` of coordinate `0` at `x = 0.87`, `r = 1.8`, the
good bands `|phase| > L/2 − η`, and the two good levels the confinement proof uses. -/
private def wallLevels : Except String String := Id.run do
  let mut checks : Array (String × Bool) := #[]
  let r := 1.8
  let x : Point := ⟨0.87, 0⟩
  let lo : Int := -13
  let hi : Int := 9
  let good := ((List.range (hi - lo + 1).toNat).map (fun i : Nat => lo + i)).filter
    (fun m => goodness r x 0 m > 0)
  checks := checks.push ("the good levels in [−13, 9] are −10, −2 and 3", (good == [-10, -2, 3]))
  let px0 := 70.0
  let px1 := 420.0
  let top := 54.0
  let bot := 268.0
  let xPos := fun (m : Float) => px0 + (m - (Float.ofInt lo - 0.5)) / (Float.ofInt (hi - lo) + 1) * (px1 - px0)
  let yPos := fun (v : Float) => (top + bot) / 2 - v / period * (bot - top)
  let band := margin r / period * (bot - top)
  let mut xs : Array Node := #[
    Svg.rect (xPos (-2.5)) top (xPos 2.5 - xPos (-2.5)) (bot - top) (some (tint faint 70)),
    label ⟨xPos 0, top - 10⟩ (math "|m| ≤ 2") muted,
    Svg.rect px0 top (px1 - px0) band (some (tint goodC 70)),
    Svg.rect px0 (bot - band) (px1 - px0) band (some (tint goodC 70)),
    label ⟨px1 + 6, top + band - 2⟩ (txt "good") goodC .start,
    label ⟨px1 + 6, bot - 2⟩ (txt "good") goodC .start,
    Svg.line ⟨px0, yPos 0⟩ ⟨px1, yPos 0⟩ faint 1,
    Svg.rect px0 top (px1 - px0) (bot - top) none #[("stroke", rgbHex muted), ("stroke-width", "1")]]
  for m in [-10, 3] do
    xs := xs.push (Svg.line ⟨xPos m.toFloat, top⟩ ⟨xPos m.toFloat, bot⟩ ink 1 #[("stroke-dasharray", "3 3")])
  xs := xs ++ #[label ⟨xPos (-10), top - 10⟩ (math "lo = −10"), label ⟨xPos 3 + 4, top - 10⟩ (math "hi = 3") ink .start]
  for i in [:(hi - lo + 1).toNat] do
    let m : Int := lo + i
    let p : Point := ⟨xPos (Float.ofInt m), yPos (reducedPhase x 0 m)⟩
    xs := xs.push <|
      if m == -10 || m == 3 then Svg.path (Path.ellipse p 6 6) ink (some paper) 1.5
      else if good.contains m then Svg.path (Path.ellipse p 6 6) paper ink 2.5
      else Svg.path (Path.ellipse p 3.5 3.5) muted none
  xs := xs.push (label ⟨xPos (-2), yPos (reducedPhase x 0 (-2)) + 26⟩ (math "−2") ink)
  xs := xs ++ yAxis px0 top bot #[(top, math "L/2"), (yPos 0, math "0"), (bot, math "−L/2")]
    (txt "phase mod " ++ math "L")
  xs := xs ++ xAxis bot px0 px1 ((#[-12, -8, -4, 0, 4, 8] : Array Int).map fun m =>
      (xPos (Float.ofInt m), math (if m < 0 then s!"−{m.natAbs}" else toString m)))
    (txt "level " ++ math "m" ++ txt " of coordinate " ++ math "n_0")
  xs := xs ++ legend 40 352 #[(swDot ink, txt "good, used by the proof"),
    (swRing ink, txt "good, not in the search range"),
    (fun p => #[Svg.path (Path.ellipse p 3.5 3.5) muted none], txt "not good"),
    (fun _ => #[], math "r = 1.8,  x = 0.87,  j = 0")]
  return plate "The phases of the levels of one coordinate"
    "For r = 1.8, x = 0.87 and coordinate 0, the phase of each level m from −13 to 9 reduced modulo L. Levels in the shaded bands are good: −10, −2 and 3. The proof uses −10 and 3; −2 lies in the range |m| ≤ 2 where it does not search."
    455 checks xs

/-! ### Figure 9: a component of the centre graph -/

/-- The component of the label `0` in the centre graph at `x = 1/2`, `r = 1.95`, enumerated in
label space from the window test, and the number of labels found (`0` if the search did not
finish). -/
private def componentEdges : List (Label × Label) × Nat := Id.run do
  let r := 1.95
  let x : Point := ⟨0.5, 0⟩
  let z : Label := #[0, 0, 0, 0, 0]
  let mut seen := [z]
  let mut todo := [z]
  let mut edges := []
  for _ in [:64] do
    let n :: rest := todo | break
    todo := rest
    -- Weight-zero labels gain `e_j`, weight-one labels lose it (`TDCSG.Five.CenterEdge`).
    let sign : Int := if weight n == 0 then 1 else -1
    for j in [:5] do
      let m := shift n j sign
      if inWindow r x n && inWindow r x m then
        if sign == 1 then edges := (n, m) :: edges
        if !seen.contains m then
          seen := m :: seen
          todo := m :: todo
  return (edges, if todo.isEmpty then seen.length else 0)

/-- The 18 labels of the component drawn at their projections inside the window. -/
private def component : Except String String := Id.run do
  let mut checks : Array (String × Bool) := #[]
  let f : Frame := ⟨⟨165, 178⟩, 150⟩
  let x : Point := ⟨0.5, 0⟩
  let (edges, count) := componentEdges
  checks := checks.push ("the component has 18 labels", count == 18)
  let mut xs := #[circle f x 0.975 windowC (tint windowC 18) 2]
  for (n, m) in edges do
    xs := xs.push (seg f (proj n) (proj m) ink 1.5)
  for (n, m) in edges do
    xs := xs ++ #[dot f (proj n) leftC 5, dot f (proj m) rightC 5]
  xs := xs ++ #[cross f x,
    labelAt f ⟨0, 0⟩ (-6) 24 (math "0") leftC .finish, labelAt f ⟨1, 0⟩ 6 24 (math "e_0") rightC .start,
    labelAt f ⟨1.38, 0.86⟩ 0 0 (txt "window") windowC .start]
  xs := xs ++ legend 40 362 #[(swDot leftC, txt "weight 0 (left centers)"),
    (swDot rightC, txt "weight 1 (right centers)"),
    (fun p => #[Svg.path (Path.ellipse p 7 7) (some (tint windowC 18)) windowC 2],
      txt "window " ++ math "|w − x| ≤ r/2" ++ txt ", center " ++ math "x" ++ txt " (×)"),
    (fun _ => #[], math "r = 1.95,  x = 1/2")]
  return plate "The component of zero in the center graph"
    "The 18 labels reachable from 0 at x = 1/2 and r = 1.95, drawn at their projections inside the window of radius r/2, with the edges of the center graph."
    450 checks xs

/-- Writes the seven plates and their SHA-256 manifest to `dest`. The generator runs this before
Verso copies its site assets. -/
def write (dest : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dest
  let mut sums := ""
  for (name, svg) in [("disks", disks), ("moving", moving),
      ("lens", lenses), ("levels", wallLevels), ("terminal", terminal), ("component", component),
      ("chord", chord)] do
    let file := name ++ ".svg"
    let svg ← IO.ofExcept svg
    IO.FS.writeFile (dest / file) svg
    sums := sums ++ Sha256.hex (Sha256.hashString svg) ++ "  " ++ file ++ "\n"
  IO.FS.writeFile (dest / "SHA256SUMS") sums

end TDCSGBlueprint.Figures
