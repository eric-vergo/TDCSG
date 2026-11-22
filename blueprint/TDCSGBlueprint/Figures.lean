/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import PILean.Svg
import PILean.Trust.Sha256

/-! Plane diagrams for the fivefold critical radius. The integer labels of the example component
are retained throughout enumeration. Floating-point arithmetic is used only for illustrations. -/

namespace TDCSGBlueprint.Figures

open PILean Svg

private def ink := Rgba.rgb 28 44 57
private def blue := Rgba.rgb 16 96 136
private def rust := Rgba.rgb 157 60 30
private def faint := Rgba.rgb 145 159 164
private def paper := Rgba.rgb 250 248 241
private def phi := (1 + Float.sqrt 5) / 2
private def critical := Float.sqrt (3 + phi)
private def unitDir (j : Nat) : Point :=
  let a := 2 * 3.141592653589793 * j.toFloat / 5
  ⟨Float.cos a, Float.sin a⟩

private structure Frame where
  origin : Point
  scale : Float

private def Frame.atPt (f : Frame) (p : Point) : Point :=
  ⟨f.origin.x + f.scale * p.x, f.origin.y - f.scale * p.y⟩

private def label (x y : Float) (s : String) (c := ink) : Node :=
  Svg.text x y s 16 c .middle #[("font-family", "system-ui, sans-serif")]

private def disk (f : Frame) (p : Point) (r : Float) (c : Rgba) (shade := false) : Node :=
  let fill := if shade then some { c with a := 22 } else none
  Svg.path (Path.ellipse (f.atPt p) (r*f.scale) (r*f.scale)) fill c 2

private def dot (f : Frame) (p : Point) (c := ink) : Node :=
  Svg.path (Path.ellipse (f.atPt p) 4 4) c none

private def edge (f : Frame) (a b : Point) (c := ink) (w : Float := 2) : Node :=
  Svg.line (f.atPt a) (f.atPt b) c w

private def plate (title : String) (h : Float) (xs : Array Node) : String :=
  Svg.document 520 h (#[Svg.el "title" #[] #[.text title], Svg.rect 0 0 520 h paper] ++ xs)

private def opening : String := Id.run do
  let f : Frame := ⟨⟨260,142⟩, 59⟩
  let e := unitDir 1 - unitDir 2
  return plate "The critical chord between two closed disks" 286 #[
    disk f ⟨-1,0⟩ critical blue true, disk f ⟨1,0⟩ critical rust true,
    edge f ((-1 : Float)*e) e ink 3, dot f e rust, dot f ((-1 : Float)*e) blue,
    dot f ⟨-1,0⟩ blue, dot f ⟨1,0⟩ rust, dot f ⟨0,0⟩,
    label 183 181 "−E" blue, label 337 113 "E" rust,
    label 198 134 "−1", label 338 164 "+1", label 263 164 "0"]

private def disks : String := Id.run do
  let f : Frame := ⟨⟨260, 135⟩, 75⟩
  let l : Point := ⟨-1, 0⟩
  let r : Point := ⟨1, 0⟩
  let z : Point := ⟨0, 0⟩
  let a := l + unitDir 4
  return plate "A clockwise fifth-turn about the left center" 270 #[
    disk f l 1.5 blue true, disk f r 1.5 rust true, edge f l z blue, edge f l a blue,
    dot f l, dot f r, dot f z rust, dot f a blue,
    label 185 124 "−1", label 335 124 "+1", label 260 122 "z",
    label 238 221 "A(z)" blue]

private def moving : String := Id.run do
  let f : Frame := ⟨⟨260, 147⟩, 95⟩
  let z : Point := ⟨0,0⟩
  let x : Point := ⟨0.5,0⟩
  let mut nodes := #[disk f x 0.975 blue true, dot f x rust, label 325 172 "x"]
  for j in [:5] do
    let p := unitDir j
    let active := (p - x).norm ≤ 0.975
    let col := if active then blue else faint
    nodes := nodes ++ #[edge f z p col, dot f p col]
    let q := f.atPt ((1.22 : Float) * p)
    nodes := nodes.push (label q.x (q.y + 5) (#["1", "ζ", "ζ²", "ζ³", "ζ⁴"][j]!) col)
  return plate "Five possible center changes in the physical projection" 300
    (nodes ++ #[dot f z, label 248 170 "0"])

private def lenses : String := Id.run do
  let u := unitDir 1
  let axial := (1 + Float.sqrt 5 / 2) / 2
  let mut nodes := #[]
  for (ox,r,title) in [(128.0,critical,"At equality"),(385.0,1.8,"Below, r = 1.8")] do
    let f : Frame := ⟨⟨ox,178⟩,72⟩
    let a := r/2
    let t := Float.sqrt (a*a-0.25)
    let tip : Point := ⟨u.x/2 + t*u.y, u.y/2 - t*u.x⟩
    let wall := axial - (3 + phi - r*r)/16
    nodes := nodes ++ #[label ox 28 title, disk f ⟨0,0⟩ a blue true, disk f u a rust true,
      edge f ⟨wall,-1.13⟩ ⟨wall,2.03⟩ ink 1.5, dot f tip, dot f ⟨0,0⟩ blue,
      dot f u rust, label (ox-13) 198 "0", label (ox+13) 95 "u"]
  return plate "The lens reaches the cut at equality and misses it below" 274 nodes

private abbrev Label := Array Int
private def projection (n : Label) : Point :=
  (List.range 5).foldl (fun p j => p + (Float.ofInt n[j]!) * unitDir j) ⟨0,0⟩

/-- The component of the zero label at x = 1/2 and r = 1.95, enumerated in label space. -/
private def componentEdges : List (Label × Label) := Id.run do
  let z : Label := #[0,0,0,0,0]
  let mut seen := [z]
  let mut todo := [z]
  let mut edges := []
  -- The figure's build guard below checks exhaustion and the expected vertex count.
  for _ in [:64] do
    let n :: rest := todo | break
    todo := rest
    let sign : Int := if n.foldl (·+·) 0 == 0 then 1 else -1
    for j in [:5] do
      let m := n.modify j (· + sign)
      if (projection m - (⟨0.5,0⟩ : Point)).norm ≤ 0.975 then
        if sign == 1 then edges := (n,m) :: edges
        if !seen.contains m then
          seen := m :: seen
          todo := m :: todo
  if !todo.isEmpty || seen.length != 18 then panic! "component enumeration failed"
  return edges

private def component : String := Id.run do
  let f : Frame := ⟨⟨200,158⟩,120⟩
  let mut xs := #[disk f ⟨0.5,0⟩ 0.975 blue true]
  for (n,m) in componentEdges do
    xs := xs.push (edge f (projection n) (projection m) blue)
  for (n,m) in componentEdges do
    xs := xs ++ #[dot f (projection n) blue, dot f (projection m) rust]
  return plate "The projected 18-label component in its physical window" 314 xs

private def wallLevels : String := Id.run do
  let period := Float.sqrt 5 / 2
  let margin := (3 + phi - 1.8 * 1.8) / 16
  let alpha := 1 + phi / 2
  let xPos := fun (m : Float) => 300 + 19*m
  let yPos := fun (v : Float) => 108 - 100*v
  let mut xs := #[]
  for top in [period/2, -period/2+margin] do
    xs := xs.push (Svg.rect 51 (yPos top) 424 (100*margin) (some { rust with a := 56 }))
  xs := xs ++ #[Svg.line ⟨51,108⟩ ⟨475,108⟩ faint 1,
    label 29 58 "+L/2", label 29 169 "−L/2", label 260 27 "Phase of each coordinate level"]
  for i in [:23] do
    let m := i.toFloat - 13
    let raw := alpha*m - 0.37
    let phase := raw - period * Float.floor (raw/period + 0.5)
    let px := xPos m
    let py := yPos phase
    let selected := i == 3 || i == 16
    let col := if selected then rust else blue
    if selected then
      xs := xs ++ #[Svg.line ⟨px,47⟩ ⟨px,171⟩ rust 1 #[("stroke-dasharray","3 3")],
        label px 193 (if i == 3 then "lo = −10" else "hi = 3") rust]
    xs := xs.push (Svg.path (Path.ellipse ⟨px,py⟩ 3.4 3.4) col none)
  return plate "Two integer levels whose phases lie near half a period" 211 xs

private def terminal : String := Id.run do
  let f : Frame := ⟨⟨188,137⟩,106⟩
  let u : Point := ⟨1,0⟩
  -- Window center near the leaf at zero: only its j = 0 neighbor lies in the window.
  let x : Point := ⟨0.87,0⟩
  let mut xs := #[disk f x 0.9 blue true]
  for j in [:5] do
    let q := unitDir j
    let c := if j == 0 then blue else faint
    xs := xs ++ #[edge f ⟨0,0⟩ q c, dot f q c]
  xs := xs ++ #[dot f ⟨0,0⟩ rust, dot f x, dot f u blue, label 175 162 "leaf" rust,
    label 335 127 "neighbor" blue, label 267 165 "x"]
  return plate "One retained crossing at a terminal endpoint" 276 xs

private def chord : String := Id.run do
  let e := unitDir 1 - unitDir 2
  let mut xs := #[]
  for k in [:4] do
    let yy := 53 + k.toFloat * 61
    let f : Frame := ⟨⟨289,yy⟩, 100⟩
    let t := k.toFloat * (2*phi-2)
    let t := t - 2 * Float.floor ((t+1)/2)
    xs := xs ++ #[edge f ((-1 : Float)*e) e faint, dot f (t*e) rust,
      label 70 (yy-2) s!"Step {k}",
      label 70 (yy+18) (#["start", "word 3", "word 1", "word 3"][k]!) blue, label 135 (yy+39) "−E", label 417 (yy-18) "E"]
  return plate "The first four points of the irrational chord rotation" 285 xs

/-- The generator writes these PILean diagrams before Verso copies its site assets. -/
def write (dest : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dest
  let mut sums := ""
  for (name,svg) in [("critical-chord",opening), ("disks",disks), ("moving",moving), ("lens",lenses),
      ("levels",wallLevels), ("terminal",terminal), ("component",component), ("chord",chord)] do
    let file := name ++ ".svg"
    IO.FS.writeFile (dest / file) svg
    sums := sums ++ Sha256.hex (Sha256.hashString svg) ++ "  " ++ file ++ "\n"
  IO.FS.writeFile (dest / "SHA256SUMS") sums

end TDCSGBlueprint.Figures
