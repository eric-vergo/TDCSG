/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import TDCSGFigures

/-!
# Previews of the figures

`tdcsg-figure-preview [--out DIR] [NAME …]` renders the figures named (all of `previews` when none
is named) to `DIR` (`out` by default) for an author to look at: for each figure, or each frame of
an explorer, an SVG and a PNG in the light style, in its dark twin, and at the narrow width in
both, named `NAME[-frame-K][-narrow][-dark].{svg,png}` (a plot, which has no narrow rendition, in
the light style and its dark twin). It prints every layout problem the figure's checks report
(`PILean.Plane.Check`, `PILean.Plot.Check` for a plot) at both widths, whatever the figure's
checks level, and exits with status 1 if there is one. The site build renders the same figures
with the files, fingerprints and manifest of `PILeanVerso.withFigures`; these previews are only
for looking.

`tdcsg-figure-preview --frame-pair-keys DIR [OPTION …]` draws the key figures of the frame pair
(`TDCSGFigures.Lift.FramePairConfig.keys`) as pictures of each panel in a folder of `DIR` named
after the variant, with contact sheets (`sheet*.html`: one row per key, the two panels and the
caption), prints their layout problems, whether every declared move arrives exactly
(`FramePairConfig.allArrive`) and the disks' diameters in pixels, and exits with status 1 if one
fails. The options: `--word W` (letters `a`, `b`, `A = a⁻¹`, `B = b⁻¹`; `abab` by default),
`--variant R1|R2|R3`, `--trails`, `--trail-arcs`, `--full`, `--idle outline|ring` and
`--view shared|cropped|wide-right`.
-/

namespace TDCSGFigures.Preview

open PILean

/-- What a preview shows: a plane figure, the frames of an explorer of plane figures as its
slider or stepper shows them (one view for all, `Plane.commonView`), or a plot. -/
inductive Entry where
  /-- A plane figure. -/
  | plane (fig : Plane.Figure)
  /-- The frames of an explorer, with their value or step labels. -/
  | frames (figs : Array (String × Plane.Figure))
  /-- A plot. -/
  | plot (fig : Plot.Figure)

/-- The figures with their names. A new figure is added here to be previewed. -/
def previews : Array (String × Entry) := #[
  ("criticalChord", .plane criticalChord),
  ("orbitRadius", .frames sliderFrames),
  ("extensionJump", .plane extensionJump),
  ("disjointDisks", .plane disjointDisks),
  ("generatorStep", .plane generatorStep),
  ("wordSteps", .frames stepFrames),
  ("radiusLineInfinite", .plane radiusLineInfinite),
  ("radiusLineFinite", .plane radiusLineFinite),
  ("chordPieces", .plane chordPieces),
  ("wordTrace", .frames traceFrames),
  ("exchangedIntervals", .plane exchangedIntervals),
  ("coordinateBox", .plane coordinateBox),
  ("radiusThreshold", .plane radiusThreshold),
  ("chordOrbit", .plane chordOrbit),
  ("orderEight", .plane orderEight),
  ("orderTen", .plane orderTen),
  ("orderTwelve", .plane orderTwelve),
  ("unitSteps", .plane Lift.unitSteps),
  ("changeOfFrame", .frames Lift.frames),
  ("lensEstimate", .plane Lens.lensEstimate),
  ("lensRadius", .frames Lens.sliderFrames),
  ("levelPhases", .plot Levels.levelPhases),
  ("terminalCrossing", .plane Levels.terminalCrossing),
  ("terminalZoom", .plane Levels.terminalZoom),
  ("componentOfZero", .plane Confinement.componentOfZero),
  ("walkToLeaf", .frames Confinement.walkFrames)]

/-- The pictures of one figure: name suffix and figure, light, dark, narrow and narrow dark. -/
def variants (fig : Plane.Figure) : Array (String × Plane.Figure) :=
  let dark := fun (f : Plane.Figure) => f.style.darkTwin?.map fun s => { f with style := s }
  let base := #[("", fig)] ++ (fig.narrow.map ("-narrow", ·)).toArray
  base.flatMap fun (n, f) => #[(n, f)] ++ ((dark f).map (n ++ "-dark", ·)).toArray

/-- Writes the pictures of `fig` as `stem…` in `dir` and returns the layout problems of the figure
and of its narrow rendition (the checks cover both themes). -/
def render (dir : System.FilePath) (stem : String) (fig : Plane.Figure) : IO (Array String) := do
  for (suffix, f) in variants fig do
    IO.FS.writeFile (dir / s!"{stem}{suffix}.svg") f.toSvg
    match f.toPng with
    | some png => IO.FS.writeBinFile (dir / s!"{stem}{suffix}.png") png
    | none => throw <| IO.userError s!"{stem}{suffix}: no pixels"
  let narrow := match fig.narrow with
    | some f => f.problems.map ("narrow: " ++ ·.message)
    | none => #[]
  return fig.problems.map (·.message) ++ narrow

/-- Writes the pictures of the plot `fig` as `stem…` in `dir`, light and dark, and returns its
labelling problems. -/
def renderPlot (dir : System.FilePath) (stem : String) (fig : Plot.Figure) : IO (Array String) := do
  let dark := fig.style.darkTwin?.map fun s => { fig with style := s }
  for (suffix, f) in #[("", fig)] ++ (dark.map ("-dark", ·)).toArray do
    IO.FS.writeFile (dir / s!"{stem}{suffix}.svg") f.toSvg
    match f.toPng with
    | some png => IO.FS.writeBinFile (dir / s!"{stem}{suffix}.png") png
    | none => throw <| IO.userError s!"{stem}{suffix}: no pixels"
  return fig.checkMessages

/-- The command-line options: the output folder and the names asked for. -/
def parse : List String → System.FilePath × Array String →
    Except String (System.FilePath × Array String)
  | [], acc => .ok acc
  | "--out" :: dir :: rest, (_, ns) => parse rest (dir, ns)
  | "--out" :: [], _ => .error "--out needs a folder"
  | n :: rest, (d, ns) => parse rest (d, ns.push n)

/-! ### The key figures of the frame pair -/

/-- Text with `&`, `<`, `>` and `"` escaped for HTML. -/
def htmlEscape (t : String) : String :=
  t.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

/-- The options of `--frame-pair-keys`: the word, the right panel's style (`R1`, `R2`, `R3`),
trails, and the full-size left panel. -/
def parseFramePair : List String → Lift.FramePairConfig → Except String Lift.FramePairConfig
  | [], c => .ok c
  | "--word" :: w :: rest, c => parseFramePair rest { c with word := Lift.parseWord w }
  | "--variant" :: "R1" :: rest, c => parseFramePair rest { c with right := .bodies }
  | "--variant" :: "R2" :: rest, c => parseFramePair rest { c with right := .centres }
  | "--variant" :: "R3" :: rest, c => parseFramePair rest { c with right := .bodiesGraph }
  | "--trails" :: rest, c => parseFramePair rest { c with trails := true }
  | "--full" :: rest, c => parseFramePair rest { c with left := .full }
  | "--trail-arcs" :: rest, c => parseFramePair rest { c with trailStyle := .arcs }
  | "--idle" :: "outline" :: rest, c => parseFramePair rest { c with idleMark := .outline }
  | "--idle" :: "ring" :: rest, c => parseFramePair rest { c with idleMark := .ring }
  | "--view" :: "shared" :: rest, c => parseFramePair rest { c with view := .shared }
  | "--view" :: "cropped" :: rest, c => parseFramePair rest { c with view := .cropped }
  | "--view" :: "wide-right" :: rest, c => parseFramePair rest { c with view := .wideRight }
  | a :: _, _ => .error s!"--frame-pair-keys: unknown option {a}"

/-- The name of a variant's folder: word, right style, trails, left scale. -/
def variantName (c : Lift.FramePairConfig) : String :=
  let w := String.join (c.word.map fun l => match l with
    | .a => "a" | .b => "b" | .aInv => "A" | .bInv => "B")
  let r := match c.right with | .bodies => "R1" | .centres => "R2" | .bodiesGraph => "R3"
  s!"{w}-{r}-{if c.trails then "trails" else "notrails"}-" ++
    (match c.left with | .halved => "halved" | .full => "full") ++
    (if c.trails && c.trailStyle == .arcs then "-arcs" else "") ++
    (match c.idleMark with | .outline => "" | .ring => "-ring") ++
    (match c.view with | .shared => "" | .cropped => "-cropped" | .wideRight => "-wideright")

/-- A contact sheet: one row per key with the pictures `left` and `right` (file names relative to
the sheet) and the caption. -/
def contactSheet (title : String) (rows : Array (String × String × String)) (dark : Bool)
    (stacked : Bool) : String :=
  let bg := if dark then "#1b1d21" else "#ffffff"
  let fg := if dark then "#e6e6e6" else "#1b1d21"
  let cell := fun (f : String) => s!"<img src=\"{htmlEscape f}\" alt=\"\">"
  let body := String.join (rows.toList.map fun (l, r, cap) =>
    if stacked then
      s!"<tr><td>{cell l}<br>{cell r}</td><td>{htmlEscape cap}</td></tr>\n"
    else s!"<tr><td>{cell l}</td><td>{cell r}</td><td>{htmlEscape cap}</td></tr>\n")
  s!"<!doctype html><html><head><meta charset=\"utf-8\"><title>{htmlEscape title}</title>" ++
    s!"<style>body\{background:{bg};color:{fg};font:14px sans-serif}td\{vertical-align:top;" ++
    "padding:6px}td:last-child{max-width:22em}</style></head><body>" ++
    s!"<h1>{htmlEscape title}</h1><table>\n{body}</table></body></html>\n"

/-- Writes the keys of both panels of a variant as pictures (light, dark, narrow, narrow dark) in a
folder of `dir` named after the variant, with three contact sheets, and returns the layout
problems and whether every step arrives exactly. -/
def renderFramePair (dir : System.FilePath) (c : Lift.FramePairConfig) :
    IO (Array String × Bool) := do
  let out := dir / variantName c
  IO.FS.createDirAll out
  let mut problems : Array String := #[]
  let mut rows : Array (String × String × String) := #[]
  for (k, (l, r)) in c.keys.mapIdx fun k p => (k, p) do
    problems := problems ++ ((← render out s!"left-{k}" l).map (s!"left key {k}: " ++ ·))
    problems := problems ++ ((← render out s!"right-{k}" r).map (s!"right key {k}: " ++ ·))
    rows := rows.push (s!"left-{k}", s!"right-{k}", c.keyCaption k)
  let title := s!"Frame pair keys: {variantName c}"
  let sheet := fun (suffix : String) => rows.map fun (l, r, cap) =>
    (s!"{l}{suffix}.png", s!"{r}{suffix}.png", cap)
  IO.FS.writeFile (out / "sheet.html") (contactSheet title (sheet "") false false)
  IO.FS.writeFile (out / "sheet-dark.html") (contactSheet title (sheet "-dark") true false)
  IO.FS.writeFile (out / "sheet-narrow.html")
    (contactSheet title (sheet "-narrow") false true)
  IO.FS.writeFile (out / "sheet-narrow-dark.html")
    (contactSheet title (sheet "-narrow-dark") true true)
  return (problems, c.allArrive)

/-- The diameter in pixels of the disks of each panel, at its width and at its narrow width. -/
def diskSizes (c : Lift.FramePairConfig) : String :=
  match c.keys[0]? with
  | none => ""
  | some (l, r) =>
    let rl : Float := match c.left with
      | .halved => Exact.toFloat c.radius | .full => 2 * Exact.toFloat c.radius
    let d := fun (f : Plane.Figure) (ρ : Float) => (f.frame.scale * ρ).round.toUInt64.toNat
    let nl := l.narrow.getD l
    let nr := r.narrow.getD r
    s!"disk diameter: left {d l rl} px, right {d r (Exact.toFloat c.radius)} px " ++
      s!"(panels {l.width.round.toUInt64.toNat} and {r.width.round.toUInt64.toNat} px wide); " ++
      s!"narrow: left {d nl rl} px, " ++
      s!"right {d nr (Exact.toFloat c.radius)} px"

end TDCSGFigures.Preview

open PILean TDCSGFigures.Preview in
/-- Renders the previews (see the module docstring). -/
def main (args : List String) : IO UInt32 := do
  if let "--frame-pair-keys" :: dir :: rest := args then
    let c ← IO.ofExcept (parseFramePair rest {})
    let (ps, ok) ← renderFramePair dir c
    for p in ps do IO.println s!"  {p}"
    IO.println (s!"{variantName c}: {c.keyCount} keys, {ps.size} layout problems, " ++
      s!"exact arrival {ok}; {diskSizes c}")
    return if ps.isEmpty && ok then 0 else 1
  let (dir, names) ← IO.ofExcept (parse args ("out", #[]))
  let unknown := names.filter fun n => !previews.any (·.1 == n)
  if !unknown.isEmpty then
    let known := ", ".intercalate (previews.map (·.1)).toList
    IO.eprintln s!"unknown figures: {", ".intercalate unknown.toList}; known: {known}"
    return 2
  IO.FS.createDirAll dir
  let mut problems := 0
  for (name, entry) in previews do
    if !names.isEmpty && !names.contains name then continue
    if let .plot f := entry then
      let ps ← renderPlot dir name f
      IO.println s!"{name}: plot, {ps.size} labelling problems"
      for p in ps do IO.println s!"  {p}"
      problems := problems + ps.size
      continue
    let figs : Array (String × Plane.Figure) := match entry with
      | .plot _ => #[]
      | .plane f => #[(name, f)]
      | .frames fs =>
        let views := PILean.Plane.commonView (fs.map (·.2))
        views.mapIdx fun k f => (s!"{name}-frame-{k}", f)
    for (stem, f) in figs do
      let ps ← render dir stem f
      IO.println s!"{stem}: {f.items.size} items, {ps.size} layout problems"
      for p in ps do IO.println s!"  {p}"
      problems := problems + ps.size
  IO.println s!"wrote {dir}"
  return if problems == 0 then 0 else 1
