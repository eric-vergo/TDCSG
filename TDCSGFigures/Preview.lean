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
`--variant R1|R2|R3`, `--trails` (the last three positions), `--full-trails` (every earlier
position), `--trail-arcs`, `--full`, `--idle ring|outline` and
`--view shared|cropped|wide-right`.

`tdcsg-figure-preview --motion-variants DIR` animates the variants of the frame pair in
`motionVariants` (`TDCSGFigures.Lift.FramePairConfig.motion`, two panels on one clock) and writes,
for each, four standalone animated SVGs at the canonical pacing (`Lift.canonicalPacing`: every
move and rest one second, no easing, a cut) to `DIR/svg` (`ID.svg`, `ID-dark.svg`,
`ID-narrow.svg`, `ID-narrow-dark.svg`), the files PILean's `tools/motion-browser-check.py` reads
for the light renditions to `DIR/check`, the list of variants with their options, segments,
captions and sizes to `DIR/variants.json`, and `DIR/index.html`: a self-contained page (the
template `FramePairPreview.html` with the variants and SVG texts filled in) that plays a variant
re-timed by sliders for the durations, easing, seam and speed, scrubs through the loop, shows the
stills, and writes the chosen values as Lean to copy. A variant the engine refuses (an error of
`MotionPanels.report` under `checks := .fail`) is printed and makes the tool exit with status 1.
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
  | "--full-trails" :: rest, c =>
    parseFramePair rest { c with trails := true, trailLength := none }
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
    (if c.trails && c.trailLength.isNone then "-full" else "") ++
    (match c.idleMark with | .outline => "-outline" | .ring => "") ++
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

/-! ### The animated frame pair: variants and a page to tune them -/

/-- The variants of `--motion-variants`: the words `abab` (every letter acts), `ababbab` (one
letter does not), `aababaabbabb` (three do not) and `aabaaabbbbb` (closed: its last key is its
first), each with the right panel `R1` and `R3` (`R2` for the twelve-letter word), without and with
trails (a tail of the last three positions; every earlier position for `abab` only), the views
shared and cropped (wide-right for the two long words), the idle mark as a ring (as a dashed circle
outside the disk for the twelve-letter word), and the left panel halved (full size for `abab` and
the twelve-letter word). -/
def motionVariants : Array Lift.FramePairConfig :=
  let w := Lift.parseWord
  let twelve := w "aababaabbabb"
  let closed := w "aabaaabbbbb"
  #[{ word := w "abab" }, { word := w "abab", trails := true },
    { word := w "abab", trails := true, trailLength := none },
    { word := w "abab", right := .bodiesGraph }, { word := w "abab", left := .full },
    { word := w "abab", view := .cropped },
    { word := w "ababbab" }, { word := w "ababbab", trails := true },
    { word := w "ababbab", right := .bodiesGraph }, { word := w "ababbab", view := .cropped },
    { word := twelve }, { word := twelve, trails := true },
    { word := twelve, right := .bodiesGraph },
    { word := twelve, right := .bodiesGraph, trails := true },
    { word := twelve, right := .centres },
    { word := twelve, view := .cropped }, { word := twelve, view := .wideRight },
    { word := twelve, right := .bodiesGraph, view := .wideRight },
    { word := twelve, right := .centres, view := .wideRight },
    { word := twelve, idleMark := .outline },
    { word := twelve, idleMark := .outline, view := .wideRight },
    { word := twelve, left := .full }, { word := twelve, left := .full, view := .wideRight },
    { word := closed }, { word := closed, trails := true },
    { word := closed, right := .bodiesGraph },
    { word := closed, view := .cropped }, { word := closed, view := .wideRight },
    { word := closed, right := .bodiesGraph, view := .wideRight }]

/-- A JSON string: escaped, and with `</` written `<\/` so that it can stand inside an HTML
`script` element. -/
def jsonString (s : String) : String :=
  "\"" ++ (Trust.Json.escape s).replace "</" "<\\/" ++ "\""

/-- A number as JSON (`0` for one that is not finite). -/
def jsonNum (x : Float) : String := if x.isFinite then toString x else "0"

/-- A page point as JSON. -/
def jsonPoint (p : Point) : String := s!"[{jsonNum p.x}, {jsonNum p.y}]"

/-- Whether some actor that turns has a label or a point's marker: then the picture must have
upright groups. -/
def turningMarks (m : Plane.Motion) : Bool :=
  (m.steps.mapIdx fun j s => (j, s)).any fun (j, s) => s.moves.any fun (id, mv) =>
    match mv, (m.keys.getD j default).actor? id with
    | .turn .., some it => it.leaves.any (·.geom.upright)
    | _, _ => false

/-- What PILean's `tools/motion-browser-check.py` expects of a picture of panels, as JSON, in the
shape PILean's own tests write for it: the cycle; at the middle of each key's rest every actor's
anchor in the composed still and every upright group's anchor where the plan draws it; every turn
with its centre, start, angle and the eased fraction done at a quarter, a half and three quarters
of it; each panel's box on the page; and the marked points of every actor at every rest and at
three points of every move (`phase`). -/
def browserExpectations (name : String) (r : Plane.MotionPanelsReport) : String := Id.run do
  let st := r.style
  let anchorOf := fun (pr : Plane.PanelReport) (fig : Plane.Figure) (id : String) =>
    (fig.actor? id).bind fun it => (it.leaves[0]?).bind fun lf =>
      (Plane.anchors pr.env.frame st lf.geom)[0]?
  let rests := (List.range r.figure.keyCount).map fun k =>
    let actors := r.panels.toList.flatMap fun pr =>
      let fig := pr.keys.figure k
      let still := pr.plan.layers.filter (·.geoms.isNone)
      let ids := (still.filterMap (·.version.actor)).toList.eraseDups.filter fig.hasActor
      ids.filterMap fun id => (anchorOf pr fig id).map fun a =>
        s!"\{\"id\": \"{pr.idPrefix}{Canvas.safeToken id}\", \"at\": {jsonPoint a}}"
    let t := Exact.toFloat (r.timeline.restTime k)
    let ups := ((r.markersAt t).filter (·.1 == "upright")).toList.map fun (_, q, _) =>
      jsonPoint q
    s!"\{\"key\": {k}, \"t\": {jsonNum t}, \"actors\": [{", ".intercalate actors}], " ++
      s!"\"uprights\": [{", ".intercalate ups}]}"
  let segs := r.timeline.segments
  let turns := r.panels.toList.flatMap fun pr =>
    let still := pr.plan.layers.filter (·.geoms.isNone)
    still.toList.flatMap fun L => match L.version.actor with
      | none => []
      | some id => L.links.toList.filterMap fun
        | .turn j c deg => do
          let i ← (List.range segs.size).find? fun i => (segs[i]?.map (·.kind)) == some (.move j)
          let s ← segs[i]?
          let start ← anchorOf pr (pr.keys.figure j) id
          let samples := [0.25, 0.5, 0.75].map fun (x : Float) =>
            let t := Exact.toFloat s.start + x * Exact.toFloat s.dur
            s!"\{\"t\": {jsonNum t}, " ++
              s!"\"f\": {jsonNum ((pr.plan.clock.splines.getD i .linear).eval x)}}"
          return s!"\{\"id\": \"{pr.idPrefix}{Canvas.safeToken id}\", \"step\": {j}, " ++
            s!"\"centre\": {jsonPoint c}, \"start\": {jsonPoint start}, " ++
            s!"\"sweep\": {jsonNum deg}, \"samples\": [{", ".intercalate samples}]}"
        | .slide .. => none
  let ups := r.panels.foldl (fun a pr => a + pr.plan.markerCounts.2) 0
  let panels := (r.panels.zip r.layout.places).toList.map fun (pr, place) =>
    s!"\{\"id\": \"{(pr.idPrefix.dropEnd 1).toString}\", \"box\": [{jsonNum place.x}, " ++
      s!"{jsonNum place.y}, {jsonNum place.frame.width}, {jsonNum place.frame.height}]}"
  let restTimes := (List.range r.figure.keyCount).map fun k =>
    Exact.toFloat (r.timeline.restTime k)
  let times := restTimes ++
    (segs.toList.filter fun s => match s.kind with | .move _ => true | _ => false).flatMap
      fun s => [0.25, 0.5, 0.75].map fun (x : Float) =>
        Exact.toFloat s.start + x * Exact.toFloat s.dur
  let phase := times.map fun t =>
    let actors := ((r.markersAt t).filter (·.1.startsWith "actor ")).toList.map
      fun (n, q, _) => s!"[\"{(n.drop 6).toString}\", {jsonPoint q}]"
    s!"\{\"t\": {jsonNum t}, \"actors\": [{", ".intercalate actors}]}"
  let marks := r.figure.panels.any fun p => turningMarks p.motion
  return s!"\{\"name\": \"{name}\", \"svg\": \"{name}.svg\", " ++
    s!"\"poster_png\": \"{name}-poster.png\", " ++
    s!"\"cycle\": {jsonNum (Exact.toFloat r.timeline.cycle)}, \"uprights\": {ups}, " ++
    s!"\"turning_marks\": {marks}, \"band\": {jsonNum r.layout.band}, " ++
    s!"\"rests\": [{", ".intercalate rests}], \"turns\": [{", ".intercalate turns}], " ++
    s!"\"panels\": [{", ".intercalate panels}], \"phase\": [{", ".intercalate phase}]}\n"

/-- The segments of a picture's timeline as JSON: each rest with its key, each move with its
step and what it does (`turn`, or the mark of a letter that does not act: `appear`, `vanish`),
with its start and duration in seconds. -/
def segmentsJson (c : Lift.FramePairConfig) (r : Plane.MotionPanelsReport) : String :=
  let phases := c.frameSteps.toArray.map (·.phase)
  let one := fun (s : Anim.Segment) =>
    let time := s!"\"start\": {jsonNum (Exact.toFloat s.start)}, " ++
      s!"\"duration\": {jsonNum (Exact.toFloat s.dur)}"
    match s.kind with
    | .rest k => s!"\{\"kind\": \"rest\", \"key\": {k}, {time}}"
    | .move j =>
      let kind := match phases.getD j .turn with
        | .turn => "turn" | .markAppears => "appear" | .markVanishes => "vanish"
      s!"\{\"kind\": \"{kind}\", \"step\": {j}, {time}}"
    | .seamIn => s!"\{\"kind\": \"seamIn\", {time}}"
    | .seamOut => s!"\{\"kind\": \"seamOut\", {time}}"
  "[" ++ ", ".intercalate (r.timeline.segments.toList.map one) ++ "]"

/-- The page of `--motion-variants`, with a marker where the data goes. -/
def motionPage : String := include_str "FramePairPreview.html"

/-- Whether the variant's loop is closed: its last key draws what its first does (in both panels
the same actors in order, of the same kinds and base titles at the same exact anchors; the ids
may differ, as a centre-graph edge's id names its key), so that the loop needs no reset. -/
def closedWord (c : Lift.FramePairConfig) : Bool :=
  let last := c.keyCount - 1
  [Lift.Panel.left, .right].all fun p =>
    let a := c.actorsAt p 0
    let b := c.actorsAt p last
    a.length == b.length && (a.zip b).all fun (x, y) =>
      x.kind == y.kind && x.base == y.base && x.anchors.length == y.anchors.length &&
        (x.anchors.zip y.anchors).all fun (p, q) => Lift.ZetaFrac.same p q

/-- One variant of `--motion-variants` written: its four SVGs (wide and narrow, light and dark)
in `dir/svg`, the files of the browser check for its light renditions in `dir/check`, and its
entry of `variants.json` with the SVG texts by file name; or the errors of the renditions that
the engine refused. -/
def renderMotionVariant (dir : System.FilePath) (c : Lift.FramePairConfig) :
    IO (Except (Array String) (String × Array (String × String))) := do
  let id := variantName c
  let renditions : Array (String × String × Plane.MotionPanels) :=
    let wide := c.motion
    let dark := c.motionWith Lift.canonicalPacing (dark := true)
    #[("wide", "", wide), ("wideDark", "-dark", dark)] ++
      (wide.narrow.map fun n => #[("narrow", "-narrow", n)]).getD #[] ++
      (dark.narrow.map fun n => #[("narrowDark", "-narrow-dark", n)]).getD #[]
  let mut errors : Array String := #[]
  let mut files : Array (String × String) := #[]
  let mut sizes : Array (String × Nat × Nat) := #[]
  let mut bytes : Array (String × Nat) := #[]
  let mut segments := "[]"
  for (key, suffix, P) in renditions do
    let r := P.report
    for n in r.problems do
      if n.severity == .note then IO.println s!"  note, {id}{suffix}: {n.message}"
    match r.svg? with
    | .error es => errors := errors ++ es.map (s!"{id}{suffix}: " ++ ·)
    | .ok svg =>
      let file := s!"svg/{id}{suffix}.svg"
      IO.FS.writeFile (dir / file) svg
      files := files.push (file, svg)
      sizes := sizes.push (key, r.pixelSize)
      bytes := bytes.push (key, svg.utf8ByteSize)
      if key == "wide" then segments := segmentsJson c r
      if suffix == "" || suffix == "-narrow" then
        let name := id ++ suffix
        IO.FS.writeFile (dir / "check" / s!"{name}.svg") svg
        for k in [0:P.keyCount] do
          IO.FS.writeFile (dir / "check" / s!"{name}-key{k}.svg") (r.keyStillSvg k)
        IO.FS.writeBinFile (dir / "check" / s!"{name}-poster.png")
          ((r.keyStillPng P.poster).getD .empty)
        IO.FS.writeFile (dir / "check" / s!"{name}.json") (browserExpectations name r)
  if !errors.isEmpty then return .error errors
  let right := match c.right with | .bodies => "R1" | .centres => "R2" | .bodiesGraph => "R3"
  let view := match c.view with
    | .shared => "shared" | .cropped => "cropped" | .wideRight => "wideRight"
  let idle := match c.idleMark with | .outline => "outline" | .ring => "ring"
  let left := match c.left with | .halved => "halved" | .full => "full"
  let trails := if !c.trails then "none"
    else match c.trailLength with | some n => s!"last {n}" | none => "full"
  let obj := fun (xs : List String) => "{" ++ ", ".intercalate xs ++ "}"
  let entry := obj [s!"\"id\": {jsonString id}", s!"\"word\": {jsonString c.wordText}",
    s!"\"title\": {jsonString c.motion.info.title}",
    s!"\"closed\": {closedWord c}",
    "\"options\": " ++ obj [s!"\"right\": \"{right}\"", s!"\"trails\": \"{trails}\"",
      s!"\"view\": \"{view}\"", s!"\"idle\": \"{idle}\"", s!"\"left\": \"{left}\""],
    "\"steps\": [" ++ ", ".intercalate (c.frameSteps.map fun s =>
      s!"\{\"letter\": {jsonString s.letter.text}, \"acts\": {s.acts}}") ++ "]",
    s!"\"letters\": {c.word.length}",
    s!"\"trailLength\": {match c.trailLength with | some n => toString n | none => "null"}",
    s!"\"segments\": {segments}",
    "\"captions\": [" ++ ", ".intercalate ((List.range c.keyCount).map fun k =>
      jsonString (c.keyCaption k)) ++ "]",
    "\"size\": " ++ obj (sizes.toList.map fun (k, w, h) => s!"\"{k}\": [{w}, {h}]"),
    "\"bytes\": " ++ obj (bytes.toList.map fun (k, n) => s!"\"{k}\": {n}"),
    "\"files\": " ++ obj (files.toList.map fun (f, _) =>
      let key := if f.endsWith "-narrow-dark.svg" then "narrowDark"
        else if f.endsWith "-narrow.svg" then "narrow"
        else if f.endsWith "-dark.svg" then "wideDark" else "wide"
      s!"\"{key}\": {jsonString f}")]
  return .ok (entry, files)

/-- Writes the variants of the animated frame pair (`motionVariants`) into `dir`: one standalone
animated SVG per variant and rendition at the canonical pacing (`Lift.canonicalPacing`) in
`dir/svg`, the files of PILean's browser check in `dir/check`, `variants.json`, and `index.html`,
a page that plays the variants re-timed and writes the chosen values as Lean. Returns the
messages of the variants the engine refused (an error under `checks := .fail`). -/
def writeMotionVariants (dir : System.FilePath) : IO (Array String) := do
  IO.FS.createDirAll (dir / "svg")
  IO.FS.createDirAll (dir / "check")
  let mut entries : Array String := #[]
  let mut svgs : Array (String × String) := #[]
  let mut errors : Array String := #[]
  for c in motionVariants do
    let t0 ← IO.monoMsNow
    match ← renderMotionVariant dir c with
    | .error es =>
      errors := errors ++ es
      IO.println s!"{variantName c}: {es.size} errors"
    | .ok (entry, files) =>
      entries := entries.push entry
      svgs := svgs ++ files
      let sizes := ", ".intercalate (files.toList.map fun (f, s) => s!"{f} {s.utf8ByteSize} B")
      IO.println s!"{variantName c}: no errors ({(← IO.monoMsNow) - t0} ms); {sizes}"
  let variants := "[\n" ++ ",\n".intercalate entries.toList ++ "\n]\n"
  IO.FS.writeFile (dir / "variants.json") variants
  let svgObj := "{" ++ ",\n".intercalate (svgs.toList.map fun (f, s) =>
    s!"{jsonString f}: {jsonString s}") ++ "}"
  let data := s!"window.FRAME_PAIR_DATA = \{\"variants\": {variants}, \"svgs\": {svgObj}};"
  IO.FS.writeFile (dir / "index.html") (motionPage.replace "/*@DATA@*/" data)
  return errors

end TDCSGFigures.Preview

open PILean TDCSGFigures.Preview in
/-- Renders the previews (see the module docstring). -/
def main (args : List String) : IO UInt32 := do
  if let ["--motion-variants", dir] := args then
    let errors ← writeMotionVariants dir
    for e in errors do IO.println s!"  {e}"
    IO.println s!"wrote {dir}/index.html; {errors.size} errors"
    return if errors.isEmpty then 0 else 1
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
