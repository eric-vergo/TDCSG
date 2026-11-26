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

An animation (a `PILean.Plane.MotionPanels`) is written as its animated SVG in the light style and
its dark twin, the still of each key (`NAME-key-K.{svg,png}`), and the same for its narrow
rendition (`NAME-narrow…`); its problems are those of its report (`MotionPanels.report`), and
its notes are printed but do not count.

`tdcsg-figure-preview --frame-pair WORD [--radius P/Q] [--pivot] [--faint] [--out DIR]` writes the
frame pair of chapter 4 for another word (letters `a`, `b`, `A = a⁻¹`, `B = b⁻¹`;
`TDCSGFigures.Lift.FramePairConfig`), radius, with the turn centres marked (`pivotMark`) or the
riding disks faint (`faintDisks`), as `DIR/framePair-WORD[-rP_Q][-pivot][-faint]…`, and prints
whether every declared move arrives exactly (`FramePairConfig.allArrive`).
-/

namespace TDCSGFigures.Preview

open PILean

/-- What a preview shows: a plane figure, the frames of an explorer of plane figures as its
slider or stepper shows them (one view for all, `Plane.commonView`), a plot, or an animation. -/
inductive Entry where
  /-- A plane figure. -/
  | plane (fig : Plane.Figure)
  /-- The frames of an explorer, with their value or step labels. -/
  | frames (figs : Array (String × Plane.Figure))
  /-- A plot. -/
  | plot (fig : Plot.Figure)
  /-- An animation of plane figures as panels on one clock. -/
  | motion (P : Plane.MotionPanels)

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
  ("wordLoop1", .motion wordLoop1),
  ("wordLoop2", .motion wordLoop2),
  ("wordLoop3", .motion wordLoop3),
  ("exchangedIntervals", .plane exchangedIntervals),
  ("coordinateBox", .plane coordinateBox),
  ("radiusThreshold", .plane radiusThreshold),
  ("chordOrbit", .plane chordOrbit),
  ("orderEight", .plane orderEight),
  ("orderTen", .plane orderTen),
  ("orderTwelve", .plane orderTwelve),
  ("unitSteps", .plane Lift.unitSteps),
  ("framePair", .motion Lift.framePair),
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

/-- Writes the animation `P` as `stem…` in `dir` (see the module docstring) and returns its
errors and those of its narrow rendition; prints its notes. -/
def renderMotion (dir : System.FilePath) (stem : String) (P : Plane.MotionPanels) :
    IO (Array String) := do
  let renditions := #[("", P)] ++ (P.narrow.map ("-narrow", ·)).toArray
  let mut errors := #[]
  for (suffix, Q) in renditions do
    let r := Q.report
    for p in r.problems do
      if p.severity == .note then IO.println s!"  note{suffix}: {p.message}"
      else errors := errors.push s!"{suffix}: {p.message}"
    let dark := r.style.darkTwin?.map Q.withStyle
    for (theme, R) in #[("", some Q), ("-dark", dark)] do
      if let some R := R then
        if let .ok svg := R.report.svg? then
          IO.FS.writeFile (dir / s!"{stem}{suffix}{theme}.svg") svg
    for k in [0:Q.keyCount] do
      IO.FS.writeFile (dir / s!"{stem}{suffix}-key-{k}.svg") (r.keyStillSvg k)
      if let some png := r.keyStillPng k then
        IO.FS.writeBinFile (dir / s!"{stem}{suffix}-key-{k}.png") png
  return errors

end TDCSGFigures.Preview

/-- The options of `--frame-pair WORD`: `--radius P/Q` (a rational radius), `--pivot` (the turn
centres marked), `--faint` (the riding disks faint) and `--out DIR`, in any order. -/
def framePairOptions (args : List String) :
    Except String ((Option Rat × Bool × Bool) × System.FilePath) :=
  go args ((none, false, false), "out")
where
  /-- The options read so far. -/
  go : List String → (Option Rat × Bool × Bool) × System.FilePath →
      Except String ((Option Rat × Bool × Bool) × System.FilePath)
    | [], acc => .ok acc
    | "--pivot" :: rest, ((r, _, f), d) => go rest ((r, true, f), d)
    | "--faint" :: rest, ((r, p, _), d) => go rest ((r, p, true), d)
    | "--out" :: d :: rest, (o, _) => go rest (o, d)
    | "--radius" :: q :: rest, ((_, p, f), d) =>
      match q.splitOn "/" with
      | [a, b] => match a.toNat?, b.toNat? with
        | some a, some b@(_ + 1) => go rest ((some ((a : Rat) / b), p, f), d)
        | _, _ => .error s!"--radius {q}: expected P/Q with natural numbers P and Q > 0"
      | _ => .error s!"--radius {q}: expected P/Q"
    | a :: _, _ => .error s!"unknown option {a}"

open PILean TDCSGFigures.Preview in
/-- Renders the previews (see the module docstring). -/
def main (args : List String) : IO UInt32 := do
  if let "--frame-pair" :: word :: rest := args then
    let (opts, dir) ← IO.ofExcept (framePairOptions rest)
    IO.FS.createDirAll dir
    let w ← IO.ofExcept (TDCSGFigures.Lift.parseWord word)
    let c : TDCSGFigures.Lift.FramePairConfig :=
      { word := w, radius := opts.1.getD TDCSGFigures.Lift.radius, pivotMark := opts.2.1,
        faintDisks := opts.2.2 }
    let stem := s!"framePair-{word}" ++ (opts.1.map fun q => s!"-r{q.num}_{q.den}").getD "" ++
      (if opts.2.1 then "-pivot" else "") ++ (if opts.2.2 then "-faint" else "")
    let errors ← renderMotion dir stem c.motion
    for e in errors do IO.println s!"  {e}"
    IO.println s!"{stem}: {c.keyCount} keys, {errors.size} errors, exact arrival \
      {c.allArrive}; wrote {dir}"
    return if errors.isEmpty && c.allArrive then 0 else 1
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
    if let .motion P := entry then
      let ps ← renderMotion dir name P
      IO.println s!"{name}: animation, {P.keyCount} keys, {ps.size} errors"
      for p in ps do IO.println s!"  {p}"
      problems := problems + ps.size
      continue
    let figs : Array (String × Plane.Figure) := match entry with
      | .plot _ | .motion _ => #[]
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
