/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures
import PILeanTest.MotionPanels

/-!
# What the browser checks of the animations expect

`tdcsg-motion-out DIR` writes, for each animation of the site and for its narrow rendition, the
files that PILean's browser checks read, named by the declaration (`TDCSGFigures.wordLoop1`, with
`-narrow` for the narrow rendition, when the animation has one): the animated SVG, the still of each key (`-key<k>.svg`), the
poster key's PNG (`-poster.png`), and the expectations (`.json`), written by PILean's own writer
`PILeanTest.MotionPanelsChecks.expectations` from the motion's report: at every rest each actor's
anchor in the key's still, every turn with its centre, start, angle and the eased fraction done at
a quarter, a half and three quarters of it, each panel's box, and every actor's position at every
rest and at three points of every move, so that a check can tell that the panels are in phase.

`scripts/check-motion.py` reads the folder: PILean's `tools/motion-browser-check.py` checks the
standalone files, and PILean's `motion_browser.py` checks the moving pictures of the built site
against the same expectations.
-/

open PILean PILean.Plane TDCSGFigures

/-- The animations of the site, with the names of their files in the site: the declaration's name,
without the name of its module where the module's name begins it (`walkToLeaf`, declared in
`TDCSGFigures.Confinement`). -/
def motions : Array (String × MotionPanels) := #[
  ("TDCSGFigures.wordLoop1", wordLoop1),
  ("TDCSGFigures.wordLoop2", wordLoop2),
  ("TDCSGFigures.wordLoop3", wordLoop3),
  ("TDCSGFigures.Lift.framePair", Lift.framePair),
  ("TDCSGFigures.extensionJump", extensionJump),
  ("TDCSGFigures.disjointDisks", disjointDisks),
  ("TDCSGFigures.generatorStep", generatorStep),
  ("TDCSGFigures.wordSteps", wordSteps),
  ("TDCSGFigures.exchangedIntervals", exchangedIntervals),
  ("TDCSGFigures.chordOrbit", chordOrbit),
  ("walkToLeaf", Confinement.walkToLeaf)]

/-- Writes the files of `P` and of its narrow rendition into `dir`. -/
def writePanels (dir : System.FilePath) (name : String) (P : MotionPanels) : IO Unit := do
  let all := #[(name, P)] ++ (P.narrow.map fun n => #[(name ++ "-narrow", n)]).getD #[]
  for (file, Q) in all do
    let r := Q.report
    IO.FS.writeFile (dir / s!"{file}.svg") r.toSvgUnchecked
    for k in [0:Q.keyCount] do
      IO.FS.writeFile (dir / s!"{file}-key{k}.svg") (r.keyStillSvg k)
    IO.FS.writeBinFile (dir / s!"{file}-poster.png") ((r.keyStillPng Q.poster).getD .empty)
    IO.FS.writeFile (dir / s!"{file}.json") (PILeanTest.MotionPanelsChecks.expectations file r)

/-- Writes the files of every animation into the folder given (see the module docstring). -/
def main (args : List String) : IO UInt32 := do
  let [dir] := args | do
    IO.eprintln "usage: tdcsg-motion-out DIR"
    return 2
  IO.FS.createDirAll dir
  for (name, P) in motions do
    writePanels dir name P
    IO.println s!"{name}: {P.keyCount} keys"
  IO.println s!"motion files written to {dir}"
  return 0
