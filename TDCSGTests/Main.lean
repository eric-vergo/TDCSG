/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGCompute.SelfTest
import TDCSGTests.FrameWords
import TDCSGTests.FramePair
import TDCSGTests.Motions

/-!
# The test driver

`lake test` builds this executable, and with it the pins of `TDCSGTests.FrameWords`,
`TDCSGTests.FramePair` and `TDCSGTests.Motions` (checked by the kernel, and the `#guard` lines by
evaluation, when the modules are built), and runs the self-tests of the orbit engine
(`TDCSGCompute.runSelfTests`) and PILean's engine on every animation of the site
(`TDCSGTests.Motions.engineErrors`), compiled.
-/

/-- Runs the self-tests of the orbit engine and requires that PILean's engine finds no error in
any animation of the site (`TDCSGTests.Motions.engineErrors`). -/
def main : IO UInt32 := do
  let code ← TDCSGCompute.runSelfTests
  let errors := TDCSGTests.Motions.engineErrors
  for e in errors do IO.eprintln e
  IO.println s!"animations: {TDCSGTests.Motions.siteMotions.size} checked by PILean's engine, \
    {errors.length} errors"
  return if errors.isEmpty then code else 1
