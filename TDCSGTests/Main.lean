/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGCompute.SelfTest
import TDCSGTests.FrameWords

/-!
# The test driver

`lake test` builds this executable, and with it the pins of `TDCSGTests.FrameWords` (checked by
the kernel when the module is built), and runs the self-tests of the orbit engine
(`TDCSGCompute.runSelfTests`).
-/

/-- Runs the self-tests of the orbit engine. -/
def main : IO UInt32 := TDCSGCompute.runSelfTests
