/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.OrbitLoop
import TDCSGFigures.LensLoop

/-!
# The variants of the two loops that would replace the sliders

The looks to choose from for the orbit of `0` as the radius grows (`OrbitLoop`) and for the lens
as the radius grows to `R` (`Lens.LensLoopConfig`), each with the exact checks of its data. None of
them is a figure of the site; `tdcsg-figure-preview --variants DIR` writes them, and
`tdcsg-motion-out --variants DIR` writes what the browser checks of their files read.
-/

namespace TDCSGFigures.LoopVariants

open PILean PILean.Plane TDCSGFigures OrbitLoop Lens

/-- The variants, by name, with whether their exact checks hold. -/
def variants : Array (String × MotionPanels × Bool) := #[
  ("orbitGrowthSix", growthSix.motion, growthSix.nested && growthSix.arrives),
  ("orbitDepthPair", depthPair.motion, depthPair.enough && depthPair.arrives),
  ("orbitGrowthFive", growthFive.motion, growthFive.nested && growthFive.arrives),
  ("lensMorph", lensMorph.motion, lensMorph.keyFacts),
  ("lensFade", lensFade.motion, lensFade.keyFacts)]

end TDCSGFigures.LoopVariants
