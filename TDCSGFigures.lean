/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import TDCSGFigures.Data
import TDCSGFigures.Style
import TDCSGFigures.Front
import TDCSGFigures.Data.Early
import TDCSGFigures.Compound
import TDCSGFigures.TwoDisks
import TDCSGFigures.Parts
import TDCSGFigures.Chord
import TDCSGFigures.OtherOrders
import TDCSGFigures.Lift
import TDCSGFigures.Lens
import TDCSGFigures.Levels
import TDCSGFigures.Confinement

/-!
# The figures of the blueprint

Every figure of the site is the value of a declaration with the attribute `@[figure]`, drawn by
PILean from exact data (`TDCSGFigures.Data`, `TDCSGFigures.Data.Early`,
`TDCSGFigures.Data.PartTwo`) in the house style (`TDCSGFigures.Style`), one module per page:
`TDCSGFigures.Front` for the front page, `TDCSGFigures.Compound` and `TDCSGFigures.TwoDisks` for
chapters 1 and 2, `TDCSGFigures.Parts` for the two part dividers, `TDCSGFigures.Chord` for
chapter 3, `TDCSGFigures.Lift`, `TDCSGFigures.Lens`, `TDCSGFigures.Levels` and
`TDCSGFigures.Confinement` for chapters 4 to 7, and `TDCSGFigures.OtherOrders` for chapter 9. The
library needs neither Mathlib nor Verso.
-/
