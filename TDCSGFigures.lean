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
import TDCSGFigures.FramePair
import TDCSGFigures.FramePairMotion
import TDCSGFigures.Lens
import TDCSGFigures.Levels
import TDCSGFigures.Confinement
import TDCSGFigures.ProofDiagrams
import TDCSGFigures.OrbitLoop

/-!
# The figures of the blueprint

Every figure of the site is the value of a declaration with the attribute `@[figure]`, drawn by
PILean from exact data (`TDCSGFigures.Data`, `TDCSGFigures.Data.Early`,
`TDCSGFigures.Data.PartTwo`, `TDCSGFigures.Data.Frames`) in the house style
(`TDCSGFigures.Style`), organized by chapter:
`TDCSGFigures.Front` for the front page, `TDCSGFigures.Compound` and `TDCSGFigures.TwoDisks` for
chapters 1 and 2, `TDCSGFigures.Parts` for the two part dividers, `TDCSGFigures.Chord` for
chapter 3, `TDCSGFigures.Lift`, `TDCSGFigures.Lens`, `TDCSGFigures.Levels` and
`TDCSGFigures.Confinement` for chapters 4 to 7, and `TDCSGFigures.OtherOrders` for chapter 9.
`TDCSGFigures.ProofDiagrams` draws the interval exchange, the coordinate bounds and the
classification at the critical radius. `TDCSGFigures.FramePair` holds the key figures of the two
frames of chapter 4, and `TDCSGFigures.FramePairMotion` animates them as two panels on one clock
(`TDCSGFigures.Lift.framePair`, an animation of the site). `TDCSGFigures.Data.Moves` holds the
exact moves of the other animations and their exact arrival check. An animation that replaced a
figure with a linked theorem ends on that figure and keeps the theorem; the others are marked
`@[figure illustration]`, and the data of the key frames of all of them are stated on the page of
the figures' theorems. The library needs neither
Mathlib nor Verso. The specification theorem `<name>_spec` of each figure,
which writes out what it draws, is stated and proved on the blueprint's page of the figures'
theorems, `TDCSGFigureTheorems`, and attached to the figure there.
-/
