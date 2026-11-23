/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import TDCSGFigures.Data
import TDCSGFigures.Style
import TDCSGFigures.Front

/-!
# The figures of the blueprint

Every figure of the site is the value of a declaration with the attribute `@[figure]`, drawn by
PILean from exact data (`TDCSGFigures.Data`) in the house style (`TDCSGFigures.Style`), one module
per page: `TDCSGFigures.Front` for the front page. The library needs neither Mathlib nor Verso.
-/
