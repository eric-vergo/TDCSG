/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5.2
-/
import PILean

/-!
# The house style of the figures

The figures are diagrammatic: disks are outlines, the lens where two disks overlap is a filled
region of its own, the pieces of a chord have distinct colours with their labels beside them, and
every point, disk, centre, radius and region carries a label.

Colours are named roles of the style (`PILean.PlaneRole`), each with a light and a dark value, so
that a page in its dark theme shows the dark values, not an inverted picture. The left disk and
everything that belongs to it (its centre, its radius, the points on its circle, the weight-zero
labels) take the role `left`; the right disk and what belongs to it take `right`. The two are the
Okabe–Ito blue and vermilion, a pair that stays apart under the common colour-vision deficiencies;
the light values are darkened enough for labels on white and on the tint of the lens, the dark
values lightened for the dark page. The style keeps PILean's default light colours
(`Style.light`) beside its roles, so it has a dark twin (`Style.darkTwin?`) and inline pictures
follow the page's theme.

## Main definitions

* `houseStyle`, the role names `leftRole`, `rightRole`, `lensRole`, `pieceRole`.
* `figureWidth`, `narrowWidth`: the page widths of a figure and of its narrow rendition.
-/

namespace TDCSGFigures

open PILean PILean.Plane

/-- The role of the left disk and of everything that belongs to it. -/
def leftRole : String := "left"

/-- The role of the right disk and of everything that belongs to it. -/
def rightRole : String := "right"

/-- The role of the lens, the intersection of the two disks. -/
def lensRole : String := "lens"

/-- The role of the piece of the chord that word `i` (1, 2 or 3) moves. -/
def pieceRole (i : Nat) : String := s!"piece{i}"

/-- The roles of the house style with their light and dark colours. -/
def roles : Array PlaneRole := #[
  -- Okabe–Ito blue `#0072B2`, darkened for labels on the lens; sky blue `#56B4E9` on the dark
  -- page.
  ⟨leftRole, ⟨0, 98, 158, 255⟩, ⟨86, 180, 233, 255⟩⟩,
  -- Okabe–Ito vermilion `#D55E00`, darkened likewise; lightened on the dark page.
  ⟨rightRole, ⟨166, 62, 0, 255⟩, ⟨247, 146, 86, 255⟩⟩,
  -- A violet for the region the two disks share.
  ⟨lensRole, ⟨104, 84, 164, 255⟩, ⟨190, 172, 240, 255⟩⟩,
  -- The pieces of the three words: bluish green, ochre and reddish purple.
  ⟨pieceRole 1, ⟨0, 108, 80, 255⟩, ⟨72, 206, 164, 255⟩⟩,
  ⟨pieceRole 2, ⟨120, 92, 0, 255⟩, ⟨226, 192, 72, 255⟩⟩,
  ⟨pieceRole 3, ⟨168, 50, 120, 255⟩, ⟨236, 140, 200, 255⟩⟩]

/-- The house style: PILean's light colours with the roles above, lines of 2 pixels, markers of
radius 4 with a halo of 2, labels of 15 pixels. -/
def houseStyle : Style :=
  { Style.light with plane := { PlaneStyle.light with
      lineWidth := 2, markerRadius := 4, markerRing := 2, labelSize := 15, roles } }

/-- The width of a figure's page, in pixels: about the width of the text column. -/
def figureWidth : Float := 600

/-- The width of a figure's narrow rendition, for screens up to 560 pixels wide. -/
def narrowWidth : Float := 340

end TDCSGFigures
