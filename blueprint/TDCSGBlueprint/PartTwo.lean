/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Part II — Finite below the threshold" =>

%%%
tag := "part-finite"
file := "Part-II"
number := false
%%%

Part II proves the other half of the main theorem: for every radius $`r<\sqrt{3+\varphi}` the
group $`GG_5(r)` is finite. It consists of Chapters 4 to 7, and Chapter 8 joins the two halves.

By the finiteness criterion of Chapter 1 it suffices to bound all orbits by one number. The
argument has four steps, one per chapter.

* *Lift to integer labels* (Chapter 4). Following a point along a word, record the disk centers
  that act on it by integer vectors in $`\mathbb Z^5`. Words become walks in a graph on these
  labels, and each orbit point is determined by the final label of its walk together with one of
  finitely many choices of center and direction.
* *The lens estimate* (Chapter 5). Two disks of radius $`r/2` whose centers are at distance one
  overlap in a lens. Below the threshold the lens ends strictly before a fixed vertical line, with
  a margin of at least $`(3+\varphi-r^2)/16`.
* *Good levels* (Chapter 6). The margin gives integer levels of each coordinate at which every
  crossing edge of the label graph ends at a leaf. Good levels recur within a bounded distance,
  uniformly in the starting point, because $`\varphi` is irrational.
* *Confinement* (Chapter 7). A walk can cross a good level only to step onto a leaf and back, so
  every reachable label lies in a box independent of the starting point. Hence every orbit is
  contained in the images of one finite set, and the group is finite.

The margin of the lens estimate vanishes at the threshold. That is where this half stops, and
where Part I takes over.
