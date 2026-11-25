/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import VersoManual
import VersoBlueprint
import PILeanVerso
import TDCSGFigureTheorems

open Verso.Genre Verso.Genre.Manual Informal PILeanVerso

#doc (Manual) "Part I — Infinite at the threshold" =>

%%%
tag := "part-infinite"
file := "Part-I"
number := false
%%%

Part I proves the half of the main theorem that holds at and above the threshold: for every
radius $`r\ge\sqrt{3+\varphi}` the group $`GG_5(r)` is infinite. It consists of Chapter 3.

:::figure TDCSGFigures.radiusLineInfinite (label := "radius-line-infinite") (inline := true) (links := TDCSGFigures.radiusLineInfinite_spec) (alt := "A line of radii with the critical radius R marked between 2 and 3. Above, the finite half ends in an open ring at R; below, the infinite half starts with a filled dot at R and is drawn thick.")
The radii $`r` with the critical radius $`R=\sqrt{3+\varphi}\approx2.149` marked. The group
$`GG_5(r)` is finite for $`r<R`, the upper half-line, which ends in an open ring because $`R` is not
one of its radii, and infinite for $`r\ge R`, the lower half-line, which starts with a filled dot at
$`R`. Part I proves the infinite half, drawn thick.
:::

The proof is explicit. A chord through zero, joining two points of the boundary circles at the
threshold, is cut into three pieces, and on each piece one fixed word in the generators acts as a
translation along the chord. Parametrize the chord by $`t\in[-1,1]`. Together the three words
change $`t` by $`2/\varphi` modulo $`2`, an irrational rotation of a circle, so the orbit of zero
contains infinitely many points. Every disk test of the three words holds at the threshold, some with
equality, and therefore at every larger radius. This half shows that the bound of Part II cannot
be extended to the threshold itself.
