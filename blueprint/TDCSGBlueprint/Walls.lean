/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.FiveSharp

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "A crossing with nowhere to go" =>

%%%
tag := "walls"
%%%

![Four candidate unit edges from the red leaf end outside the blue window. The horizontal edge leads to the only retained neighbor.](/figures/terminal.svg)

A wall is a level of an integer coordinate, not a line in the projected disk. Crossing the
$`j`th wall changes $`n_j` by one. The figure isolates the local effect: one endpoint has only
the crossing edge left. In this illustration $`x=0.87` and $`r=1.8`. Gray spokes mark rejected
candidates. The theorem chooses walls for arbitrary windows and both sides of each coordinate.

![Phases at integer levels plotted modulo the period. The selected levels minus ten and three land in the shaded bands near a half-period.](/figures/levels.svg)

For the same window in direction zero, each dot gives the phase of an integer level, reduced
to the interval from minus to plus half a period. The two shaded bands are the allowed phases.
The levels $`-10` and $`3` land there, outside the initial labels on opposite sides.
The following argument finds such a pair without searching separately for each window.

:::lemma_ "irrational_levels" (lean := "TDCSG.Five.Walls.exists_levels")
For $`L>0`, $`\eta>0` and irrational $`\alpha/L`, choose levels $`m` on opposite sides of the
initial labels so that $`|\alpha m+b+Lp|>L/2-\eta` for every integer $`p`. Their absolute
values have a common bound independent of the phase $`b`.
:::

:::proof "irrational_levels"
On the circle of circumference $`L`, the multiples of $`\alpha` are dense. For each initial
phase some multiple carries it close to the half-period. These open sets cover the compact
circle. A finite subcover bounds the necessary adjustment to any proposed positive or negative
level, uniformly over the phase.
:::

:::lemma_ "terminal_crossing" (lean := "TDCSG.Five.Walls.leaf_of_level") (uses := "sharp_lens, irrational_levels")
At a selected level, any retained crossing has a leaf endpoint. At that endpoint every
alternative direction fails its closed-window test.
:::

:::proof "terminal_crossing"
Rotate by the inverse crossing direction. The midpoint's horizontal coordinate has the form
$`(1-d)m+b+Lp`. The ratio $`(1-d)/L` equals $`\varphi`, so one of the two orientations places
an endpoint in the region excluded by the sharp lens estimate.
:::

:::theorem "all_walls" (lean := "TDCSG.Five.Walls.exists_walls") (uses := "terminal_crossing")
For fixed subcritical radius, each bounded window admits a lower and an upper wall in each
of the five coordinates. A single integer bounds all the chosen wall levels.
:::
