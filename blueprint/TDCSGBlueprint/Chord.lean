/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.FiveSharp

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "An infinite orbit at the endpoint" =>

%%%
tag := "chord"
%%%

![Four successive marked positions on copies of the chord from minus E to E. The points follow a rotation modulo two, starting at zero.](/figures/chord.svg)

Set $`E=\zeta-\zeta^2` and write points on the chord as $`tE` with $`-1\le t\le1`.
The picture shows successive returns to the chord, one entire word per step. Intermediate
rotations within a word may leave the chord. At $`R` three words fit the closed disks exactly.
They continue to work at every larger radius.

:::definition "chord_check" (lean := "TDCSG.Five.pointE, TDCSG.Five.word₁, TDCSG.Five.word₂, TDCSG.Five.word₃") (uses := "disk_rotation")
Partition the chord at $`1-\varphi` and $`3-2\varphi`. Each of the three resulting subsegments
uses its own finite word. Write $`a` for the left turn and $`b` for the right turn.
In order from the left piece to the right piece, the words are
$`a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}`, $`ababb`, and $`abab^{-1}a^{-1}b^{-1}`.
Apply their letters from left to right.
:::

:::lemma_ "word_action" (lean := "TDCSG.Five.applyWord_chord, TDCSG.Five.applyWord_word₁, TDCSG.Five.applyWord_word₂, TDCSG.Five.applyWord_word₃") (uses := "chord_check")
On the first two pieces the parameter increases by $`2\varphi-2`; on the third it changes by
$`2\varphi-4`. At a common endpoint choose either valid piece. Modulo two the displacement
is always $`2/\varphi`.
:::

:::proof "word_action"
The certificates calculate each intermediate image of both endpoints in the cyclotomic integer
ring. The checked disk inequalities extend from the endpoints to the full segment by convexity.
The affine rotation formulas then carry the entire segment to the claimed translate.
:::

:::theorem "endpoint_infinite" (lean := "TDCSG.Five.exists_mem_orbit, TDCSG.CriticalRadius.infinite_orbit_zero_five") (uses := "word_action")
For each natural number $`k` the orbit of zero contains a point $`t_k E`, where
$`t_k\equiv k(2\varphi-2)\pmod{2}`. Distinct indices produce distinct parameters by
irrationality, and $`E\ne0`. Hence the orbit is infinite at every $`r\ge R`.
:::

:::theorem "classification" (lean := "TDCSG.CriticalRadius.finite_GG_five_iff, TDCSG.CriticalRadius.criticalRadius_five_eq, TDCSG.CriticalRadius.sSup_finiteRadii_five") (uses := "subcritical, endpoint_infinite")
The fivefold group is finite exactly for $`r<R`. The supremum of the finite radii and the
infimum of the infinite radii both equal $`R`. The group at their common boundary is infinite.
:::
