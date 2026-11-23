/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoManual
import VersoBlueprint
import TDCSG.CriticalRadius.Five

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "The chord and its three words" =>

%%%
tag := "chord"
%%%

This chapter makes up Part I. It proves that $`GG_5(r)` is infinite for every $`r\ge R`, where
$`R=\sqrt{3+\varphi}`. This is the half of the main theorem that holds at and above the
threshold, and it shows that the finiteness of Part II cannot extend to $`R` itself. Write
$`\zeta=\exp(2\pi i/5)`.

![Four copies of the chord from minus E to E, one per step, each marking the current point. Dashed cuts divide the chord into the pieces of the three words.](/figures/chord.svg)
*Figure 3.* The returns $`t_0E,\ldots,t_3E` of the orbit of zero to the chord, one row per step, on the parameter line $`t\mapsto tE` from $`-E` (on the right circle) to $`E` (on the left circle). The dashed cuts at $`t=1-\varphi` and $`t=3-2\varphi` separate the pieces of the three words; the word named between two rows is the one applied to the upper point. Each step adds $`2\varphi-2` modulo two.

Set $`E=\zeta-\zeta^2` and write points on the chord as $`tE` with $`-1\le t\le1`.
The picture shows successive returns to the chord, one entire word per step. Intermediate
rotations within a word may leave the chord. At $`R` every disk test of the three words holds, some with equality.
They continue to work at every larger radius.

:::definition "chord_check" (lean := "TDCSG.Five.pointE, TDCSG.Five.word₁, TDCSG.Five.word₂, TDCSG.Five.word₃")
Cut the parameter range $`[-1,1]` at $`t=1-\varphi` and $`t=3-2\varphi`, that is, the chord at
the points $`(1-\varphi)E` and $`(3-2\varphi)E`. Each of the three resulting subsegments
uses its own finite word in the generators $`a` and $`b`.
In order from the left piece to the right piece, the words are
$`a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}`, $`ababb`, and $`abab^{-1}a^{-1}b^{-1}`.
Apply their letters from left to right.
:::

:::lemma_ "word_action" (lean := "TDCSG.Five.applyWord_chord, TDCSG.Five.applyWord_word₁, TDCSG.Five.applyWord_word₂, TDCSG.Five.applyWord_word₃") (uses := "disk_rotation, chord_check")
Let $`r\ge R`. The first word sends $`tE` to $`(t+2\varphi-2)E` for $`-1\le t\le1-\varphi`, and the
second does the same for $`1-\varphi\le t\le3-2\varphi`. The third sends $`tE` to
$`(t+2\varphi-4)E` for $`3-2\varphi\le t\le1`. Modulo two the displacement is always
$`2\varphi-2=2/\varphi`.
:::

:::proof "word_action" (lean := "TDCSG.Five.norm_embed_pointE_add_one_sq, TDCSG.applyWord_segment")
Every intermediate image of both endpoints of each piece is computed exactly, as an integer
vector in the basis $`1,\zeta,\zeta^2,\zeta^3`. Before each letter both current endpoints are
checked to lie in that letter's closed disk at radius $`R`, hence at every larger radius; at
$`R` the point $`E` lies on the left boundary circle, since $`|E+1|^2=3+\varphi`. A disk is
convex, so the letter then acts on the whole current segment as one rotation. The final
endpoints are the claimed translates, and the composite of rotations is the translation between
them. The kernel decides every check.
:::

:::theorem "threshold_infinite" (lean := "TDCSG.Five.exists_mem_orbit, TDCSG.Five.infinite_orbit_zero, TDCSG.Five.infinite_GG") (uses := "word_action, infinite_of_orbit, generated_by_two")
Let $`r\ge R`. For each natural number $`k` the orbit of zero contains a point $`t_kE` with
$`-1\le t_k<1` and $`t_k\equiv k(2\varphi-2)\pmod{2}`. The orbit of zero is infinite, and so is
$`GG_5(r)`.
:::

:::proof "threshold_infinite"
Every letter of a word is a generator or the inverse of one, hence an element of $`GG_5(r)`, so
each word maps the orbit of zero into itself. Start from $`t_0=0`. Given $`t_k`, apply the first word if $`t_k\le1-\varphi`, the second if
$`1-\varphi<t_k<3-2\varphi`, and the third if $`t_k\ge3-2\varphi`. The result stays in $`[-1,1)`
and changes $`t_k` by $`2\varphi-2` modulo two. If $`t_k=t_l`, then $`(k-l)(2\varphi-2)` is an even integer, which
forces $`k=l` because $`\varphi` is irrational. The points $`t_kE` are distinct since $`E\ne0`.
An infinite orbit forces an infinite group.
:::

This proves the infinite half of the main theorem. Chapter 8 combines it with the finite half of
Part II.
