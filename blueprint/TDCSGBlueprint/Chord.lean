/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoManual
import VersoBlueprint
import PILeanVerso
import TDCSGFigureTheorems
import TDCSG.CriticalRadius.Five

open Verso.Genre Verso.Genre.Manual Informal PILeanVerso

#doc (Manual) "The chord and its three words" =>

%%%
tag := "chord"
%%%

This chapter makes up Part I. It proves that $`GG_5(r)` is infinite for every $`r\ge R`, where
$`R=\sqrt{3+\varphi}`. This is the half of the main theorem that holds at and above the
threshold, and it shows that the finiteness of Part II cannot extend to $`R` itself. Write
$`\zeta=\exp(2\pi i/5)`.

Set $`E=\zeta-\zeta^2` and write points on the chord as $`tE` with $`-1\le t\le1`. Each word
below returns a point of its piece of the chord to the chord, and intermediate rotations within a
word may leave the chord. At $`R` every disk test of the three words holds, some with equality.
They continue to work at every larger radius.

:::definition "chord_check" (lean := "TDCSG.Five.pointE, TDCSG.Five.word₁, TDCSG.Five.word₂, TDCSG.Five.word₃")
Cut the parameter range $`[-1,1]` at $`t=1-\varphi` and $`t=3-2\varphi`, that is, the chord at
the points $`(1-\varphi)E` and $`(3-2\varphi)E`. Each of the three resulting subsegments
uses its own finite word in the generators $`a` and $`b`.
In order from the left piece to the right piece, the words are
$`a^{-1}a^{-1}b^{-1}a^{-1}b^{-1}`, $`ababb`, and $`abab^{-1}a^{-1}b^{-1}`.
Apply their letters from left to right.
:::

:::figure TDCSGFigures.chordPieces (label := "chord-pieces") (inline := true) (proves := TDCSGFigures.chordPieces_spec) (alt := "Two closed disks of the critical radius about minus one and one, their lens, and the chord from minus E to E through the lens, cut into three pieces numbered 1, 2, 3; the three words are written below.")
The closed disks of radius $`R=\sqrt{3+\varphi}` about $`-1` and $`1`, their lens, and the chord
from $`-E` to $`E`, where $`E=\zeta-\zeta^2` lies on the left circle and $`-E` on the right one. The
cuts $`(1-\varphi)E` and $`(3-2\varphi)E` divide the chord into the pieces numbered 1, 2 and 3;
piece $`i` is moved by word $`i`, written out below the disks with its letters applied from left
to right.
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

:::figure_explorer TDCSGFigures.wordTrace (label := "word-trace") (proves := TDCSGFigures.wordTrace_spec) (alt := "Three frames, one per word. Each shows a piece of the chord, dashed, numbered 0, and its images after each letter, numbered by the letters applied, until the last image lies on the chord again.")
The three words at the critical radius, one per frame. The piece of the chord that word $`i` acts
on is numbered 0 and drawn dashed; its image after $`k` letters is numbered $`k`, and the last image
lies on the chord again, moved by $`(2\varphi-2)E` for the first two words and by $`(2\varphi-4)E`
for the third. Before every letter both ends of the current segment lie in that letter's closed
disk, so the letter turns the whole segment; the marked ends lie on a boundary circle, where a disk
test holds with equality.
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

:::figure TDCSGFigures.chordOrbit (label := "chord-orbit") (inline := true) (proves := TDCSGFigures.chordOrbit_spec) (alt := "The orbit of zero along the chord: 25 rows, one per step k from 0 to 24, each with one point on the parameter line from minus one to one, and three vertical bands for the pieces of the three words.")
The returns $`t_0E,t_1E,\ldots,t_{24}E` of the orbit of zero to the chord, one row per step $`k`
from the top (the axis on the left), on the parameter line $`t\mapsto tE`, $`-1\le t<1`. The bands
mark the pieces of the three words, cut at $`t=1-\varphi` and $`t=3-2\varphi`; each point lies in
the band of the word applied next, which adds $`2\varphi-2` modulo $`2`. The end $`t=-1` (filled)
belongs to the range and the end $`t=1` (open ring) does not; the rotation is irrational, so the
points never repeat.
:::

{figref "chord-orbit"}[] shows successive returns to the chord, one entire word per step.

This proves the infinite half of the main theorem. Chapter 8 combines it with the finite half of
Part II.
