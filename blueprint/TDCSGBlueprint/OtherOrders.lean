/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoBlueprint
import TDCSG.CriticalRadius.Statements
import TDCSG.Finiteness

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Other orders" =>

%%%
tag := "other-orders"
%%%

The main theorem is proved in Chapter 8. This chapter places it among the other rotation orders:
what the Lean library proves for orders 8, 10 and 12, what holds for every order, and what is
open. None of it is used in the proof of the main theorem.

The chord construction suggests searching for new infinite orbits when the disks rotate through
an eighth, tenth or twelfth turn. All three orders have proved upper bounds. Finiteness on the
whole range below each bound is open. Certificates prove finiteness on initial ranges through a
refereed written theorem and a computer check, neither of them in Lean, as described at the end
of this chapter.

:::theorem "other_upper" (lean := "TDCSG.CriticalRadius.criticalRadius_eight_le, TDCSG.CriticalRadius.criticalRadius_ten_le, TDCSG.CriticalRadius.criticalRadius_twelve_le, TDCSG.CriticalRadius.infinite_orbit_zero_ten, TDCSG.CriticalRadius.infinite_orbit_pStar_eight, TDCSG.CriticalRadius.infinite_orbit_pStar_twelve, TDCSG.CriticalRadius.pStar_eight_mem_sphere, TDCSG.CriticalRadius.pStar_twelve_mem_sphere") (uses := "critical_radius_def, infinite_of_orbit, generated_by_two")
The critical radii for orders 8, 10 and 12 are at most
$`\sqrt{10-5\sqrt2}`, $`\sqrt{4-\varphi}`, and $`\sqrt{40-22\sqrt3}` respectively.
At order ten the witness is the orbit of zero. At orders eight and twelve the witness is a
lattice point that lies on the boundary circle of the left disk at the stated radius, and its
orbit is infinite at that radius and every larger one.
:::

:::proof "other_upper"
At order ten, three words act on a chord through zero as an irrational rotation, as at order
five. At orders eight and twelve, a self-similar family of words, closed under rescaling by
$`\sqrt2-1` or $`2-\sqrt3`, carries the critical point to infinitely many distinct points of
its orbit. Every disk test holds at the stated radius and hence at every larger one. An
infinite orbit forces an infinite group, and the critical radius is at most every radius with
an infinite group.
:::

*What is open.* Whether these three bounds are equalities is open. Equality would need the
group to be finite at every radius below the bound, the counterpart of Part II for these orders;
the certificates described below prove finiteness only on initial ranges. Whether, for a general
order, the group is infinite at the critical radius itself is also open; for order five the main
theorem settles it.

:::theorem "crystallographic" (lean := "TDCSG.finite_GG") (uses := "group_orbit, two_disk_finite")
For two possibly unequal orders, the group is finite at every pair of radii if the least
common multiple of the orders is one of 1, 2, 3, 4 or 6.
:::

:::proof "crystallographic"
Both orders then divide 4 or both divide 6, so every rotation factor lies in the Gaussian or the
Eisenstein integers. At each point every group element acts as $`z\mapsto uz+t` with $`u` and
$`t` in that lattice. It moves points only within the union of the disks, so $`t` is bounded,
and a discrete lattice has finitely many bounded points. The orbits are therefore uniformly
bounded, and the group is finite.
:::

:::theorem "radius_monotonicity" (lean := "TDCSG.orbit_mono, TDCSG.finite_GG_of_le") (uses := "group_orbit, generated_by_two, compound_monotone")
Enlarging either disk can only enlarge each point orbit. If the larger-radius group is finite,
the uniform bound on its orbit sizes also bounds every orbit at the smaller radii, so the
smaller-radius group is finite.
:::

:::proof "radius_monotonicity"
A word that reached a point can change its action after a disk is enlarged. To retain the old
path, note that on the smaller disk its rotation agrees with the rotation of the larger disk,
and off it the smaller rotation fixes the point. Omitting the letters that fixed the current
point leaves active steps that still act in the enlarged disks. For the group statement, the
orbit sizes of the finite larger group are at most its order.
:::

# Computing a single orbit

The program `tdcsg-orbit` represents a cyclotomic integer by its coefficients in a power
basis. Rotations operate on these integers and the disk test handles equality on the boundary.
Breadth-first search starts from a specified point and applies both generators and their
inverses. Exhausting the queue proves that this particular orbit has been fully enumerated
by the algorithm. Reaching a search cap leaves its eventual size undetermined. Run
`lake test` to exercise the engine's self-tests. See the
[engine guide](https://github.com/eric-vergo/TDCSG/blob/main/notes/engine.md) for reproducible
commands and exact radius syntax.

# What a certificate adds

A cut-set certificate is a finite union of arcs of circles of radius $`r` that contains both
boundary circles, is mapped into itself by both generators and their inverses, and meets the boundary circles
in a controlled way: no carrying circle is tangent to a boundary circle, and every arc endpoint
on a boundary circle is also the endpoint of an arc that enters that disk. The certificate theorem, Theorem 4.2 of the
[written proof](https://github.com/eric-vergo/TDCSG/blob/main/notes/proofs/critical-radius-n5.md),
says that such a certificate at radius $`r` makes the group finite at $`r`, and by monotonicity
at every smaller radius. Its proof is refereed, holds for every order, and has no Lean
counterpart: the library contains neither the theorem nor a definition of a certificate.

The search and verification programs are separate. The checker reads a finished certificate
and tests its closure conditions using exact arithmetic without floating point. The
[certificate records](https://github.com/eric-vergo/TDCSG/blob/main/notes/certificates.md)
give input radii, commands and file checksums. The certified finiteness ranges for orders 8,
10 and 12, and the certified initial ranges at order five, are therefore proved modulo that
computation, not in Lean.

The [relative certificates](https://github.com/eric-vergo/TDCSG/blob/main/notes/relative-certificates.md)
use smaller windows or symmetry to bring additional cases within reach. Window-avoiding
chain bounds control a restricted class of paths. The order-five classification on this site
instead uses integer-coordinate confinement and the endpoint word construction, and every step
of it is checked in Lean.
