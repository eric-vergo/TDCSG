/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
import VersoBlueprint
import PILeanVerso
import TDCSGBlueprint.RepoFile
import TDCSGFigureTheorems
import TDCSG.CriticalRadius.Statements
import TDCSG.Finiteness

open Verso.Genre Verso.Genre.Manual Informal PILeanVerso TDCSGBlueprint

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
written theorem, with an independent referee report in the repository, and a computer check,
neither of them in Lean, as described at the end of this chapter.

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

:::figure TDCSGFigures.orderEight (label := "order-eight") (inline := true) (proves := TDCSGFigures.orderEight_spec) (alt := "Order eight: two closed disks about minus one and one, a critical point p-star on the left circle at the bottom of the lens, a vertical chord through it, and two orbit points q0 and q1 above it on the chord.")
Order 8, at the radius $`r_8=\sqrt{10-5\sqrt2}`: the closed disks about $`-1` and $`1`, their lens,
and the critical point $`p^*=1-2\zeta+\zeta^2-\zeta^3`, $`\zeta=\exp(2\pi i/8)`, on the left circle
and inside the right disk. On the vertical chord through $`p^*` lie the points
$`q_k=p^*+4i(\sqrt2-1)^{k+1}` of its orbit, drawn for $`k=0,1`; they accumulate at $`p^*`, so the
orbit is infinite.
:::

:::figure TDCSGFigures.orderTen (label := "order-ten") (inline := true) (proves := TDCSGFigures.orderTen_spec) (alt := "Order ten: two closed disks about minus one and one and a chord through zero from minus W on the right circle to W on the left circle, cut into three pieces numbered 1, 2, 3; the three words are written below.")
Order 10, at the radius $`r_{10}=\sqrt{4-\varphi}`: the closed disks about $`-1` and $`1`, their
lens, and the chord through $`0` from $`-W` on the right circle to $`W=\sqrt5\,u` on the left
circle, $`u=\exp(4\pi i/5)`. The cuts $`-\varphi^{-1}u` and $`u` divide it into the pieces numbered
1, 2 and 3, on which the words written below act as translations, together a rotation of the
chord by $`2\varphi^{-1}u` modulo $`2\sqrt5\,u`; the orbit of $`0` is infinite.
:::

:::figure TDCSGFigures.orderTwelve (label := "order-twelve") (inline := true) (proves := TDCSGFigures.orderTwelve_spec) (alt := "Order twelve: two closed disks about minus one and one, a critical point p-star on the left circle at the lower right of the lens, the chord through it, and the orbit point q0 next to it on the chord.")
Order 12, at the radius $`r_{12}=\sqrt{40-22\sqrt3}`: the closed disks about $`-1` and $`1`, their
lens, and the critical point $`p^*=-2\zeta+4\zeta^2-3\zeta^3`, $`\zeta=\exp(2\pi i/12)`, on the left
circle and inside the right disk. The chord through $`p^*` runs in the direction
$`V=\zeta^5+\zeta^6`; on it lies the first orbit point $`q_0=p^*+(14-8\sqrt3)V`, and the points
$`p^*+2(2-\sqrt3)^{k+2}V` that follow accumulate at $`p^*`, too close to draw apart.
:::

*What is open.* Whether these three bounds are equalities is open. Equality would need the
group to be finite at every radius below the bound, the counterpart of Part II for these orders;
the certificates described below prove finiteness only on initial ranges. Whether, for a general
order, the group is infinite at the critical radius itself is also open; for order five the main
theorem settles it.

:::theorem "crystallographic" (lean := "TDCSG.finite_GG") (uses := "group_orbit, generated_by_two, two_disk_support, two_disk_finite")
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
Let the radii $`r_1\le r_1'` and $`r_2\le r_2'` be given, and let $`O` be the orbit of a point
$`p` under the group at the larger radii. Each generator at the smaller radii is the rotation of
a smaller disk extended by the identity. On the smaller disk it agrees with the generator of the
larger group for the same center, because both act there as the same rotation, and off the
smaller disk it is the identity. So it maps $`O` into $`O`, and so does its inverse. By the
monotonicity lemma of Chapter 1 the whole group at the smaller radii maps $`O` into itself, and
the orbit of $`p` at the smaller radii, which contains $`p`, lies in $`O`. For the group
statement, the orbits of the finite larger group have at most as many points as the group has
elements. So the orbits of the finitely generated smaller group are uniformly bounded, and it is
finite.
:::

# Computing a single orbit

%%%
number := false
%%%

The program `tdcsg-orbit` represents a cyclotomic integer by its coefficients in a power
basis. Rotations operate on these integers and the disk test handles equality on the boundary.
Breadth-first search starts from a specified point and applies both generators and their
inverses. Exhausting the queue proves that this particular orbit has been fully enumerated
by the algorithm. Reaching a search cap leaves its eventual size undetermined. Run
`lake test` to exercise the engine's self-tests. See the
{repoFile "notes/engine.md"}[engine guide] for reproducible
commands and exact radius syntax.

# What a certificate adds

%%%
number := false
%%%

A cut-set certificate is a finite union of arcs of circles of radius $`r` that contains both
boundary circles, is mapped into itself by both generators and their inverses, and meets the boundary circles
in a controlled way: no carrying circle is tangent to a boundary circle, and every arc endpoint
on a boundary circle is also the endpoint of an arc that enters that disk. The certificate
theorem says that such a certificate at radius $`r` makes the group finite at $`r`, and by
monotonicity at every smaller radius. It is Theorem 4.2, “finiteness certificate”, of the note
{repoFile "notes/proofs/critical-radius-n5.md"}[Bounds on the critical radius of GG₅]
(`notes/proofs/critical-radius-n5.md` in the repository), a written proof that is not part of
this site. The theorem holds for every order, and the note has an independent referee report in
the repository. It has no Lean counterpart: the library contains
neither the theorem nor a definition of a certificate.

The search and verification programs are separate. The checker reads a finished certificate
and tests its closure conditions using exact arithmetic without floating point. The
{repoFile "notes/certificates.md"}[certificate records]
give input radii, commands and file checksums. The certified finiteness ranges for orders 8,
10 and 12 are therefore proved modulo that computation, not in Lean. At order five no certificate
is needed: finiteness on the whole range $`r<R` is proved in Lean, in Part II.

The note on {repoFile "notes/relative-certificates.md"}[relative certificates] records a
weaker kind of certificate, computed at the radius of the closed form itself. It fixes windows:
small closed regions of the plane, one around each lattice point on the two boundary circles. A
relative certificate is a finite union of arcs of circles of radius $`r` that contains the
boundary circles and the boundaries of the windows, and is mapped into itself by the generators
and their inverses outside the windows. It does not prove finiteness by itself. It bounds the
number of points that can be reached from a given point by moves whose intermediate points stay
outside the windows, for every smaller radius at once, and so reduces finiteness to bounding how
many points of an orbit lie in the windows. None of this is needed at order five, where the classification on
this site uses integer-coordinate confinement and the chord construction of Part I, and every
step of it is checked in Lean.
