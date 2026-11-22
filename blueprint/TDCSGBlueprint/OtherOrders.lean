/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoBlueprint
import TDCSG.CriticalRadius.Statements
import TDCSG.Finiteness

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Other orders and the exact orbit engine" =>

%%%
tag := "other-orders"
%%%

The chord construction suggests searching for new infinite orbits when the disks rotate through
an eighth, tenth or twelfth turn. All three orders have proved upper bounds. The matching
subcritical finiteness theorem is still open for each.

:::theorem "other_upper" (lean := "TDCSG.CriticalRadius.criticalRadius_eight_le, TDCSG.CriticalRadius.criticalRadius_ten_le, TDCSG.CriticalRadius.criticalRadius_twelve_le")
The upper bounds for orders 8, 10 and 12 are respectively
$`\sqrt{10-5\sqrt2}`, $`\sqrt{4-\varphi}`, and $`\sqrt{40-22\sqrt3}`.
At order ten the witness is the orbit of zero. At orders eight and twelve a distinguished
point on the left disk boundary has an infinite orbit.
:::

:::theorem "crystallographic" (lean := "TDCSG.finite_GG")
For two possibly unequal orders, the group is finite at every pair of radii if the least
common multiple of the orders is one of 1, 2, 3, 4 or 6.
:::

:::theorem "radius_monotonicity" (lean := "TDCSG.orbit_mono, TDCSG.finite_GG_of_le") (uses := "uniform_orbits")
Enlarging either disk can only enlarge each point orbit. If the larger-radius group is finite,
the uniform bound on its orbit sizes also bounds every orbit at the smaller radii.
:::

A word that reached a point can change its action after a disk is enlarged. To retain the old
path, omit letters that fixed the current point at the smaller radius. The remaining active
steps still act in the enlarged disks.

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

A cut-set certificate describes arcs of circles and their behavior under the generators.
The search and verification programs are separate. The checker reads a finished certificate
and tests its closure conditions using integer arithmetic. The
[certificate records](https://github.com/eric-vergo/TDCSG/blob/main/notes/certificates.md)
give input radii, commands and file checksums.

:::theorem "certificate_reduction" (lean := "TDCSG.CutSetCertificate, TDCSG.finite_GG_of_certificate")
Assuming the cut-set certificate theorem for order $`n`, a certificate at $`r_0>1` gives
finiteness throughout the range covered by that theorem. In this formal reduction the
certificate theorem is an explicit hypothesis.
:::

The [relative certificates](https://github.com/eric-vergo/TDCSG/blob/main/notes/relative-certificates.md)
use smaller windows or symmetry to bring additional cases within reach. Window-avoiding
chain bounds control a restricted class of paths. The order-five classification on this site
instead uses integer-coordinate confinement and the endpoint word construction, with no
cut-set certificate hypothesis.
