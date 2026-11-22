/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import TDCSGBlueprint.Figures
import TDCSGBlueprint.Disks
import TDCSGBlueprint.Lift
import TDCSGBlueprint.Lens
import TDCSGBlueprint.Walls
import TDCSGBlueprint.Confinement
import TDCSGBlueprint.Chord
import TDCSGBlueprint.OtherOrders
import TDCSGBlueprint.Verification

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "The critical radius of fivefold disk rotations" =>

%%%
authors := ["Eric Vergo", "OpenAI GPT-6.2 Astra"]
%%%

![At the critical radius, the diagonal chord joins a point on the right disk boundary to its opposite on the left disk boundary.](/figures/critical-chord.svg)

Two overlapping disks generate a finite group until their common radius reaches
$`\sqrt{3+\varphi}`. At the endpoint, a single orbit visits infinitely many points.
Follow the geometry from the disks to the integer walls, then return to the plane for the
endpoint construction. Each mathematical block opens alongside the declarations used in its proof.

The [original paper](https://arxiv.org/abs/2302.12950) introduced these groups and proposed
the fivefold closed form. The [integer-coordinate proof](https://github.com/eric-vergo/TDCSG/blob/main/notes/proofs/sharp-lower-bound-n5-pentagrid.md)
establishes finiteness throughout the open range below it.

{ref "disks"}[Start the geometric proof] · {ref "verification"}[Inspect the independent statement]

{include 0 TDCSGBlueprint.Disks}
{include 0 TDCSGBlueprint.Lift}
{include 0 TDCSGBlueprint.Lens}
{include 0 TDCSGBlueprint.Walls}
{include 0 TDCSGBlueprint.Confinement}
{include 0 TDCSGBlueprint.Chord}
{include 0 TDCSGBlueprint.OtherOrders}
{include 0 TDCSGBlueprint.Verification}

{blueprint_graph}

{blueprint_summary}
