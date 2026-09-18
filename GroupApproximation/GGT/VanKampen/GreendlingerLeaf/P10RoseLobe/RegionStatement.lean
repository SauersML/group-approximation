import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.RegionColour
import GroupApproximation.Meta.AxiomGuard

/-!
# The region choice of the planar core, in class form

Lane gl-p10-62.  Notation: `M = X.toCombMap`, `c = K.boundary.cycle`,
`R = EqvGen (FaceClassStep M (walkKeep M c))`, `Γ = walkMap M c`,
`I = invDarts X K.sourceArc.darts`, `T = K.targetArc.darts`.  The `R`-classes are the regions of
`c`: by the hypotheses of `roseLobeCore_Statement` they are the faces of the planar map `Γ`, each
inside or outside `K.faces`.

`roseLobeRegion_Statement` is the planar core of `roseLobeCore_Statement` with the Boolean move
calculus stripped off: its conclusion names regions and positions on `c` only.  Either

* (lobe) a nonempty list `rs ⊆ c` (the union of their inside regions is removed), a dart of the
  kept cell in none of them, and `c = A ++ B ++ C` whose removed darts (`d` in some root region)
  are `B` or `A ++ C` (`roseLobeRegion_Block`), placed as in `roseLobeRegion_Place`; or
* (lake) a walk dart `y` whose outer region (the class of `α y`) meets neither the outer face nor
  the source cell, and `c = A ++ B ++ C` whose removed darts (`α d` in the region of `α y`) are
  `B` or `A ++ C`.

It takes the hypotheses of `roseLobeCore_Statement` and two more, both proved
(`roseLobeRegion_faceOf_alpha_inv`, `roseLobeRegion_faceOf_alpha_tgt`): the reverse of every dart
of `I` lies on the source cell, and that of every dart of `T` on the outer face.  So in the lake
case no dart of `I` or `T` is ever removed.

## Route of the reduction `roseLobeRegion_core_of`

With `z = lobeColour rs`: for roots on `c`, `movePred z d` holds on `c` iff `d` is in no root
class (`roseLobeRegion_movePred_in`); for the root `α y`, iff `α d` is not in the class of `α y`
(`roseLobeRegion_movePred_out`), since the class of `α y` holds no dart of `c` (side constancy).
The block and placement clauses then read off (`roseLobeRegion_block`, `roseLobeRegion_place`).
Source: inside roots lie in `K.faces`; a lake meeting no source dart leaves the source out
(`not_mem_flipFaces`).  Kept: the kept dart outside every root class keeps the kept cell
(`roseJunctionCore_mem_flipFaces`); a lake root is outside `K.faces` (`α y` crosses `c`).  Root:
`rs ⊆ c`, or `rs = [α y]` with `α y ~ α y`.  Placement of a lake is the first disjunct.

## LOUD: strength of the residual

`roseLobeRegion_Statement` is **NOT strictly weaker** than `roseLobeCore_Statement`: pointwise
(for each fixed pocket) its conclusion is **EQUIVALENT** to Core's under Core's hypotheses (the
converse is not formalised; sketch: an inside root off `c` is replaced by a walk dart of its class
(cover); a single root outside `K.faces` meets no walk dart (side), so it is `R`-joined to some
`α y`, and the source clause says no source dart is in its class).  As closed propositions the two
are equivalent only if both are true.  It is **strictly smaller in proof content**: the move
calculus (`movePred`, `flipFaces`, `lobeColour`, the root/source/kept Boolean clauses and the
lake placement) is discharged here, and the facing of `I` and `T` is supplied.  What remains is
the pure region choice: a set of faces of `Γ` whose walk darts form one cyclic block, placed
relative to `I` and `T`.

## Remaining gap

Choose the region(s).  Not proved here.  In the truth check an inside lobe suffices on every
model configuration, but a lake is needed on about a third of the random ones.

## Truth check (Python, not formalised)

`scratchpad/gl-p10-62/region.py`, extending `scratchpad/gl-p10-60/core.py` (the gl-p10-50 / 54 /
58 generator).  Per configuration it reruns the five planar checks of `core.py`, checks the two
added hypotheses, searches the class-form conclusion clause by clause, and compares with the
gl-p10-58 check of the NoBub conclusion (`AGREE`).  Models: `315` configurations, all with a
lobe witness, `0` failures.  Random seeds `0`-`7` (`300` each): `494752` configurations
(`327801` lobe, `166951` lake), `0` without a witness, `0` disagreements with gl-p10-58, `0`
failures of the planar or the added hypotheses.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim
