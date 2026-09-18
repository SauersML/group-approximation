import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.PlaceBlock
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.NoBubSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The lobe step as a positional no-bubble statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-58.

`roseLobePlace_Statement` (gl-p10-56) asks for a lobe colouring with the root, source, kept and
block clauses, and two *placement* clauses about the filtered arcs: the kept darts of the reversed
source arc `I = invDarts X K.sourceArc.darts` form an infix of `I`, and the kept darts of the target
arc `t2 = K.targetArc.darts` form a prefix of some drop `t2.drop k` with `start + k ≤ n`, unless
the lobe is a lake.  `roseLobeNoBub_Statement` keeps the root, source, kept and block clauses
verbatim and replaces both placement clauses by conditions on the *position* of the block
`c = A ++ B ++ C` alone (no filtered arc, no drop, no wrap bound):

* source side: `P` removes `A ++ C`, or some dart of `B` is off `I`, or `B` is a prefix or a
  suffix of `I`;
* target side: no dart of `B` is on `t2`, or `C = []` and `P` removes `B`, or `P` removes
  `A ++ C` and no dart of `A` is on `t2`.

This is "no bubble": the excluded rm-form blocks are exactly those strictly inside `I`, and the
excluded target cases are those where the kept part of `t2` does not start at the arc start.
`roseLobeNoBub_place_of_noBub` proves the reduction, through `roseLobeNoBub_place1` and
`roseLobeNoBub_place2` (`NoBubSides`, `NoBubLists`); the target placement always uses `k = 0`.

## LOUD: strength of the residual

`roseLobeNoBub_Statement` is **pointwise STRONGER** than `roseLobePlace_Statement`: for a fixed
witness `rs, A, B, C`, its conclusion implies Place's (proved), and not conversely (Place also
accepts an rm bubble whose removed middle is invisible on `I`, e.g. `B = []`, a kp block strictly
inside `t2` with a later drop `k > 0`, and any infix placement of `I`).  As a closed proposition it
implies `roseLobePlace_Statement`; **the converse is NOT proved** (it would need the planar core
below).  So this is NOT a weaker statement.  What it buys is strictly smaller proof content: the
filter, infix, drop and wrap analysis of both placements is discharged here, and what is left is
the positional existence claim alone.

## Remaining gap (the planar core)

Existence, under the rose hypotheses, of a lobe colouring with the root, source and kept clauses
and one contiguous removed block, which is a lake or sits on the cycle as above.  The
complement-lobe exchange does not give this: for a bubble lobe `Z` the kept clause forces
`K.kept ∉ Z`, so the complementary lobe flips the kept cell out.

## Truth check (Python, not formalised)

`scratchpad/gl-p10-58/nobub_lean.py` extends `gl-p10-56/place.py` on the gl-p10-50 / gl-p10-54
generator.  For every configuration it searches all lobe and lake colourings passing the source and
kept clauses and all splittings `cyc = A ++ B ++ C` in rm or kp form, and tests the clause exactly
as stated here.  Models: `315` configurations, `0` without a witness, `1478` witnesses.  Random
seeds `0`-`7` (`300` each): `494752` configurations, `0` without a witness.  Every non-lake witness
(`1111562` random, `1478` model) was also checked to satisfy Place's placement with `k = 0`
(`0` unsound).  Weaker positional forms FAIL: dropping the prefix/suffix-of-`I` alternative fails
on seeds `5` and `6` (`gl-p10-58/forms.py`, variants V1-V3, V5), and dropping the kp alternatives
fails on the models (V4, V6).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim
