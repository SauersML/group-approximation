import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.MultiStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.TripleExcl
import GroupApproximation.Meta.AxiomGuard

/-!
# The region choice outside the one- to five-dart cases

Lane gl-p10-69.  Notation as in `MultiStatement`: `M = X.toCombMap`, `c = K.boundary.cycle`,
`R = EqvGen (FaceClassStep M (walkKeep M c))`, `I = invDarts X K.sourceArc.darts`,
`T = K.targetArc.darts`.

## Route

On the residual of `roseLobeMulti_Statement` (no region of the one- and two-dart kinds) the
truth check finds every surviving region witnessed by one of six fixed-size shapes, and each is
proved as a case lemma with an explicitly named witness (`TripleLake`, `TripleLobe`):

* (lake triple: consecutive, wrapping after the first dart, wrapping after the second) the
  class of `α a1` meets `α c` in `α a1`, `α a2`, `α a3` only, three cyclically consecutive darts
  of `c`, and misses the outer face and the source cell: the lake at `a1`;
* (inside triple / quadruple / quintuple) three, four or five consecutive darts `B` of `c` are
  closed under the classes they meet (one, two or more classes: one case), none of which is the
  kept class, suitably placed: the lobe `rs = B` with `B` removed.

No contiguity hypothesis (the darts are given with their positions), no general run lemma over
an arbitrary block (each shape is a separate lemma on an explicit literal).  Strict descent to
the two-dart cases is not available: the size of the trace of a region on `c` is intrinsic to
the region, and no concrete measure on the configuration decreases along a move that keeps the
hypotheses of `roseLobeMulti_Statement` (the truth check sees three- to five-dart witnesses with
no one- or two-dart witness at all), so the residual is NOT closed.

## LOUD: strength of the residual

`roseLobeTriple_Statement` is `roseLobeMulti_Statement` with six more hypotheses, the negations
of the six cases (`roseLobeTriple_NoLakeRun`, `_NoLakeWrapL`, `_NoLakeWrapR`, `_NoLobeRun`,
`_NoLobeQuad`, `_NoLobeQuint`).  So it is implied by `roseLobeMulti_Statement`, and
`roseLobeTriple_multi_of` proves the converse: as closed propositions the two (and
`roseLobeChoice_Statement`, `roseLobeRegion_Statement`) are **EQUIVALENT**; it is **NOT strictly
weaker in logical strength**, and not stronger.  It is **strictly smaller in proof content**:
every configuration with a region of the six shapes is now discharged, and on the `maxeps 2`
random configurations the residual drops from `29` (resp. `173`) to `0`.

## LOUD: model failures of the conclusion at `maxeps 10`

On seed `5`, `N = 30`, `maxeps 10` the truth-check model finds `1260` distinct configurations
satisfying every MODELLED hypothesis of `roseLobeMulti_Statement` (planarity, `hiff`, `hcov`,
`hside`, `hI`, `hT`, `ClosedWalk`, `¬FirstTurns`, `¬Unpinched`, `AllNonFirstTurnsCrossed`, the
arc-length bounds and all exclusions) and having NO lobe and NO lake: the conclusion of
`roseLobeMulti_Statement` (hence of this statement, of `roseLobeChoice_Statement` and of
`roseLobeRegion_Statement`) FAILS in the combinatorial model there.  They have
`sourceArc = targetArc = []` up to one dart, the two sides (length `≤ 7 ≤ eps`) covering the
whole walk, and interleaving inside and outside classes (a rose); all admit a letter labelling.
NOT modelled: `X.LeastArea`.  So these statements can only be true through `LeastArea` (or a
defect of the model); the earlier "failures 0" (gl-p10-63, -67) covered `maxeps 2` and seed `0`
at `maxeps 10` only.  This residual is therefore OPEN and possibly FALSE as stated without a use
of `LeastArea`.

## Remaining gap

Planar existence of a region when every region meets `c` in at least three darts in a shape not
covered here or in badly placed one to five darts; on the model, exactly the `1260` failures
above, which have no region at all.

## Truth check (Python, not formalised)

`scratchpad/gl-p10-69/c3.py` (with `c1.py`, on gl-p10-67 `b1.py` / `b4.py`).  Per configuration
of the gl-p10-67 residual it builds exactly the Lean witness of each case here that applies and
asserts `roseLobeRegion_Block` / `_Place` on it (`0` assertion failures).

* Seeds `0`-`7`, `N = 60`, `maxeps 2` (`104954` configurations): gl-p10-67 residual `29`, new
  residual `0`.  Cases (overlapping): lake triple `14`, lake wrap `14`, inside quadruple `1`.
* Seeds `0`-`7`, `N = 300`, `maxeps 2` (`494752` configurations): residual `173`, new residual
  `0`.  Lake triple `80`, lake wrap `92`, inside triple `10`, inside quadruple `3`.
* Seeds `0`-`7`, `N = 30`, `maxeps 10`: residual `10283` (seeds `0`, `1`, `2`, `5`, `6`: `48`,
  `573`, `648`, `5742`, `3272`), new residual `1260`, all on seed `5` and all model failures of
  the conclusion (above).  The inside quintuple is needed on seed `1` (`143`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
