import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchSection
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 08: the pocket face set with a proper source arc

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `OsinSectionPocketFaceSetProperSectionStatement`
(`Estimating/OsinPocketPinchSection`) is the `hfaces` residual of
`relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals` (`GreendlingerLeaf/Common/EightResidualWaist`).

## Route

The sub-leaf `P08ProperArc` proves the statement itself: the face set between two exterior regions, on
an O-equivalent copy with letter labels, in walk order, with source arc shorter than the boundary of
its source cell.  The first-turn producer `OsinSectionPocketFaceSetFirstTurnSectionStatement.toProper`
(`Estimating/OsinPocketPinchFirstTurnAssembly`) is not used: first-turn order fails at map level on a
lake holding the source cell (`Estimating/OsinPocketPinchOuterDispatch`).

## Assumed sub-leaf endpoint

The sub-leaf lives in the module `GreendlingerLeaf/P08ProperArc/Proof` and exposes

* `GreendlingerLeaf.P08ProperArc.proof : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v}`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08

universe u w v

/-- **Piece 08 of the Greendlinger leaf: `OsinSectionPocketFaceSetProperSectionStatement` holds**, with
no hypotheses. -/
theorem proof : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v} :=
  GreendlingerLeaf.P08ProperArc.proof

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08.proof
