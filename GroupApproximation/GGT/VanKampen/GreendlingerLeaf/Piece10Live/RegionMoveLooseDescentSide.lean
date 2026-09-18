import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseDescent
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseSideResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# The loose-count surgery is equivalent to the side statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-24.

## Route

* `regionMoveLooseDescent_side_of_surgery` (proved): Surgery → `RegionMoveLooseSideStatement`,
  through Close and the residual.
* `regionMoveLooseDescent_surgery_of_side` (proved): `RegionMoveLooseSideStatement` → Surgery,
  through Close.

## Status (LOUD)

`RegionMoveLooseDescentSurgeryStatement` is **logically equivalent** to
`RegionMoveLooseSideStatement`.  It is neither weaker nor stronger.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

/-- **The side statement from the surgery.** -/
theorem regionMoveLooseDescent_side_of_surgery
    (h : RegionMoveLooseDescentSurgeryStatement.{u, w, v}) :
    RegionMoveLooseSideStatement.{u, w, v} :=
  regionMoveLooseSide_of_residual
    (regionMoveLoose_residual_of_close (regionMoveLooseDescent_close_of_surgery h))

/-- **The surgery from the side statement.** -/
theorem regionMoveLooseDescent_surgery_of_side (h : RegionMoveLooseSideStatement.{u, w, v}) :
    RegionMoveLooseDescentSurgeryStatement.{u, w, v} :=
  regionMoveLooseDescent_surgery_of_close (regionMoveLooseSide_close_of_side h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_side_of_surgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_surgery_of_side
