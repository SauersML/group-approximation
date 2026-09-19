import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Model14
import GroupApproximation.Manuscript.NonMF.Full.GL03DKept.Core
import GroupApproximation.Meta.AxiomGuard

/-!
# The 14-dart shared-rose model against the kept sub-walk core statement

`m14_core_instance` applies `Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement` to the 14-dart
model.  It type-checks only if the model's premises (`Model14Pocket`, `Model14Diagram`) are
exactly the statement's hypotheses and `m14_Conclusion` (`Model14`) is exactly its conclusion.
Together with `m14_conclusion`, which proves `m14_Conclusion` outright, the model is a checked
instance on which the core holds.

Manuscript status: infrastructure (a truth witness) for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

open OsinPocketPinchedTwoGonModel (D)

/-- **The core statement, applied to the 14-dart model, gives `m14_Conclusion`.** -/
theorem m14_core_instance
    (h : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}) :
    m14_Conclusion :=
  h D 1 m14_X 0 4 m14_leastArea m14_letters m14_pK m14_closedWalk m14_notFirst m14_srcLt
    m14_tgtLt m14_notUnpinched m14_allCrossed

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_core_instance
