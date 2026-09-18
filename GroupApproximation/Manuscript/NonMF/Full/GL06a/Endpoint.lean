import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoins
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94LongTransitions
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingTransitionsInput
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMapSmallFaces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMapHolds
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BoundaryJunctionBudget
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01BackwardJunctions.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.Proof
import GroupApproximation.Manuscript.NonMF.Full.GL01.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06a.ObjectChanges
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06a: the class end-loop budget of Osin's Lemma 9.4 (WO-GL06-1)

This is infrastructure for Hull's small cancellation theorem, `thm:hull` in
non_mf_groups_exist.tex.  It enters through the relative Greendlinger lemma (Osin,
arXiv:math/0411039v3, Lemma 4.4), via the budget in the proof of Lemma 9.4.  It certifies no
printed sentence on its own.

`budget : OsinLemma94ClassEndLoopsBudgetInput` assembles the Lemma 9.4 producers.
* Long transitions: contact transitions and cutting transitions.
  * Contact transitions use:
    * the object changes `Full.GL06a.objectChangesStatement` (module `GL06a.ObjectChanges`);
    * the section corners;
    * the small faces of the contact map (holding faces and `Full.GL01.contactMapEmptyTwoGonInput`).
  * The cutting transitions are `osinLemma94CuttingTransitionInput`.
* Bad junctions: the same-cell junction values and the boundary junction budget (backward
  junctions and value failures).
* The class-join end loops.
-/

namespace GroupApproximation.Full.GL06a

universe u w v

/-- **The class end-loop budget** (`OsinLemma94ClassEndLoopsBudgetInput`): Osin, Lemma 9.4, the
budget of class end loops, in the proof of Lemma 4.4 feeding `thm:hull`. -/
theorem budget : GroupApproximation.GGT.VanKampen.OsinLemma94ClassEndLoopsBudgetInput.{u, w, v} :=
  GroupApproximation.GGT.VanKampen.osinLemma94ClassEndLoopsBudgetInput_of_joins
    (GroupApproximation.GGT.VanKampen.osinLemma94LongTransitionInput_of_pieces
      (GroupApproximation.GGT.VanKampen.osinLemma94ContactTransitionInput_of_pieces
        objectChangesStatement
        GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.proof
        (GroupApproximation.GGT.VanKampen.osinLemma94ContactMapSmallFacesInput_of_nondegenerate
          (GroupApproximation.GGT.VanKampen.osinLemma94ContactMapNondegenerateSmallFacesInput_of_pieces
            GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.proof
            GroupApproximation.Full.GL01.contactMapEmptyTwoGonInput)))
      GroupApproximation.GGT.VanKampen.osinLemma94CuttingTransitionInput)
    (GroupApproximation.GGT.VanKampen.osinLemma94BadJunctionInput_of_pieces
      GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.proof
      (GroupApproximation.GGT.VanKampen.osinLemma94BoundaryJunctionBudgetInput_of_pieces
        GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01BackwardJunctions.proof
        GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.proof))
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.proof

end GroupApproximation.Full.GL06a

#audit_axioms GroupApproximation.Full.GL06a.budget
