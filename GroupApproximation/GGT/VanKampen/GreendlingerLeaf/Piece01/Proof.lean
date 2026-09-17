import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoins
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94LongTransitions
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingTransitionsInput
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMapSmallFaces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMapHolds
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BoundaryJunctionBudget
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01BackwardJunctions.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 01: the budget of the class end loops

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.4.  `OsinLemma94ClassEndLoopsBudgetInput`
(`Estimating/OsinLemma94ClassEndLoopsSide`) is the `hbudget` residual of
`relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals` (`GreendlingerLeaf/Common/EightResidualWaist`).

## Route

The producer chain is the one of `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV9`
(`Estimating/OsinGreendlingerWaistV9`), with the contact transitions pushed down to their pieces:

* `osinLemma94ClassEndLoopsBudgetInput_of_joins` (`Estimating/OsinLemma94ClassJoins`) over
  - the long transitions, `osinLemma94LongTransitionInput_of_pieces` (`Estimating/OsinLemma94LongTransitions`),
    over the contact transitions and the proved cutting transitions `osinLemma94CuttingTransitionInput`
    (`Estimating/OsinLemma94CuttingTransitionsInput`).  The contact transitions come from
    `osinLemma94ContactTransitionInput_of_pieces` (`Estimating/OsinLemma94ContactAssembly`) over the
    object changes, the section corners and the small faces of the contact map; the small faces come from
    `osinLemma94ContactMapSmallFacesInput_of_nondegenerate` (`Estimating/OsinLemma94ContactMapSmallFaces`)
    and `osinLemma94ContactMapNondegenerateSmallFacesInput_of_pieces` (`Estimating/OsinLemma94ContactMapHolds`);
  - the bad junctions, `osinLemma94BadJunctionInput_of_pieces` (`Estimating/OsinLemma94BadJunctionPieces`),
    over the cell junction value and `osinLemma94BoundaryJunctionBudgetInput_of_pieces`
    (`Estimating/OsinLemma94BoundaryJunctionBudget`);
  - the end loops of the class joins.

## Assumed sub-leaf endpoints

Each sub-leaf lives in the module `GreendlingerLeaf/<Dir>/Proof` and exposes, in the namespace
`GroupApproximation.GGT.VanKampen.GreendlingerLeaf.<Dir>`, a theorem `proof` with the universe
parameters `u w v` of its statement:

* `P01ObjectChanges.proof : OsinLemma94ObjectChangesStatement.{u, w, v}`;
* `P01SectionCorners.proof : OsinLemma94SectionCornersInput.{u, w, v}`;
* `P01HoldingSmallFaces.proof : OsinLemma94ContactMapHoldingSmallFacesInput.{u, w, v}`;
* `P01EmptyTwoGon.proof : OsinLemma94ContactMapEmptyTwoGonInput.{u, w, v}`;
* `P01CellJunctionValue.proof : OsinLemma94CellJunctionValueInput.{u, w, v}`;
* `P01BackwardJunctions.proof : OsinLemma94BackwardJunctionCountInput.{u, w, v}`;
* `P01ValueFailures.proof : OsinLemma94BoundaryValueFailureCountInput.{u, w, v}`;
* `P01ClassJoinsEndLoops.proof : OsinLemma94ClassJoinsEndLoopsInput.{u, w, v}`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01

universe u w v

/-- **Piece 01 of the Greendlinger leaf: `OsinLemma94ClassEndLoopsBudgetInput` holds**, with no
hypotheses: the class-joins producer applied to the eight sub-leaf proofs and the proved cutting
transitions. -/
theorem proof : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v} :=
  osinLemma94ClassEndLoopsBudgetInput_of_joins
    (osinLemma94LongTransitionInput_of_pieces
      (osinLemma94ContactTransitionInput_of_pieces
        GreendlingerLeaf.P01ObjectChanges.proof
        GreendlingerLeaf.P01SectionCorners.proof
        (osinLemma94ContactMapSmallFacesInput_of_nondegenerate
          (osinLemma94ContactMapNondegenerateSmallFacesInput_of_pieces
            GreendlingerLeaf.P01HoldingSmallFaces.proof
            GreendlingerLeaf.P01EmptyTwoGon.proof)))
      osinLemma94CuttingTransitionInput)
    (osinLemma94BadJunctionInput_of_pieces
      GreendlingerLeaf.P01CellJunctionValue.proof
      (osinLemma94BoundaryJunctionBudgetInput_of_pieces
        GreendlingerLeaf.P01BackwardJunctions.proof
        GreendlingerLeaf.P01ValueFailures.proof))
    GreendlingerLeaf.P01ClassJoinsEndLoops.proof

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01.proof
