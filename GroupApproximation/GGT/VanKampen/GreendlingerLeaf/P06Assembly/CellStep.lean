import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesSurgery
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06 assembly: the Below cell step from the lakes chain

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p06-04, items (iii) and (iv).

The target is residual 06 of the Below waist, `CellPocketOuterPinchStepSectionDistinctBelowStatement`
(`Common/CellStepBelow`).  This is the P06 conjunct of `AsmClose.RegionEndpointsStatement`
(`AsmClose/Statement`), and the endpoints below have exactly that type.

## The chain

* `Piece06.proof_of_lakesSurgery` (`Piece06/LakesSurgery`): lake-fill form ⇒ unfiltered lakes.
* `Piece06.cellRoseUncutLakesBelow_of_unfiltered` (`Piece06/LakesBelow`): unfiltered ⇒ uncut lakes.
* `Piece06.proof_of_below_gaps` (`Piece06/RoseBelow`): uncut lakes + bad-corner refinement ⇒ the
  Below cell step.
* `Piece06.MonogonCorner.badCornerRefinement` (`Piece06/MonogonCorner`): the bad-corner refinement,
  hypothesis-free (gap 5 is closed).

## Why no unconditional endpoint of this type is authored

The three lakes Statements are equivalent to one another (`lakesSurgery_of_target`,
`cellRoseLakesUnfilteredBelow_of_lakes`), and each is **true but circular in case (d)**.
* **Case (d).**  Every relator cell, `Π_i` and `Π_j` included, lies off the exterior class across
  the edges off the cycle.  The filled rest `F'` then has boundary on the two sides only, and it
  holds all `n` relator cells.
* **Why this blocks a proof.**  `OsinLemma97Below` at `n` does not apply to `F'`.  What is needed is
  the short-word Greendlinger case at the same count (the three-circle model, `Piece06/LakesBelow`).
* **Why it is still true.**  Lemma 9.7 at count `n` makes the hypotheses unsatisfiable, so the
  statement holds, but no same-count proof is known.

So the hcellStep-typed endpoint is **superseded by binder 5 through the bypass**
(`P06Assembly.proof_of_innerPocketEnclosed_of_bypass`, module `P06Assembly/Proof`).  There the
walk binder is refuted before any pinch is needed.  Consumers of the waist should take binder 5
directly (the four-residual waist, module `P06Assembly/Waist`), not residual 06.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly

universe u w v

/-- **The Below cell step from the uncut lakes residual**, with the hypothesis-free bad-corner
refinement.  This is `AsmFrontier.cellStepBelow_of_monogonCorner_lakes` with the landed monogon
corner. -/
theorem cellStep_of_lakes (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} :=
  Piece06.proof_of_below_gaps hlakes Piece06.MonogonCorner.badCornerRefinement

/-- **The Below cell step from the unfiltered lakes residual.** -/
theorem cellStep_of_unfiltered
    (hunfiltered : Piece06.CellRoseLakesUnfilteredBelowStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} :=
  cellStep_of_lakes (Piece06.cellRoseUncutLakesBelow_of_unfiltered hunfiltered)

/-- **The Below cell step from the lakes surgery residual** (circular in case (d); see the module
docstring). -/
theorem cellStep_of_surgery (hsurgery : Piece06.CellRoseLakesSurgeryBelowStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} :=
  Piece06.proof_of_below_gaps
    (Piece06.cellRoseUncutLakesBelow_of_unfiltered (Piece06.proof_of_lakesSurgery hsurgery))
    Piece06.MonogonCorner.badCornerRefinement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.cellStep_of_lakes
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.cellStep_of_unfiltered
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.cellStep_of_surgery
