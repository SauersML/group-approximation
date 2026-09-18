import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Statement
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06e.AllCellsStatement
import GroupApproximation.Manuscript.NonMF.Full.GL06e.Refuted
import GroupApproximation.Meta.AxiomGuard

/-!
# The lake exclusion from the enclosed inner pocket, conditional on the all-cells refutation

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

**CONDITIONAL, stated loudly.**  Both theorems here take the hypothesis
`GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`, which is **not proved** in the
repository.  An earlier draft of this module tried to refute the all-cells disjunct of the
corrected enclosed inner pocket inline, through an undefined placeholder
(`ALLCELLS_REFUTATION_PENDING`).  No existing declaration refutes that disjunct unconditionally,
so the refutation is now an explicit hypothesis.  It is the Route A binder 5 residual of
`NMWire2.Census`.

`proof_of_innerPocketEnclosed` derives the proper arcs of the cell pocket walk below the inductive
bound (`CellPocketWalkProperArcsBelowSectionStatement`).  In fact the walk does not exist:
`GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells` refutes it, from the
corrected enclosed inner pocket and the all-cells refutation.  Its route is:
* the pocket walk is a pocket region holding a kept relator cell off both candidates;
* the corrected enclosed inner pocket gives either a two-arc face set, unpinched to a
  `TwoArcExit` and refuted by clause (b) below the relator count (`GL06g.false_of_twoArcExit`),
  or an enclosed face set holding every relator cell with outer walk of length at most `2ε`,
  refuted by the hypothesis.
The thresholds are those of that refutation.

`proof_of_allCells` discharges the corrected enclosed inner pocket by the proved
`GL03BPinch.innerPocketEnclosedTwoArcCorrected`, leaving the all-cells refutation as the only
hypothesis.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06g

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **The lake exclusion from the enclosed inner pocket, CONDITIONAL on the all-cells
refutation** (Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).

**The hypothesis `hall` (`GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`) is not proved
in the repository.**  From it and the corrected enclosed inner pocket, a cell pocket walk with the
exterior off its side does not exist below the inductive bound
(`GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells`), so its arcs are proper
vacuously. -/
theorem proof_of_innerPocketEnclosed
    (h : GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps0, heps0⟩ :=
    GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells h hall D hhyp lambda c
      mu hlambda hlambda1 hc hmu hmu1
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrefuted⟩ := heps0 eps heps
  refine ⟨rho0, hrho0, fun rho hrho W hcondition => ?_⟩
  intro Delta cuts hlea hbelow S _i _j _a _b ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂
    hw hoff
  exact (hrefuted rho hrho W hcondition Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K
    hfirst hsecond h₁ h₂ hw hoff).elim

/-- **The lake exclusion, CONDITIONAL on the all-cells refutation alone** (Osin, proof of
Lemma 9.7(b); `thm:hull`).  `proof_of_innerPocketEnclosed` with the corrected enclosed inner
pocket supplied by the proved `GL03BPinch.innerPocketEnclosedTwoArcCorrected`.

**The hypothesis `hall` is not proved in the repository.** -/
theorem proof_of_allCells
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  proof_of_innerPocketEnclosed GL03BPinch.innerPocketEnclosedTwoArcCorrected.{u, w, v} hall

end GroupApproximation.Full.GL06g

#audit_axioms GroupApproximation.Full.GL06g.proof_of_innerPocketEnclosed
#audit_axioms GroupApproximation.Full.GL06g.proof_of_allCells
