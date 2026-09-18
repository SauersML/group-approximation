import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchOuterDispatch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Predicate
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Frontier reduction for residual 10 of the Below waist

Lane gl-assembly-03, second module.  Residual 10 (`hstep`) is
`PocketOuterPinchStepSectionStatement` (`Estimating/OsinPocketPinchOuterDispatch`).

* `outerPinchStep_of_cases`: the step from its two cases, split on the rose configuration
  `P10ChordLift.AllNonFirstTurnsCrossed K`, at the larger of the two thresholds for `ε` and for `ρ`.
  This is a local copy of `Piece10.proof_of_cases`; the module `Piece10/Proof` cites the missing
  `P10Rose.rose` and is not imported.  The non-rose case is `P10ChordLift.NonRoseStepStatement`
  (`P10ChordLift/Proof`), the rose case `P10ChordLift.RoseStepStatement` (`P10ChordLift/Predicate`).
* `outerPinchStep_of_nonRose_subArc`: the step from the non-rose case and
  `P10Rose.RoseRegionMoveSubArcStatement`, through `P10Rose.rose_of_regionMoveSubArc`
  (`P10Rose/SubArc`).  The filter route (`RoseFilterStepStatement`, `RoseRegionMoveStatement`) is
  not used.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier

universe u w v

/-- **The outer-pinch step from its two cases**, at the larger of the two thresholds for `ε` and for
`ρ`: split on whether every non-first turn of the boundary cycle is crossed. -/
theorem outerPinchStep_of_cases (hnon : P10ChordLift.NonRoseStepStatement.{u, w, v})
    (hrose : P10ChordLift.RoseStepStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hnon D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hrose D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps0 eps1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps ((le_max_left eps0 eps1).trans heps)
  obtain ⟨rho1, -, hrho1⟩ := heps1 eps ((le_max_right eps0 eps1).trans heps)
  refine ⟨max rho0 rho1, lt_of_lt_of_le hrho0 (le_max_left rho0 rho1),
    fun rho hrho' W hcondition => ?_⟩
  intro X lo hi hlea hlabel K hK hturns hprop htgt hpinch
  by_cases hall : P10ChordLift.AllNonFirstTurnsCrossed K
  · exact hrho1 rho ((le_max_right rho0 rho1).trans hrho') W hcondition X lo hi hlea hlabel K hK
      hturns hprop htgt hpinch hall
  · exact hrho rho ((le_max_left rho0 rho1).trans hrho') W hcondition X lo hi hlea hlabel K hK
      hturns hprop htgt hpinch hall

/-- **Residual 10 from the non-rose case and the sub-arc region move.** -/
theorem outerPinchStep_of_nonRose_subArc (hnon : P10ChordLift.NonRoseStepStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  outerPinchStep_of_cases hnon (P10Rose.rose_of_regionMoveSubArc hsub)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.outerPinchStep_of_cases
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.outerPinchStep_of_nonRose_subArc
