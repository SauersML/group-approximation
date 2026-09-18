import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07Below.RerouteStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsPinchCorrBridge
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The GGT-side consumers of the corrected enclosed pocket, discharged

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121).

* `nmWire2_p07Reroute_arcsInput_of_allCells`: `GreendlingerLeaf.p07Reroute_arcsInput_of_corrected`
  with `hencl` discharged by `GL03BPinch.innerPocketEnclosedTwoArcCorrected`.  Every other
  hypothesis is kept exactly.
* `nmWire2_pinchAbsPinchCorr_pinchPart`: `P07InnerPocket.pinchAbsPinchCorr_pinch_ofPCorr` at the
  proved `GL03BPinch.innerPocketEnclosedTwoArcPinchedCorrected`.
* `nmWire2_pinchAbsPinchCorr_off`: `P07InnerPocket.pinchAbsPinchCorr_off_ofCorr` at the proved
  `GL03BPinch.innerPocketEnclosedTwoArcCorrected`.

The section-level consumers `GreendlingerLeaf.p07Reroute_arcs_of_corr_allCells` and the `_corr`
endpoints of `Piece07Below.RerouteFrontier` are already discharged in
`Piece07Below.RerouteEndpoint`, so they are not repeated here.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire2

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **Proper arcs below the inductive bound, at fixed parameters, from the all-cells refutation
alone** (Osin, proof of Lemma 9.7(b); `thm:hull`).  This is
`GreendlingerLeaf.p07Reroute_arcsInput_of_corrected` with `hencl` discharged. -/
theorem nmWire2_p07Reroute_arcsInput_of_allCells
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps rho : ℕ}
    {mu lambda c : ℝ}
    (hall : GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowInput.{u, w, v}
      D lambda c mu eps W)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ)) :
    CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W :=
  GreendlingerLeaf.p07Reroute_arcsInput_of_corrected
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected hall hcondition
    hlambda hlambda1 hc hmu hmu1 hrho hlarge

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_p07Reroute_arcsInput_of_allCells

end Input

/-- **The pinch part of the P07 inner pocket bridge**, from the proved pinched corrected
statement. -/
theorem nmWire2_pinchAbsPinchCorr_pinchPart :
    GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_PinchPart.{u, w, v} :=
  GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_pinch_ofPCorr
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcPinchedCorrected

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_pinchAbsPinchCorr_pinchPart

/-- **The off part of the P07 inner pocket bridge**, from the proved corrected statement. -/
theorem nmWire2_pinchAbsPinchCorr_off :
    GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_OffStatement.{u, w, v} :=
  GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_off_ofCorr
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_pinchAbsPinchCorr_off

end GroupApproximation.Full.NMWire2
