import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDoneSwap
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHmClosedWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Boone–Higman metabelian roots after τ is proved (lane bh-met-93b)

This is pure wiring.  `hmClosed_finitelyPresentedMetabelian_of_six` has `hswap` as its sixth
hypothesis.  Here `hswap` is supplied by `higmanVCTauDone_swapSection_of_antichain`, so the
only Higman input left is the antichain half (1) of the transfer.

`higmanVCTauDone_finitelyPresentedMetabelian` has 6 hypotheses:
`hH hvdk hloc hgen hcube hA`.  It supersedes these roots:
* `higmanVCPivotY_finitelyPresentedMetabelian`: 7 hypotheses, `… hZ hB`; `hB` is now proved
  and `hZ` implies `hA`;
* `higmanVCTauEqLvl_finitelyPresentedMetabelian` (`… hO (h : TightEq)`) and
  `higmanVCTauEqLvl_fpMetabelian_of_Z` (`… hZ (h : TightEq)`): 7 each; `TightEq` is now proved;
* `higmanVCTauEqLvl_fpMetabelian_of_d2` (`… hO (h : D2Residual)`) and
  `higmanVCTauEqTwo_fpMetabelian_of_decomp` (`… hO (h : Decomp)`): 7 each.

Compared with `hmClosed_finitelyPresentedMetabelian_of_six` it has the same count, but `hswap`
is replaced by `hA`, and `hA` now implies `hswap`.  The Z and orbit variants below are the
6-hypothesis forms of the old 7-hypothesis roots.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Best Boone–Higman metabelian root.**  The τ half is proved; the Higman input left is
the antichain half `HigmanVCAllAntichainStatement`, which is equivalent to (1). -/
theorem higmanVCTauDone_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hA : HigmanVCAllAntichainStatement) :
    FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian_of_six hH hvdk hloc hgen hcube
    (higmanVCTauDone_swapSection_of_antichain hA)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_finitelyPresentedMetabelian

/-- The best root with half (1) stated literally. -/
theorem higmanVCTauDone_fpMetabelian_of_ker_le
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (h : ∀ d : ℕ, 1 < d →
      (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True)) :
    FinitelyPresentedMetabelianStatement :=
  higmanVCTauDone_finitelyPresentedMetabelian hH hvdk hloc hgen hcube
    (higmanVCAll_antichain_of_ker_le h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_fpMetabelian_of_ker_le

/-- `higmanVCPivotY_finitelyPresentedMetabelian` without `hB`. -/
theorem higmanVCTauDone_fpMetabelian_of_Z
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hZ : HigmanVCPivotYStatement) :
    FinitelyPresentedMetabelianStatement :=
  higmanVCPivotY_finitelyPresentedMetabelian hH hvdk hloc hgen hcube hZ higmanVCTauDone_tau

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_fpMetabelian_of_Z

/-- `higmanVCTauEqLvl_finitelyPresentedMetabelian` without the tight-eq residual. -/
theorem higmanVCTauDone_fpMetabelian_of_orbit
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hO : HigmanVCOrbitStatement) :
    FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian_of_six hH hvdk hloc hgen hcube
    (higmanVCTauDone_swapSection_of_orbit hO)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_fpMetabelian_of_orbit

end GroupApproximation.BooneHigman.Metabelian.Envelope
