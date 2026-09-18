import GroupApproximation.BooneHigman.Metabelian.VdKSREndpoint
import GroupApproximation.BooneHigman.Metabelian.VdKDiagEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateWire
import GroupApproximation.BooneHigman.Metabelian.ElemFPNK2SliceWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The row-extension input from the diagonal residual alone

Lane `bh-met-90y`, wiring.  Lane `bh-met-90m` proves the polynomial stable-range bound
`vdkStab_PolyStableRangeHighStatement` outright (`ElemFP.vdkSR_polyStableRangeHigh`).  This file
discharges the `hA` argument of the diagonal and row-core endpoints with it, and replaces `hvdk`
in four Boone–Higman roots by the diagonal residual `ElemFP.vdkInj_DiagStatement`.

* `ElemFP.vdkHighWire_vdkRowExt_of_diag`, `ElemFP.vdkHighWire_vdkRowExt_of_rowCore`.
* `Envelope.vdkHighWire_finitelyPresentedMetabelian_of_six`
  (from `hmClosed_finitelyPresentedMetabelian_of_six`),
  `Envelope.vdkHighWire_dilate_finitelyPresentedMetabelian`
  (from `k2Dilate_hmClosed_finitelyPresentedMetabelian`),
  `Envelope.vdkHighWire_core_finitelyPresentedMetabelian`
  (from `nk2Core_finitelyPresentedMetabelian`),
  `Envelope.vdkHighWire_slice_finitelyPresentedMetabelian`
  (from `nk2Slice_finitelyPresentedMetabelian`).

No other root parameter is discharged by the stable-range bound: `hloc`
(`PolyK2CubeNilLocalStatement`) and `hstab` (`CZCubePosStabOverStatement` over `ℤ[1/m]`) are
not stable-range statements, and the only consumers of the stable-range statements are the
row-extension endpoints of the `VdK*` modules.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **Endpoint**: `VdKRowExtensionStatement` from the diagonal residual alone. -/
theorem vdkHighWire_vdkRowExt_of_diag (h : vdkInj_DiagStatement) : VdKRowExtensionStatement :=
  vdkInj_vdkRowExt_of_high_diag vdkSR_polyStableRangeHigh h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkHighWire_vdkRowExt_of_diag

/-- **Endpoint**: `VdKRowExtensionStatement` from the row-core residual alone. -/
theorem vdkHighWire_vdkRowExt_of_rowCore (h : vdkDiag_RowCoreStatement) :
    VdKRowExtensionStatement :=
  vdkDiag_vdkRowExt_of_high_rowCore vdkSR_polyStableRangeHigh h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkHighWire_vdkRowExt_of_rowCore

end GroupApproximation.BooneHigman.Metabelian.ElemFP

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `hmClosed_finitelyPresentedMetabelian_of_six` with `hvdk` replaced by the diagonal
residual. -/
theorem vdkHighWire_finitelyPresentedMetabelian_of_six
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hdiag : ElemFP.vdkInj_DiagStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian_of_six hH (ElemFP.vdkHighWire_vdkRowExt_of_diag hdiag)
    hloc hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.vdkHighWire_finitelyPresentedMetabelian_of_six

/-- `k2Dilate_hmClosed_finitelyPresentedMetabelian` with `hvdk` replaced by the diagonal
residual. -/
theorem vdkHighWire_dilate_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hdiag : ElemFP.vdkInj_DiagStatement)
    (hL : ElemFP.k2CubeDilate_LocalStatement)
    (hR : ElemFP.k2Dilate_PolyK2Statement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  k2Dilate_hmClosed_finitelyPresentedMetabelian hH
    (ElemFP.vdkHighWire_vdkRowExt_of_diag hdiag) hL hR hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.vdkHighWire_dilate_finitelyPresentedMetabelian

/-- `nk2Core_finitelyPresentedMetabelian` with `hvdk` replaced by the diagonal residual. -/
theorem vdkHighWire_core_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hdiag : ElemFP.vdkInj_DiagStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hU : ElemFPCharZero.nk2Core_SliceStatement)
    (hstab : ∀ m : ℕ, 0 < m →
      ElemFPCharZero.CZCubePosStabOverStatement (Localization.Away (m : ℤ)))
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  nk2Core_finitelyPresentedMetabelian hH (ElemFP.vdkHighWire_vdkRowExt_of_diag hdiag) hgen hU
    hstab hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.vdkHighWire_core_finitelyPresentedMetabelian

/-- `nk2Slice_finitelyPresentedMetabelian` with `hvdk` replaced by the diagonal residual. -/
theorem vdkHighWire_slice_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hdiag : ElemFP.vdkInj_DiagStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hU : ElemFPCharZero.nk2Slice_CofinalStatement)
    (hstab : ∀ m : ℕ, 0 < m →
      ElemFPCharZero.CZCubePosStabOverStatement (Localization.Away (m : ℤ)))
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  nk2Slice_finitelyPresentedMetabelian hH (ElemFP.vdkHighWire_vdkRowExt_of_diag hdiag) hgen hU
    hstab hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.vdkHighWire_slice_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
