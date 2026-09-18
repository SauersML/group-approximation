import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotYReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCAllReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVPresentReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHmClosedWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Wiring the pivot residual into `hswap` (lane bh-met-77u)

`HigmanVSwapSectionStatement` (`hswap`) follows from `HigmanVCTransferStatement`, which has two
halves:
* (1) `hA`, relation completeness `ker E ≤ normalClosure (rels)`;
* (2) `hB`, an extension `τ` that kills the long relators.

This file supplies the pivot half (1) from the residual Z = `HigmanVCPivotYStatement`, along the
chain Z → Y → X → (1):
* `higmanVCPivotY_Y_of_Z`;
* `higmanVCPivotAC_X_of_Y`;
* `higmanVCTreeNFWitPivot_ker_le_of_X`.

It keeps `hB` as a hypothesis.
* `higmanVCPivotY_transfer_of_Z_of_tau`: Z and `hB` give `HigmanVCTransferStatement`.
* `higmanVCPivotY_swapSection_of_Z_of_tau`: Z and `hB` give `hswap`.
* `higmanVCPivotY_swapSection_of_Y_of_tau`: the same from Y.
* `higmanVCPivotY_finitelyPresentedMetabelian`: `hmClosed_finitelyPresentedMetabelian_of_six`
  with `hswap` replaced by Z and `hB`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Z gives the antichain gap `HigmanVCAllAntichainStatement`. -/
theorem higmanVCPivotY_antichain_of_Z (h : HigmanVCPivotYStatement) :
    HigmanVCAllAntichainStatement :=
  higmanVCAll_antichain_of_ker_le fun d hd => higmanVCPivotY_ker_le_of_Z h d hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_antichain_of_Z

/-- **Transfer.**  Z (the half `hA`) and the extension `τ` (the half `hB`). -/
theorem higmanVCPivotY_transfer_of_Z_of_tau (hZ : HigmanVCPivotYStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVCTransferStatement :=
  fun d hd => ⟨higmanVCPivotY_ker_le_of_Z hZ d hd, hB d hd⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_transfer_of_Z_of_tau

/-- **`hswap` from Z and `τ`.** -/
theorem higmanVCPivotY_swapSection_of_Z_of_tau (hZ : HigmanVCPivotYStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVSwapSectionStatement :=
  higmanVPresent_swapSection_of_finFP
    (higmanVC_finFP_of_transfer (higmanVCPivotY_transfer_of_Z_of_tau hZ hB))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_swapSection_of_Z_of_tau

/-- **`hswap` from Y and `τ`.** -/
theorem higmanVCPivotY_swapSection_of_Y_of_tau (hY : HigmanVCPivotACStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVSwapSectionStatement :=
  higmanVCPivotY_swapSection_of_Z_of_tau (higmanVCPivotY_Z_of_Y hY) hB

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_swapSection_of_Y_of_tau

/-- **The root with `hswap` replaced by Z and `τ`.** -/
theorem higmanVCPivotY_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hZ : HigmanVCPivotYStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian_of_six hH hvdk hloc hgen hcube
    (higmanVCPivotY_swapSection_of_Z_of_tau hZ hB)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
