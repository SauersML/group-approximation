import GroupApproximation.GroupTheory.CentralHNNResiduallyFinite
import GroupApproximation.Higman.CentralHNNFreeLabelFaithful
import GroupApproximation.Higman.PairedReturnEdgeSeparable
import GroupApproximation.Sofic.ProfiniteSplitEmbedding

/-!
# Residual finiteness of the paired-return ambient

The paired-return ambient is a rank-two free-lamp amalgam.  Its explicit
normal form as two successive central HNN extensions combines with
separability of the paired edge to show that the whole ambient is residually
finite.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnAmbientResiduallyFinite

open PairedReturnCutter
open PairedReturnEdgeSeparable

abbrev P : Type := PairedReturnGraphIntersection.P
abbrev Edge : Subgroup P := PairedReturnGraphIntersection.M
abbrev Stage1 : Type := FreeLampFinitePresentation.Stage1 P Edge
abbrev Stage2 : Type := FreeLampFinitePresentation.Stage2 P Edge

/-- The canonical base embedding of a central HNN extension is split by
killing its stable letter. -/
theorem baseRet_comp_of (M : Subgroup P) :
    (CentralHNNFreeLabel.baseRet M).comp
        (HNNExtension.of : P →* Higman.CentHNN M) =
      MonoidHom.id P := by
  apply MonoidHom.ext
  intro g
  simp [CentralHNNFreeLabel.baseRet_of]

/-- The first central HNN stage is residually finite. -/
theorem stage1_residuallyFinite : Group.ResiduallyFinite Stage1 := by
  exact CentralHNNResiduallyFinite.centralHNN_residuallyFinite Edge
    profiniteClosure_edge

/-- The transported edge remains profinitely closed in the first stage. -/
theorem profiniteClosure_stage1Sub :
    profiniteClosure (FreeLampFinitePresentation.stage1Sub P Edge) =
      FreeLampFinitePresentation.stage1Sub P Edge := by
  letI : Group.ResiduallyFinite Stage1 := stage1_residuallyFinite
  exact profiniteClosure_map_eq_of_split_closed
    (HNNExtension.of : P →* Stage1)
    (CentralHNNFreeLabel.baseRet Edge)
    (baseRet_comp_of Edge) Edge profiniteClosure_edge

/-- The second central HNN stage is residually finite. -/
theorem stage2_residuallyFinite : Group.ResiduallyFinite Stage2 := by
  letI : Group.ResiduallyFinite Stage1 := stage1_residuallyFinite
  exact CentralHNNResiduallyFinite.centralHNN_residuallyFinite
    (FreeLampFinitePresentation.stage1Sub P Edge)
    profiniteClosure_stage1Sub

/-- The concrete paired ambient is the two-stage central HNN tower. -/
noncomputable def ambientEquivStage2 : PairedReturnCutter.Ambient ≃* Stage2 :=
  (FreeLampFinitePresentation.swappedAmalgamEquivFreeLamp
      (K := PairedReturnCutter.Sync) P Edge).trans
    ((FreeLampFinitePresentation.freeLampEquivOfLampEquiv P Edge
      PairedReturnCutter.syncEquivFree).trans
        (FreeLampFinitePresentation.freeLampEquivStage2 P Edge))

/-- **The finitely presented paired-return ambient is residually finite.** -/
theorem ambient_residuallyFinite :
    Group.ResiduallyFinite PairedReturnCutter.Ambient := by
  letI : Group.ResiduallyFinite Stage2 := stage2_residuallyFinite
  exact residuallyFinite_of_mulEquiv ambientEquivStage2

end PairedReturnAmbientResiduallyFinite
end Higman
end GroupApproximation
