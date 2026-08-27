import GroupApproximation.Higman.FreeLampProfiniteEmbedding
import GroupApproximation.Higman.PairedReturnAmbientResiduallyFinite

/-!
# Profinite data of the paired-return benign witness

The paired-return ambient is a free lamp.  Killing its lamp factor retracts it
onto the canonical left copy of `F₃ × F₃`; hence that embedding is closed and
induces the full profinite topology.  This file packages every field of the
strengthened benign witness except the independently isolated finite-cover
statement that the literal five-generator cutter is closed.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnProfiniteWitness

noncomputable section

open PairedReturnCutter

abbrev P : Type := PairedReturnGraphIntersection.P
abbrev Edge : Subgroup P := PairedReturnGraphIntersection.M

/-- The paired ambient, viewed in free-lamp order. -/
def ambientEquivFreeLamp : Ambient ≃* FreeLamp P Edge Sync :=
  FreeLampFinitePresentation.swappedAmalgamEquivFreeLamp
    (K := Sync) P Edge

/-- Kill the synchronized lamp factor and retain the canonical left vertex. -/
def ambientBaseRet : Ambient →* P :=
  (FreeLampProfiniteEmbedding.baseRet P Edge Sync).comp
    ambientEquivFreeLamp.toMonoidHom

@[simp] theorem ambientBaseRet_left (p : P) :
    ambientBaseRet
      (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC p) = p := by
  have hleft : ambientEquivFreeLamp
      (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC p) =
        inAmbient P Edge Sync p := by
    exact FreeLampFinitePresentation.amalgamToFreeLamp_left
      (K := Sync) P Edge p
  change FreeLampProfiniteEmbedding.baseRet P Edge Sync
    (ambientEquivFreeLamp
      (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC p)) = p
  rw [hleft]
  exact FreeLampProfiniteEmbedding.baseRet_inAmbient P Edge Sync p

theorem ambientBaseRet_comp_left :
    ambientBaseRet.comp
        (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC) =
      MonoidHom.id P := by
  apply MonoidHom.ext
  exact ambientBaseRet_left

/-- The canonical paired-return vertex carries cofinally every finite quotient
of `P`. -/
theorem leftEmbedding_cofinal :
    CofinalProfiniteEmbedding
      (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC) :=
  CofinalProfiniteEmbedding.postcomp_of_retraction
    CofinalProfiniteEmbedding.id
    (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC)
    ambientBaseRet ambientBaseRet_comp_left

/-- The canonical paired-return vertex is profinitely closed in the ambient
free lamp. -/
theorem profiniteClosure_leftEmbedding :
    profiniteClosure
        (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC).range =
      (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC).range := by
  letI : Group.ResiduallyFinite Ambient :=
    PairedReturnAmbientResiduallyFinite.ambient_residuallyFinite
  exact profiniteClosure_range_eq_range_of_retraction
    (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC)
    ambientBaseRet ambientBaseRet_comp_left

/-- Every profinite field of the literal paired-return witness, with the
five-cutter closedness theorem as the single visible remaining input. -/
def witness
    (hclosed : profiniteClosure fiveCutter = fiveCutter) :
    ProfiniteBenignWitness Star.graphSub where
  witness := fiveCutterWitness.witness
  ambientRF := PairedReturnAmbientResiduallyFinite.ambient_residuallyFinite
  cutterClosed := hclosed
  embCofinal := leftEmbedding_cofinal
  embClosed := profiniteClosure_leftEmbedding

end

end PairedReturnProfiniteWitness
end Higman
end GroupApproximation
