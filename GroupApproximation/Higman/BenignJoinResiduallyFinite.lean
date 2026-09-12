import GroupApproximation.GroupTheory.CentralHNNResiduallyFinite
import GroupApproximation.Higman.BenignJoin
import GroupApproximation.Higman.CentralHNNFreeLabelFaithful
import GroupApproximation.Sofic.ProfiniteRetract
import GroupApproximation.Sofic.ProfiniteSplitEmbedding

/-!
# Residual finiteness of the two-HNN benign join

The join witness first takes the direct product of two witness ambients and
then adjoins two stable letters, centralizing `L₁ × ⊤` and `⊤ × L₂`.
If the two input ambients are residually finite and their cutters are
profinitely closed, both HNN stages are residually finite.  The second edge is
transported through the split base embedding of the first stage.
-/

namespace GroupApproximation
namespace Higman
namespace BenignJoinResiduallyFinite

noncomputable section

variable {G : Type} [Group G] {A₁ A₂ : Subgroup G}
variable (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂)

/-- The first product edge is the preimage of the first cutter under the first
coordinate projection. -/
theorem joinM₁_eq_comap_fst :
    joinM₁ w₁ w₂ = w₁.L.comap (MonoidHom.fst w₁.K w₂.K) := by
  ext z
  simp [joinM₁, Subgroup.mem_prod]

/-- The second product edge is the preimage of the second cutter under the
second coordinate projection. -/
theorem joinM₂_eq_comap_snd :
    joinM₂ w₁ w₂ = w₂.L.comap (MonoidHom.snd w₁.K w₂.K) := by
  ext z
  simp [joinM₂, Subgroup.mem_prod]

theorem profiniteClosure_joinM₁
    (hL₁ : profiniteClosure w₁.L = w₁.L) :
    profiniteClosure (joinM₁ w₁ w₂) = joinM₁ w₁ w₂ := by
  rw [joinM₁_eq_comap_fst]
  exact profiniteClosure_comap_eq_of_closed w₁.L
    (MonoidHom.fst w₁.K w₂.K) hL₁

theorem profiniteClosure_joinM₂
    (hL₂ : profiniteClosure w₂.L = w₂.L) :
    profiniteClosure (joinM₂ w₁ w₂) = joinM₂ w₁ w₂ := by
  rw [joinM₂_eq_comap_snd]
  exact profiniteClosure_comap_eq_of_closed w₂.L
    (MonoidHom.snd w₁.K w₂.K) hL₂

/-- Killing the central stable letter splits the base embedding. -/
theorem baseRet_comp_of (M : Subgroup (JoinBase w₁ w₂)) :
    (CentralHNNFreeLabel.baseRet M).comp
        (HNNExtension.of : JoinBase w₁ w₂ →* CentHNN M) =
      MonoidHom.id (JoinBase w₁ w₂) := by
  apply MonoidHom.ext
  intro g
  simp [CentralHNNFreeLabel.baseRet_of]

/-- The first central HNN stage of the join is residually finite. -/
theorem level1_residuallyFinite
    [Group.ResiduallyFinite w₁.K] [Group.ResiduallyFinite w₂.K]
    (hL₁ : profiniteClosure w₁.L = w₁.L) :
    Group.ResiduallyFinite (JoinLevel1 w₁ w₂) := by
  exact CentralHNNResiduallyFinite.centralHNN_residuallyFinite
    (joinM₁ w₁ w₂) (profiniteClosure_joinM₁ w₁ w₂ hL₁)

/-- The second product edge remains closed after transport into the first HNN
stage. -/
theorem profiniteClosure_joinM₂'
    [Group.ResiduallyFinite w₁.K] [Group.ResiduallyFinite w₂.K]
    (hL₁ : profiniteClosure w₁.L = w₁.L)
    (hL₂ : profiniteClosure w₂.L = w₂.L) :
    profiniteClosure (joinM₂' w₁ w₂) = joinM₂' w₁ w₂ := by
  letI : Group.ResiduallyFinite (JoinLevel1 w₁ w₂) :=
    level1_residuallyFinite w₁ w₂ hL₁
  exact profiniteClosure_map_eq_of_split_closed
    (HNNExtension.of : JoinBase w₁ w₂ →* JoinLevel1 w₁ w₂)
    (CentralHNNFreeLabel.baseRet (joinM₁ w₁ w₂))
    (baseRet_comp_of w₁ w₂ (joinM₁ w₁ w₂))
    (joinM₂ w₁ w₂) (profiniteClosure_joinM₂ w₁ w₂ hL₂)

/-- **RF preservation for the ambient of Higman's benign join.** -/
theorem level2_residuallyFinite
    [Group.ResiduallyFinite w₁.K] [Group.ResiduallyFinite w₂.K]
    (hL₁ : profiniteClosure w₁.L = w₁.L)
    (hL₂ : profiniteClosure w₂.L = w₂.L) :
    Group.ResiduallyFinite (JoinLevel2 w₁ w₂) := by
  letI : Group.ResiduallyFinite (JoinLevel1 w₁ w₂) :=
    level1_residuallyFinite w₁ w₂ hL₁
  exact CentralHNNResiduallyFinite.centralHNN_residuallyFinite
    (joinM₂' w₁ w₂)
    (profiniteClosure_joinM₂' w₁ w₂ hL₁ hL₂)

end

end BenignJoinResiduallyFinite
end Higman
end GroupApproximation
