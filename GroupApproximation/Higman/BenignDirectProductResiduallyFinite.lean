import GroupApproximation.Higman.BenignClosure
import GroupApproximation.Sofic.ProfiniteFiniteIndexPromotion
import GroupApproximation.Sofic.ProfiniteRetract

/-!
# Residual finiteness through Higman's direct-product benign operations

The intersection and preimage witnesses in `Benign` and `BenignClosure` use
only direct products.  This file records the corresponding stronger invariant:
if the input witness ambients are residually finite and their cutters are
profinitely closed, then the constructed ambient is residually finite and its
new cutter is profinitely closed.

This leaves the benign join as the only operation whose *output cutter*
requires a normal-form/separability argument.  Its ambient RF permanence is
proved separately in `BenignJoinResiduallyFinite`.
-/

namespace GroupApproximation
namespace Higman
namespace BenignDirectProductResiduallyFinite

noncomputable section

variable {G N : Type} [Group G] [Group N]

/-! ## Closed intersections -/

/-- An intersection of two profinitely closed subgroups is profinitely
closed. -/
theorem profiniteClosure_inf_eq_of_closed {K : Type} [Group K]
    (L₁ L₂ : Subgroup K)
    (hL₁ : profiniteClosure L₁ = L₁)
    (hL₂ : profiniteClosure L₂ = L₂) :
    profiniteClosure (L₁ ⊓ L₂) = L₁ ⊓ L₂ := by
  apply le_antisymm
  · intro x hx
    apply Subgroup.mem_inf.mpr
    constructor
    · rw [← hL₁]
      exact profiniteClosure_mono inf_le_left hx
    · rw [← hL₂]
      exact profiniteClosure_mono inf_le_right hx
  · exact le_profiniteClosure (L₁ ⊓ L₂)

/-! ## The intersection witness -/

variable {H₁ H₂ : Subgroup G}
variable (w₁ : BenignWitness H₁) (w₂ : BenignWitness H₂)

/-- The product cutter is the intersection of the two coordinate preimages. -/
theorem inf_L_eq_comap_fst_inf_comap_snd :
    (w₁.inf w₂).L =
      w₁.L.comap (MonoidHom.fst w₁.K w₂.K) ⊓
        w₂.L.comap (MonoidHom.snd w₁.K w₂.K) := by
  ext z
  change (z.1 ∈ w₁.L ∧ z.2 ∈ w₂.L) ↔
    (z.1 ∈ w₁.L ∧ z.2 ∈ w₂.L)
  rfl

/-- The cutter of Higman's intersection witness is profinitely closed. -/
theorem profiniteClosure_inf_L
    (hL₁ : profiniteClosure w₁.L = w₁.L)
    (hL₂ : profiniteClosure w₂.L = w₂.L) :
    profiniteClosure (w₁.inf w₂).L = (w₁.inf w₂).L := by
  rw [inf_L_eq_comap_fst_inf_comap_snd]
  apply profiniteClosure_inf_eq_of_closed
  · exact profiniteClosure_comap_eq_of_closed w₁.L
      (MonoidHom.fst w₁.K w₂.K) hL₁
  · exact profiniteClosure_comap_eq_of_closed w₂.L
      (MonoidHom.snd w₁.K w₂.K) hL₂

/-- The ambient of Higman's intersection witness is residually finite. -/
theorem inf_ambient_residuallyFinite
    [Group.ResiduallyFinite w₁.K] [Group.ResiduallyFinite w₂.K] :
    Group.ResiduallyFinite (w₁.inf w₂).K := by
  change Group.ResiduallyFinite (w₁.K × w₂.K)
  infer_instance

/-! ## The preimage witness -/

variable (u : FPOvergroup G) (phi : G →* N)
variable {H : Subgroup N} (w : BenignWitness H)

/-- The cutter in the preimage witness is the preimage of the old cutter under
the second coordinate projection. -/
theorem comap_L_eq_comap_snd :
    (w.comap u phi).L = w.L.comap (MonoidHom.snd u.K w.K) := by
  ext z
  change (z.1 ∈ (⊤ : Subgroup u.K) ∧ z.2 ∈ w.L) ↔ z.2 ∈ w.L
  simp only [Subgroup.mem_top, true_and]

/-- The cutter of Higman's preimage witness is profinitely closed. -/
theorem profiniteClosure_comap_L
    (hL : profiniteClosure w.L = w.L) :
    profiniteClosure (w.comap u phi).L = (w.comap u phi).L := by
  rw [comap_L_eq_comap_snd]
  exact profiniteClosure_comap_eq_of_closed w.L
    (MonoidHom.snd u.K w.K) hL

/-- The ambient of Higman's preimage witness is residually finite. -/
theorem comap_ambient_residuallyFinite
    [Group.ResiduallyFinite u.K] [Group.ResiduallyFinite w.K] :
    Group.ResiduallyFinite (w.comap u phi).K := by
  change Group.ResiduallyFinite (u.K × w.K)
  infer_instance

end

end BenignDirectProductResiduallyFinite
end Higman
end GroupApproximation
