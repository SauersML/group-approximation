import GroupApproximation.Higman.MikhailovaFiberProductProfinite
import GroupApproximation.Higman.MikhailovaRankThreeWitness
import GroupApproximation.Sofic.FreeGroupResiduallyFinite

/-!
# Profinite structure of the rank-three Mikhailova witness

On the positive branch the presented marked quotient is residually finite.
The cutting subgroup is then the pullback of the profinitely closed
Mikhailova fibre product along the second projection.  Independently, the
marked source embedding is split by the first projection, so its range is
also profinitely closed in the product-of-free-groups ambient.
-/

namespace GroupApproximation
namespace Higman
namespace MikhailovaRankThree

open Mikhailova

variable {X : Type}

/-- Projection from the rank-three ambient to the Mikhailova square. -/
def mikhailovaProjection :
    Ambient X →* FreeGroup X × FreeGroup X :=
  MonoidHom.snd Source (FreeGroup X × FreeGroup X)

/-- The displayed cutter is exactly the pullback along the second
projection. -/
theorem cuttingSubgroup_eq_comap (R : Set (FreeGroup X)) :
    cuttingSubgroup R =
      (Mikhailova.freeSubgroup R).comap mikhailovaProjection := by
  ext p
  rcases p with ⟨f, uv⟩
  change (f ∈ (⊤ : Subgroup Source) ∧ uv ∈ Mikhailova.freeSubgroup R) ↔
    uv ∈ Mikhailova.freeSubgroup R
  simp

/-- Residual finiteness of the presented quotient makes the rank-three
cutting subgroup profinitely closed. -/
theorem profiniteClosure_cuttingSubgroup
    (R : Set (FreeGroup X))
    [Group.ResiduallyFinite
      (FreeGroup X ⧸ Subgroup.normalClosure R)] :
    profiniteClosure (cuttingSubgroup R) = cuttingSubgroup R := by
  rw [cuttingSubgroup_eq_comap]
  exact profiniteClosure_comap_eq_of_closed _ _
    (Mikhailova.profiniteClosure_freeSubgroup R)

/-- The first projection retracts every marked source embedding. -/
def inputProjection : Ambient X →* Source :=
  MonoidHom.fst Source (FreeGroup X × FreeGroup X)

theorem inputProjection_comp_inputHom (words : Source →* FreeGroup X) :
    inputProjection.comp (inputHom words) = MonoidHom.id Source := by
  ext f
  rfl

/-- The marked rank-three source has profinitely closed range in its
product-of-free-groups ambient. -/
theorem profiniteClosure_inputHom_range
    (words : Source →* FreeGroup X) :
    profiniteClosure (inputHom words).range = (inputHom words).range := by
  letI : Group.ResiduallyFinite (Ambient X) := inferInstance
  exact profiniteClosure_range_eq_range_of_retraction
    (inputHom words) inputProjection (inputProjection_comp_inputHom words)

end MikhailovaRankThree
end Higman
end GroupApproximation
