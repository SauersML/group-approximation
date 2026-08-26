import GroupApproximation.Higman.MikhailovaFiberProductProfinite
import GroupApproximation.Higman.MikhailovaRankThreeWitness

/-!
# Profinite closedness of the rank-three Mikhailova cutter

The full cutter is the inverse image of the Mikhailova fibre product under
projection to the final two free-group coordinates.  Thus the fibre-product
closedness theorem immediately gives the exact positive-branch separability
statement used by the central HNN layer.
-/

namespace GroupApproximation
namespace Higman
namespace MikhailovaRankThree

open Mikhailova

/-- The rank-three cutter is the inverse image of the Mikhailova subgroup
under projection to the final two coordinates. -/
theorem cuttingSubgroup_eq_comap {X : Type*} (R : Set (FreeGroup X)) :
    cuttingSubgroup R =
      (freeSubgroup R).comap
        (MonoidHom.snd Source (FreeGroup X × FreeGroup X)) := by
  ext p
  simp [cuttingSubgroup]

/-- If the finite marked target is residually finite, the complete
rank-three cutting subgroup is profinitely closed in its free product
ambient. -/
theorem profiniteClosure_cuttingSubgroup
    {X : Type*} (R : Set (FreeGroup X))
    [Group.ResiduallyFinite
      (FreeGroup X ⧸ Subgroup.normalClosure R)] :
    profiniteClosure (cuttingSubgroup R) = cuttingSubgroup R := by
  rw [cuttingSubgroup_eq_comap]
  exact profiniteClosure_comap_eq_of_closed _ _
    (profiniteClosure_freeSubgroup R)

end MikhailovaRankThree
end Higman
end GroupApproximation
