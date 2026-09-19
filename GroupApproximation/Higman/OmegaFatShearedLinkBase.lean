import GroupApproximation.Higman.OmegaFatShearedLinkSemantic
import GroupApproximation.Higman.OmegaBlockWindowBenign

/-!
# The zero-window sheared-link cutter

At width zero the sheared link has one generator.  This is the base case for
the Higman stable-hull construction of the full finite-window cutter.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq
open GroupApproximation.Higman.Conj (F₃)

theorem fatShearedBlockLink_zero_eq :
    fatShearedBlockLink 0 =
      Subgroup.closure {slimFatSemanticBaseEmb 0 (slimLinkElem 0 0)} := by
  rw [fatShearedBlockLink_eq_map]
  unfold slimLink
  rw [blockSet_zero_eq_Zset, MonoidHom.map_closure]
  congr 1
  ext x
  simp [Zset]

theorem fatShearedBlockLink_zero_fg : (fatShearedBlockLink 0).FG := by
  rw [fatShearedBlockLink_zero_eq]
  exact (Subgroup.fg_iff _).mpr
    ⟨{slimFatSemanticBaseEmb 0 (slimLinkElem 0 0)}, rfl,
      Set.finite_singleton _⟩

/-- The first unconditional finite cutter in the sheared-link induction. -/
theorem benignTF_fatShearedBlockLink_zero :
    BenignTF (fatShearedBlockLink 0) := by
  letI : Group.IsFinitelyPresented (FatCent3 0) :=
    isFinitelyPresented_fatCent3 0
  letI : Group.IsFinitelyPresented (FatCent3 0 × F₃) := inferInstance
  exact benignTF_of_fg
    (IsPowerTorsionFree.prod (isPowerTorsionFree_fatCent3 0)
      IsPowerTorsionFree.of_isMulTorsionFree)
    fatShearedBlockLink_zero_fg

end Omega
end Higman
end GroupApproximation
