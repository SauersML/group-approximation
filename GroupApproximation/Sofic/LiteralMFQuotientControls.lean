import GroupApproximation.Sofic.FreeGroupResiduallyFinite
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# The literal rank-eight quotient counterexample

This file fixes the source as the standard rank-eight free group and the
quotient map as the canonical presentation map after the displayed ordering
of the eight literal generators.
-/

namespace GroupApproximation
namespace LiteralMFQuotientControls

open LiteralNonMFPresentation

noncomputable section

/-- The canonical map from the standard rank-eight free group onto the exact
literal presented group. -/
def quotientMap8 : FreeGroup (Fin 8) →* MarkedGroup :=
  (PresentedGroup.mk
    ((relators : Finset (FreeGroup Generator)) : Set (FreeGroup Generator))).comp
      (FreeGroup.map generatorEquivFin8.symm)

/-- The displayed eight generators generate the literal presented group. -/
theorem quotientMap8_surjective : Function.Surjective quotientMap8 :=
  (PresentedGroup.mk_surjective
      ((relators : Finset (FreeGroup Generator)) : Set (FreeGroup Generator))).comp
    (FreeGroup.map_surjective generatorEquivFin8.symm.surjective)

/-- MF is not closed under quotients: the exact literal group is the
displayed quotient of the MF group `F_8`. -/
theorem manuscriptQuotientNonclosure :
    IsCDEOperatorMF (FreeGroup (Fin 8)) ∧
      Function.Surjective quotientMap8 ∧
      ¬ IsCDEOperatorMF MarkedGroup := by
  exact ⟨(isCDEOperatorMF_iff_isOperatorMF _).2
      isOperatorMF_of_residuallyFinite,
    quotientMap8_surjective,
    LiteralNonMFEndpoint.literal_not_isCDEOperatorMF⟩

end

end LiteralMFQuotientControls
end GroupApproximation
