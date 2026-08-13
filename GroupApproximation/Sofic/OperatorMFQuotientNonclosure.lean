import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.FreeGroupResiduallyFinite
import GroupApproximation.Sofic.LiteralNonMFPresentation
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Operator-MF groups are not closed under quotients

The verified finitely presented non-MF group is a presented quotient of the
free group on its finite generator type.  Free groups are residually finite,
hence operator-MF.  This gives an unconditional machine-checked quotient
counterexample using the formal Shalom-cover witness.  It is the formal
companion of manuscript Corollary `cor:quotclosure`; the paper's sharper
literal source `F_8` belongs to the separate eight-generator presentation.
-/

namespace GroupApproximation
namespace OperatorMFQuotientNonclosure

open ChosenMarkedPresentation ChosenNonMFTheorem

/-- The finite-rank free group on the chosen marked presentation's generator
type is operator-MF. -/
theorem source_isOperatorMF : IsOperatorMF (FreeGroup Generator) :=
  isOperatorMF_of_residuallyFinite

/-- The canonical presentation map from the finite-rank free group onto the
verified marked group is surjective. -/
theorem quotientMap_surjective :
    Function.Surjective
      (PresentedGroup.mk (relators : Set (FreeGroup Generator))) :=
  PresentedGroup.mk_surjective (relators : Set (FreeGroup Generator))

/-- A concrete operator-MF group has a non-operator-MF quotient. -/
theorem operatorMF_not_closed_under_this_quotient :
    IsOperatorMF (FreeGroup Generator) ∧
      Function.Surjective
        (PresentedGroup.mk (relators : Set (FreeGroup Generator))) ∧
      ¬ IsOperatorMF MarkedGroup :=
  ⟨source_isOperatorMF, quotientMap_surjective,
    chosenFinitelyPresented_not_isOperatorMF.2⟩

end OperatorMFQuotientNonclosure

namespace LiteralOperatorMFQuotientControls

open LiteralNonMFPresentation

/-- The free group on the literal presentation's eight-letter alphabet is
operator-MF.  This is independent of any analytic claim about its quotient. -/
theorem source_isOperatorMF : IsOperatorMF (FreeGroup Generator) :=
  isOperatorMF_of_residuallyFinite

/-- The canonical map from the rank-eight free group onto the literal
presented group is surjective. -/
theorem quotientMap_surjective :
    Function.Surjective
      (PresentedGroup.mk (relators : Set (FreeGroup Generator))) :=
  PresentedGroup.mk_surjective (relators : Set (FreeGroup Generator))

end LiteralOperatorMFQuotientControls
end GroupApproximation
