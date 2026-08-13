import GroupApproximation.Sofic.MFDefinitions
import GroupApproximation.Sofic.ChosenNonMFTheorem

/-!
# The non-MF witness under every analytic meaning

The standard group, CDE-corona, ultraproduct, finite-set, and MF-algebra
meanings are equivalent for the chosen countable group.  The trace-preserving,
regular, reduced-C-star, and full-C-star meanings are stronger, so the same
counterexample rules them out by contraposition.

The unrelated modular-by-finite predicate is intentionally absent: the
letters “MF” have a different meaning there, and no implication between that
subgroup-lattice property and matrix-factorization MF is asserted.
-/

namespace GroupApproximation
namespace ChosenNonMFTheorem

open ChosenMarkedPresentation

/-- The chosen finitely presented counterexample fails every matrix and
C-star-algebra meaning of MF formalized in `MFDefinitions`. -/
theorem chosenFinitelyPresented_not_all_analyticMFDefinitions :
    Group.IsFinitelyPresented MarkedGroup ∧
      ¬ IsGroupTheoreticMF MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup ∧
      ¬ IsUltraproductMF MarkedGroup ∧
      ¬ IsFiniteSetMF MarkedGroup ∧
      ¬ HasMFAlgebraUnitaryEmbedding MarkedGroup ∧
      ¬ IsTracePreservingMF MarkedGroup ∧
      ¬ IsRegularMF MarkedGroup ∧
      ¬ IsReducedGroupCStarMF MarkedGroup ∧
      ¬ IsFullGroupCStarMF MarkedGroup := by
  have h : ¬ IsGroupTheoreticMF MarkedGroup :=
    chosenFinitelyPresented_not_isOperatorMF.2
  exact ⟨chosenFinitelyPresented_not_isOperatorMF.1, h,
    not_isCDEOperatorMF_of_not_isGroupTheoreticMF h,
    not_isUltraproductMF_of_not_isGroupTheoreticMF h,
    not_isFiniteSetMF_of_not_isGroupTheoreticMF h,
    not_hasMFAlgebraUnitaryEmbedding_of_not_isGroupTheoreticMF h,
    not_isTracePreservingMF_of_not_isGroupTheoreticMF h,
    not_isRegularMF_of_not_isGroupTheoreticMF h,
    not_isReducedGroupCStarMF_of_not_isGroupTheoreticMF h,
    not_isFullGroupCStarMF_of_not_isGroupTheoreticMF h⟩

end ChosenNonMFTheorem
end GroupApproximation
