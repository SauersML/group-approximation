import GroupApproximation.Computability.FreeEdgeTowerExactEdgeHom

/-!
# Exact semantics for one raw HNN edge

This is the subgroup-equivalence counterpart of
`FreeEdgeTowerIteration.EdgeFreeness`.
-/

namespace GroupApproximation
namespace FreeEdgeTowerExactIteration

open HNNExtension
open PresentationCodes FreeEdgeTowerCode FreeEdgeTowerSemantics

noncomputable section

namespace EdgeEquivalence

variable {c : PresentationCode} {edges : List (Raw × Raw)}

/-- Britton injectivity transported through the literal presentation
equivalence. -/
theorem oldHom_injective (E : EdgeEquivalence c edges) :
    Function.Injective E.oldHom :=
  (edgeCodeEquivOfSubgroupEquiv c edges E.equiv E.generator).symm.injective.comp
    (HNNExtension.of_injective E.equiv)

/-- The exact old-group embedding preserves the literal numbered generators.
This is the marked-word compatibility needed by a finite-output compiler. -/
theorem oldHom_generator (E : EdgeEquivalence c edges)
    (i : Fin (genCount c)) :
    E.oldHom (PresentedGroup.of i) =
      PresentedGroup.of (letterOf (edgeCode c edges) i) := by
  apply (edgeCodeEquivOfSubgroupEquiv c edges E.equiv E.generator).injective
  rw [edgeCodeEquivOfSubgroupEquiv_oldGenerator]
  have hi : letterOf c (i : ℕ) = i := by
    apply Fin.ext
    exact RawWord.letterOf_val_of_lt c i.isLt
  rw [hi]
  change (edgeCodeEquivOfSubgroupEquiv c edges E.equiv E.generator)
      ((edgeCodeEquivOfSubgroupEquiv c edges E.equiv E.generator).symm
        (HNNExtension.of (PresentedGroup.of i))) =
    HNNExtension.of (PresentedGroup.of i)
  exact MulEquiv.apply_symm_apply _ _

end EdgeEquivalence

end


end FreeEdgeTowerExactIteration
end GroupApproximation
