import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.VerticalEquiv
import GroupApproximation.Sofic.CommensurabilityInvariance
import GroupApproximation.Sofic.AlternatingLampExactRadical
import GroupApproximation.Manuscript.SpectralPaper.MainTheorems
import GroupApproximation.Meta.AxiomGuard

/-!
# `G_*` is residually finite and MF

Manuscript `non_mf_group_notes.tex`, `cor:notes-a5-relation` (tex lines 2052--2073):

> the quotient `W_{A5}/⟨⟨r⟩⟩ ≅ G_*` is residually finite and MF.

The repository proves both properties for the vertical group `Vertical conjD conjD_injective`
(`AlternatingLampFamily.vertical_isResiduallyFinite` and the vertical conjunct of
`SpectralPaper.oneInvisibleRelationPackage`); they transport to the literal ascending HNN
extension `Gstar` along `gstarEquivVertical`.

Main declarations:

* `gstar_residuallyFinite` — `IsResiduallyFinite Gstar`;
* `gstar_isOperatorMF` — `IsOperatorMF Gstar`.
-/

namespace GroupApproximation.Full.NN05

open MarkedCompression ExplicitLinearModel

/-- **`G_*` is residually finite.** -/
theorem gstar_residuallyFinite : IsResiduallyFinite Gstar :=
  CommensurabilityInvariance.isResiduallyFinite_of_mulEquiv gstarEquivVertical.symm
    AlternatingLampFamily.vertical_isResiduallyFinite

/-- The vertical group `V(Γ̄, conjD)` is operator-MF (conjunct of
`SpectralPaper.oneInvisibleRelationPackage`). -/
theorem verticalConjD_isOperatorMF : IsOperatorMF (Vertical conjD conjD_injective) :=
  SpectralPaper.oneInvisibleRelationPackage.2.2.2.2.2.2.2.1

/-- **`G_*` is MF**: it has a faithful representation into the corona `∏ M_n / ⊕ M_n`. -/
theorem gstar_isOperatorMF : IsOperatorMF Gstar :=
  CommensurabilityInvariance.isOperatorMF_of_mulEquiv gstarEquivVertical.symm
    verticalConjD_isOperatorMF

#audit_axioms gstar_residuallyFinite
#audit_axioms gstar_isOperatorMF

end GroupApproximation.Full.NN05
