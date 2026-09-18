import GroupApproximation.Manuscript.NonMF.IntroCarto11BKQuestion
import GroupApproximation.Manuscript.NonMF.RelatedBK.LocalizationTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# Intro cartography, lane 11: the BK QD question with the localization gap closed

`non_mf_groups_exist.tex` L315--316:

> It also asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal;

This module feeds the corpus theorem `RelatedBK.coronaUCPFiniteCoordinateLocalization`
into the reductions of `IntroCarto11BKQuestion`. It is kept separate so that a renamed
in-flight localization theorem only touches this file.

The endpoints still take `IntroCarto10.NFQuasidiagonalStatement`, the NF ⇒ QD target of
lane nm-intro-09. When lane 09 lands, each endpoint closes by applying it to
`fun A _ hA ↦ isQuasidiagonalCStarAlgebra_of_isNFAlgebra hA`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto11

open GroupApproximation.CStarExactness

universe u

/-- **The BK QD question, restated for nuclear algebras**, modulo NF ⇒ QD
(lane nm-intro-09). -/
theorem blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_nfQuasidiagonal
    (hNFQD : IntroCarto10.NFQuasidiagonalStatement.{u}) :
    RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        IsNuclearCStarAlgebra A → IsStablyFiniteCStarAlgebra A → IsMFAlgebra A :=
  blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_localization_of_nfQuasidiagonal
    hNFQD RelatedBK.coronaUCPFiniteCoordinateLocalization

/-- **The question as a coincidence of classes**, modulo NF ⇒ QD (lane nm-intro-09). -/
theorem blackadarKirchbergQuasidiagonalQuestion_iff_stablyFinite_iff_mf_of_nfQuasidiagonal
    (hNFQD : IntroCarto10.NFQuasidiagonalStatement.{u}) :
    RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        IsNuclearCStarAlgebra A →
          (IsStablyFiniteCStarAlgebra A ↔ IsMFAlgebra A) :=
  blackadarKirchbergQuasidiagonalQuestion_iff_stablyFinite_iff_mf_of_localization_of_nfQuasidiagonal
    hNFQD RelatedBK.coronaUCPFiniteCoordinateLocalization

end IntroCarto11
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_nfQuasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.blackadarKirchbergQuasidiagonalQuestion_iff_stablyFinite_iff_mf_of_nfQuasidiagonal
