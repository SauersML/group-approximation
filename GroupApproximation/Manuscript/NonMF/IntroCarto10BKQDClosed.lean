import GroupApproximation.Manuscript.NonMF.IntroCarto10BKQDReduction
import GroupApproximation.Manuscript.NonMF.RelatedBK.LocalizationTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# Blackadar--Kirchberg QD corollaries with the localization gap closed

`non_mf_groups_exist.tex`, Related work, tex 312--316:

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

This module feeds the corpus theorem `RelatedBK.coronaUCPFiniteCoordinateLocalization`
into the reductions of `IntroCarto10BKQDReduction`. It is kept separate so that a
renamed in-flight localization theorem only touches this file.

* `isNFAlgebra_of_isNuclearCStarAlgebra_of_isQuasidiagonalCStarAlgebra` is fully
  unconditional: a nuclear quasidiagonal unital C⋆-algebra is NF.
* The remaining endpoints still take `NFQuasidiagonalStatement`, the NF ⇒ QD target
  of lane nm-intro-09, which is in flight. They are named `_of_nfQuasidiagonal`.
  Once lane 09 lands, each of them closes by applying it to
  `fun A _ hA ↦ isQuasidiagonalCStarAlgebra_of_isNFAlgebra hA`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto10

open GroupApproximation.CStarExactness

universe u

/-- **Nuclear and quasidiagonal implies NF** (unconditional). -/
theorem isNFAlgebra_of_isNuclearCStarAlgebra_of_isQuasidiagonalCStarAlgebra
    {A : Type u} [CStarAlgebra A]
    (hnuc : IsNuclearCStarAlgebra A) (hQD : RelatedTWW.IsQuasidiagonalCStarAlgebra A) :
    IsNFAlgebra A :=
  isNFAlgebra_of_isNuclearCStarAlgebra_of_isQuasidiagonalCStarAlgebra_of_localization
    RelatedBK.coronaUCPFiniteCoordinateLocalization hnuc hQD

/-- **Nuclear and MF implies quasidiagonal**, modulo NF ⇒ QD (lane nm-intro-09). -/
theorem isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_nfQuasidiagonal
    (hNFQD : NFQuasidiagonalStatement.{u})
    {A : Type u} [CStarAlgebra A]
    (hnuc : IsNuclearCStarAlgebra A) (hMF : IsMFAlgebra A) :
    RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_localization_of_nfQuasidiagonal
    hNFQD RelatedBK.coronaUCPFiniteCoordinateLocalization hnuc hMF

/-- **NF means nuclear and quasidiagonal**, modulo NF ⇒ QD (lane nm-intro-09). -/
theorem isNFAlgebra_iff_nuclear_and_quasidiagonal_of_nfQuasidiagonal
    (hNFQD : NFQuasidiagonalStatement.{u})
    {A : Type u} [CStarAlgebra A] :
    IsNFAlgebra A ↔
      IsNuclearCStarAlgebra A ∧ RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  isNFAlgebra_iff_nuclear_and_quasidiagonal_of_localization_of_nfQuasidiagonal
    hNFQD RelatedBK.coronaUCPFiniteCoordinateLocalization

/-- **For nuclear algebras, MF and quasidiagonal coincide**, modulo NF ⇒ QD
(lane nm-intro-09). -/
theorem nuclear_and_mf_iff_nuclear_and_quasidiagonal_of_nfQuasidiagonal
    (hNFQD : NFQuasidiagonalStatement.{u})
    {A : Type u} [CStarAlgebra A] :
    IsNuclearCStarAlgebra A ∧ IsMFAlgebra A ↔
      IsNuclearCStarAlgebra A ∧ RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  nuclear_and_mf_iff_nuclear_and_quasidiagonal_of_localization_of_nfQuasidiagonal
    hNFQD RelatedBK.coronaUCPFiniteCoordinateLocalization

end IntroCarto10
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto10.isNFAlgebra_of_isNuclearCStarAlgebra_of_isQuasidiagonalCStarAlgebra
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto10.isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_nfQuasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto10.isNFAlgebra_iff_nuclear_and_quasidiagonal_of_nfQuasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto10.nuclear_and_mf_iff_nuclear_and_quasidiagonal_of_nfQuasidiagonal
