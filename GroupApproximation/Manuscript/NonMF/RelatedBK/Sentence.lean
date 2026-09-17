import GroupApproximation.Manuscript.NonMF.RelatedBK.ConverseReduction
import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Manuscript.NonMF.PriorWorkBlackadarKirchberg
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): the printed sentence

Census row `14ee41b7f3cc`, `non_mf_groups_exist.tex` L310 (Related work):

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

"Developed these notions" is attribution. The mathematical claim is the
equivalence NF ⇔ nuclear ∧ MF for separable C-star algebras. Here NF is the
repository's finite-local predicate `IsNFAlgebra`, nuclear is
`IsNuclearCStarAlgebra`, and MF is `IsMFAlgebra`, which is separability
together with `HasMFEmbedding`. All three are stated for unital C-star algebras.

## What is proved

* `manuscriptSentence_blackadarKirchbergNFForward` proves NF ⇒ nuclear ∧ MF
  with no extra hypothesis. It reuses `IsNFAlgebra.isNuclearCStarAlgebra` and
  `IsNFAlgebra.isMFAlgebra`.
* `blackadarKirchbergNFIff_of_coronaUCPFiniteCoordinateLocalization` proves the
  full equivalence from the one named gap
  `CoronaUCPFiniteCoordinateLocalizationStatement`. The converse direction is
  `isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra_of_coronaUCPFiniteCoordinateLocalization`,
  and the printed separability hypothesis is spent there as `⟨hsep, hmf⟩`.
* `blackadarKirchbergNFConverseInput_of_coronaUCPFiniteCoordinateLocalization`
  derives the corpus's cited interface `PriorWork.BlackadarKirchbergNFConverseInput`
  from the same gap. That turns the old literature input into the narrower
  localization principle.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedBK

open GroupApproximation.CStarExactness

universe u

/-- **The printed sentence, forward half.** A separable NF C-star algebra is
nuclear and MF. -/
theorem manuscriptSentence_blackadarKirchbergNFForward
    {A : Type u} [CStarAlgebra A]
    (_hsep : TopologicalSpace.SeparableSpace A) (hA : IsNFAlgebra A) :
    IsNuclearCStarAlgebra A ∧ IsMFAlgebra A :=
  ⟨hA.isNuclearCStarAlgebra, hA.isMFAlgebra⟩

/-- **The printed equivalence, modulo the localization gap.** A separable
C-star algebra is NF if and only if it is nuclear and has an MF embedding. -/
theorem blackadarKirchbergNFIff_of_coronaUCPFiniteCoordinateLocalization
    (hloc : CoronaUCPFiniteCoordinateLocalizationStatement)
    {A : Type u} [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A) :
    IsNFAlgebra A ↔ IsNuclearCStarAlgebra A ∧ HasMFEmbedding A := by
  constructor
  · intro hA
    exact ⟨hA.isNuclearCStarAlgebra, hA.isMFAlgebra.2⟩
  · rintro ⟨hnuc, hmf⟩
    exact
      isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra_of_coronaUCPFiniteCoordinateLocalization
        hloc hnuc ⟨hsep, hmf⟩

/-- The localization gap implies the corpus's cited Blackadar--Kirchberg
converse interface. -/
theorem blackadarKirchbergNFConverseInput_of_coronaUCPFiniteCoordinateLocalization
    (hloc : CoronaUCPFiniteCoordinateLocalizationStatement) :
    PriorWork.BlackadarKirchbergNFConverseInput.{u} := by
  intro A _ hnuc hMF
  exact
    isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra_of_coronaUCPFiniteCoordinateLocalization
      hloc hnuc hMF

end RelatedBK
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.RelatedBK

#audit_axioms manuscriptSentence_blackadarKirchbergNFForward
#audit_axioms blackadarKirchbergNFIff_of_coronaUCPFiniteCoordinateLocalization
#audit_axioms blackadarKirchbergNFConverseInput_of_coronaUCPFiniteCoordinateLocalization
