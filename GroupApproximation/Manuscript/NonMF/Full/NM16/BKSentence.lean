import GroupApproximation.Manuscript.NonMF.Full.NM16.BKConverse
import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Analysis.LanceNFUnitalCPAP
import GroupApproximation.Manuscript.NonMF.PriorWorkBlackadarKirchberg
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): the printed sentence, unconditionally

Census row `14ee41b7f3cc`, `non_mf_groups_exist.tex` L310--315 (Related work):

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

"Developed these notions" is attribution. The mathematical claim is the
equivalence NF ⇔ nuclear ∧ MF for separable C-star algebras. Here NF is the
repository's finite-local predicate `IsNFAlgebra`, nuclear is
`IsNuclearCStarAlgebra`, and MF is `IsMFAlgebra`, which is separability
together with `HasMFEmbedding`. All three are stated for unital C-star algebras.

Lane NM16 duplicates the foreign `NonMF/RelatedBK/Sentence` here. The foreign
version takes the localization claim as a hypothesis. This version has no
hypothesis beyond the printed separability.

## What is proved

* `manuscriptSentence_blackadarKirchbergNFForward`: NF ⇒ nuclear ∧ MF, from
  `IsNFAlgebra.isNuclearCStarAlgebra` and `IsNFAlgebra.isMFAlgebra`.
* `manuscriptSentence_blackadarKirchbergNFIff`: the full printed equivalence.
  The converse is `isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra` from
  `Full/NM16/BKConverse`, applied to `⟨hsep, hmf⟩`.
* `blackadarKirchbergNFConverseInput`: the corpus's cited interface
  `PriorWork.BlackadarKirchbergNFConverseInput` holds at every universe. So
  every consumer of that binder in `PriorWorkBlackadarKirchberg` can be
  discharged, for example `nuclearReducedCPAP_of_isNuclear_of_isMFAlgebra`.
-/

namespace GroupApproximation.Full.NM16

open GroupApproximation.CStarExactness GroupApproximation.ReducedGroupCStarTrace

universe u

/-- **The printed sentence, forward half** (tex L310--315). A separable NF
C-star algebra is nuclear and MF. -/
theorem manuscriptSentence_blackadarKirchbergNFForward
    {A : Type u} [CStarAlgebra A]
    (_hsep : TopologicalSpace.SeparableSpace A) (hA : IsNFAlgebra A) :
    IsNuclearCStarAlgebra A ∧ IsMFAlgebra A :=
  ⟨hA.isNuclearCStarAlgebra, hA.isMFAlgebra⟩

/-- **The printed sentence** (tex L310--315, census `14ee41b7f3cc`). A separable
C-star algebra is NF if and only if it is nuclear and has an MF embedding. -/
theorem manuscriptSentence_blackadarKirchbergNFIff
    {A : Type u} [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A) :
    IsNFAlgebra A ↔ IsNuclearCStarAlgebra A ∧ HasMFEmbedding A := by
  constructor
  · intro hA
    exact ⟨hA.isNuclearCStarAlgebra, hA.isMFAlgebra.2⟩
  · rintro ⟨hnuc, hmf⟩
    exact isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra hnuc ⟨hsep, hmf⟩

/-- The corpus's cited Blackadar--Kirchberg converse interface holds
unconditionally (tex L310--315). -/
theorem blackadarKirchbergNFConverseInput :
    Manuscript.NonMF.PriorWork.BlackadarKirchbergNFConverseInput.{u} := by
  intro A _ hnuc hMF
  exact isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra hnuc hMF

/-- A nuclear MF reduced group C-star algebra has the Lance CPAP. This is
`PriorWork.blackadarKirchberg_nuclearReducedCPAP_of_isNuclear_of_isMFAlgebra`
with its binder discharged. -/
theorem nuclearReducedCPAP_of_isNuclear_of_isMFAlgebra
    (G : Type) [Group G]
    (hnuc : IsNuclearCStarAlgebra (ReducedGroupCStar G))
    (hMF : IsMFAlgebra (ReducedGroupCStar G)) :
    NuclearReducedCPAP G :=
  Manuscript.NonMF.PriorWork.blackadarKirchberg_nuclearReducedCPAP_of_isNuclear_of_isMFAlgebra
    blackadarKirchbergNFConverseInput.{0} G hnuc hMF

/-- `PriorWork.blackadarKirchberg_nfAlgebra_iff` with its binder discharged. -/
theorem priorWork_blackadarKirchberg_nfAlgebra_iff {A : Type u} [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A) :
    IsNFAlgebra A ↔ IsNuclearCStarAlgebra A ∧ HasMFEmbedding A :=
  Manuscript.NonMF.PriorWork.blackadarKirchberg_nfAlgebra_iff
    blackadarKirchbergNFConverseInput hsep

end GroupApproximation.Full.NM16

open GroupApproximation.Full.NM16

#audit_axioms manuscriptSentence_blackadarKirchbergNFForward
#audit_axioms manuscriptSentence_blackadarKirchbergNFIff
#audit_axioms blackadarKirchbergNFConverseInput
#audit_axioms nuclearReducedCPAP_of_isNuclear_of_isMFAlgebra
#audit_axioms priorWork_blackadarKirchberg_nfAlgebra_iff
