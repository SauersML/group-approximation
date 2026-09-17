import GroupApproximation.Manuscript.NonMF.IntroCarto10BKQDReduction
import GroupApproximation.Manuscript.NonMF.RelatedTWW.Elementary
import GroupApproximation.Meta.AxiomGuard

/-!
# Intro cartography, lane 11: the Blackadar--Kirchberg QD question for nuclear algebras

`non_mf_groups_exist.tex` L315--316 (Related work, paragraph starting at L310):

> It also asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal;

The question is `RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion`. This module
restates it downstream of the Blackadar--Kirchberg theorem "nuclear and MF implies
quasidiagonal". In the restated form, every separable nuclear stably finite
C⋆-algebra is MF. The census row is `attribution`, so this module strengthens the
corpus and changes no census status.

## Proof route

* `→` is unconditional, because quasidiagonal implies MF
  (`RelatedTWW.isMFAlgebra_of_isQuasidiagonalCStarAlgebra`).
* `←` is lane nm-intro-10,
  `IntroCarto10.isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_localization_of_nfQuasidiagonal`:
  nuclear and MF implies quasidiagonal.

## The remaining gap, and why it is true and strictly smaller

Lane 10 still takes `IntroCarto10.NFQuasidiagonalStatement` ("NF implies quasidiagonal"),
which is the target of lane nm-intro-09 and is not on disk yet. The endpoints
here carry it as the hypothesis `hNFQD`, with the suffix `_of_nfQuasidiagonal`.

The statement is TRUE. Take a dense sequence, let `F_n` be its first `n` terms, and use
tolerance `1/(n+1)`. The local NF down maps are CPC, hence star-preserving. They are
approximately multiplicative on `F_n`, and density upgrades that to all of `A`. They
also recover norms: `‖a‖ ≤ ‖up (down a)‖ + ε ≤ ‖down a‖ + ε`, because `up` is
contractive.

The statement is strictly smaller in proof content than the lane target. The target
equivalence also contains the Blackadar--Kirchberg converse "nuclear and MF implies
NF", which the corpus proves (the corona localization plus `ConverseReduction`).
`NFQuasidiagonalStatement` is only the elementary NF ⇒ QD half.

The closed forms, with the localization theorem fed in, are in
`IntroCarto11BKQuestionClosed`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto11

open GroupApproximation.CStarExactness

universe u

/-- **The unconditional half.** If the Blackadar--Kirchberg question has a positive
answer, then every separable nuclear stably finite C⋆-algebra is MF. -/
theorem nuclearStablyFiniteMF_of_blackadarKirchbergQuasidiagonalQuestion
    (hq : RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u}) :
    ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
      IsNuclearCStarAlgebra A → IsStablyFiniteCStarAlgebra A → IsMFAlgebra A := by
  intro A _ hsep hnuc hsf
  exact RelatedTWW.isMFAlgebra_of_isQuasidiagonalCStarAlgebra (hq A hsep hnuc hsf)

/-- **The BK QD question, restated for nuclear algebras**, modulo the localization
principle and NF ⇒ QD. The question holds exactly when every separable nuclear stably
finite C⋆-algebra is MF. -/
theorem blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_localization_of_nfQuasidiagonal
    (hNFQD : IntroCarto10.NFQuasidiagonalStatement.{u})
    (hloc : RelatedBK.CoronaUCPFiniteCoordinateLocalizationStatement) :
    RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        IsNuclearCStarAlgebra A → IsStablyFiniteCStarAlgebra A → IsMFAlgebra A := by
  refine ⟨nuclearStablyFiniteMF_of_blackadarKirchbergQuasidiagonalQuestion, ?_⟩
  intro h A _ hsep hnuc hsf
  exact IntroCarto10.isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_localization_of_nfQuasidiagonal
    hNFQD hloc hnuc (h A hsep hnuc hsf)

/-- **The question as a coincidence of classes**, modulo the localization principle
and NF ⇒ QD. For separable nuclear C⋆-algebras, the question holds exactly when stable
finiteness and MF coincide. The implication "MF implies stably finite" is
unconditional. -/
theorem blackadarKirchbergQuasidiagonalQuestion_iff_stablyFinite_iff_mf_of_localization_of_nfQuasidiagonal
    (hNFQD : IntroCarto10.NFQuasidiagonalStatement.{u})
    (hloc : RelatedBK.CoronaUCPFiniteCoordinateLocalizationStatement) :
    RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        IsNuclearCStarAlgebra A →
          (IsStablyFiniteCStarAlgebra A ↔ IsMFAlgebra A) := by
  constructor
  · intro hq A _ hsep hnuc
    exact ⟨nuclearStablyFiniteMF_of_blackadarKirchbergQuasidiagonalQuestion hq A hsep hnuc,
      fun hMF ↦ RelatedTWW.isStablyFiniteCStarAlgebra_of_hasMFEmbedding hMF.2⟩
  · intro h A _ hsep hnuc hsf
    exact IntroCarto10.isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_localization_of_nfQuasidiagonal
      hNFQD hloc hnuc ((h A hsep hnuc).mp hsf)

end IntroCarto11
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.nuclearStablyFiniteMF_of_blackadarKirchbergQuasidiagonalQuestion
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_localization_of_nfQuasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.blackadarKirchbergQuasidiagonalQuestion_iff_stablyFinite_iff_mf_of_localization_of_nfQuasidiagonal
