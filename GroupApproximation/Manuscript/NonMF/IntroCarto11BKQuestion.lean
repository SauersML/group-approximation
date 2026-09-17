import GroupApproximation.Manuscript.NonMF.RelatedTWW.Elementary
import GroupApproximation.Manuscript.NonMF.RelatedBK.ConverseReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Intro cartography, lane 11: the Blackadar--Kirchberg QD question for nuclear algebras

`non_mf_groups_exist.tex` L315--316 (Related work, paragraph starting at L310):

> It also asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal;

The question is `RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion`. This module
restates it downstream of the Blackadar--Kirchberg theorem "nuclear and MF implies
quasidiagonal". The restated form reads: every separable nuclear stably finite
C⋆-algebra is MF. The census row is `attribution`, so this module strengthens the
corpus and changes no census status.

## Proof route

* `→` is unconditional: quasidiagonal implies MF
  (`RelatedTWW.isMFAlgebra_of_isQuasidiagonalCStarAlgebra`).
* `←` needs "separable nuclear MF implies quasidiagonal". That is lane nm-intro-10,
  which is not on disk yet, so it is stated here as `NuclearMFQuasidiagonalStatement`.
  Lane 10 composes the corpus converse
  `RelatedBK.isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra_of_coronaUCPFiniteCoordinateLocalization`
  with lane nm-intro-09, "NF implies quasidiagonal". Lane 09 is also not on disk and
  is stated here as `NFQuasidiagonalStatement`. The composition is proved below as
  `nuclearMFQuasidiagonalStatement_of_localization_of_nfQuasidiagonal`.

## The isolated gap, and why it is true and strictly smaller

`NFQuasidiagonalStatement` says that every separable NF algebra, in the corpus
finite-local CPC sense, is quasidiagonal in the `RelatedTWW` model sense. It is TRUE,
because the proof goes through. Take a dense sequence and let `F_n` be its first `n`
terms, with tolerance `1/(n+1)`. The downward maps are CPC, hence star-preserving. They
are approximately multiplicative on `F_n`, and density gives multiplicativity on all
of `A`. Their norms recover `‖a‖` because `‖a‖ ≤ ‖up (down a)‖ + ε ≤ ‖down a‖ + ε`,
and `up` is contractive. The same `down` maps with `ε = 1` also give a zero-algebra
model. It is strictly smaller in proof content than the lane target: the target
equivalence also contains the whole Blackadar--Kirchberg converse (the corona
localization plus `ConverseReduction`), and the corpus proves that converse here.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto11

open GroupApproximation.CStarExactness

universe u

/-! ## Upstream interfaces (lanes nm-intro-09 and nm-intro-10) -/

/-- **NF implies quasidiagonal** (Blackadar--Kirchberg, lane nm-intro-09): every
C⋆-algebra that is NF in the finite-local CPC sense is quasidiagonal. -/
def NFQuasidiagonalStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A], IsNFAlgebra A →
    RelatedTWW.IsQuasidiagonalCStarAlgebra A

/-- **Nuclear and MF implies quasidiagonal** (Blackadar--Kirchberg 1997, lane
nm-intro-10). Separability is part of `IsMFAlgebra`. -/
def NuclearMFQuasidiagonalStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A], IsNuclearCStarAlgebra A → IsMFAlgebra A →
    RelatedTWW.IsQuasidiagonalCStarAlgebra A

/-- **Lane 10 from lane 09 and the localization principle.** Nuclear and MF gives NF
by the corpus converse, and NF gives quasidiagonal. -/
theorem nuclearMFQuasidiagonalStatement_of_localization_of_nfQuasidiagonal
    (hloc : RelatedBK.CoronaUCPFiniteCoordinateLocalizationStatement)
    (hnf : NFQuasidiagonalStatement.{u}) :
    NuclearMFQuasidiagonalStatement.{u} := by
  intro A _ hnuc hMF
  exact hnf A
    (RelatedBK.isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra_of_coronaUCPFiniteCoordinateLocalization
      hloc hnuc hMF)

/-! ## The restated question -/

/-- **The unconditional half.** If the Blackadar--Kirchberg question has a positive
answer, then every separable nuclear stably finite C⋆-algebra is MF. -/
theorem nuclearStablyFiniteMF_of_blackadarKirchbergQuasidiagonalQuestion
    (hq : RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u}) :
    ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
      IsNuclearCStarAlgebra A → IsStablyFiniteCStarAlgebra A → IsMFAlgebra A := by
  intro A _ hsep hnuc hsf
  exact RelatedTWW.isMFAlgebra_of_isQuasidiagonalCStarAlgebra (hq A hsep hnuc hsf)

/-- **The BK QD question, restated for nuclear algebras**, given lane 10. The
question holds exactly when every separable nuclear stably finite C⋆-algebra is MF. -/
theorem blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_nuclearMFQuasidiagonal
    (hQD : NuclearMFQuasidiagonalStatement.{u}) :
    RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        IsNuclearCStarAlgebra A → IsStablyFiniteCStarAlgebra A → IsMFAlgebra A := by
  refine ⟨nuclearStablyFiniteMF_of_blackadarKirchbergQuasidiagonalQuestion, ?_⟩
  intro h A _ hsep hnuc hsf
  exact hQD A hnuc (h A hsep hnuc hsf)

/-- **The BK QD question, restated for nuclear algebras**, given the localization
principle and lane 09. -/
theorem blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_localization_of_nfQuasidiagonal
    (hloc : RelatedBK.CoronaUCPFiniteCoordinateLocalizationStatement)
    (hnf : NFQuasidiagonalStatement.{u}) :
    RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        IsNuclearCStarAlgebra A → IsStablyFiniteCStarAlgebra A → IsMFAlgebra A :=
  blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_nuclearMFQuasidiagonal
    (nuclearMFQuasidiagonalStatement_of_localization_of_nfQuasidiagonal hloc hnf)

/-- **The question as a coincidence of classes**, given lane 10. For separable nuclear
C⋆-algebras the question holds exactly when stable finiteness and MF coincide. The
implication "MF implies stably finite" is unconditional. -/
theorem blackadarKirchbergQuasidiagonalQuestion_iff_stablyFinite_iff_mf_of_nuclearMFQuasidiagonal
    (hQD : NuclearMFQuasidiagonalStatement.{u}) :
    RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        IsNuclearCStarAlgebra A →
          (IsStablyFiniteCStarAlgebra A ↔ IsMFAlgebra A) := by
  rw [blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_nuclearMFQuasidiagonal hQD]
  constructor
  · intro h A _ hsep hnuc
    exact ⟨h A hsep hnuc,
      fun hMF ↦ RelatedTWW.isStablyFiniteCStarAlgebra_of_hasMFEmbedding hMF.2⟩
  · intro h A _ hsep hnuc hsf
    exact (h A hsep hnuc).mp hsf

end IntroCarto11
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.NFQuasidiagonalStatement
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.NuclearMFQuasidiagonalStatement
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.nuclearMFQuasidiagonalStatement_of_localization_of_nfQuasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.nuclearStablyFiniteMF_of_blackadarKirchbergQuasidiagonalQuestion
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_nuclearMFQuasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_localization_of_nfQuasidiagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto11.blackadarKirchbergQuasidiagonalQuestion_iff_stablyFinite_iff_mf_of_nuclearMFQuasidiagonal
