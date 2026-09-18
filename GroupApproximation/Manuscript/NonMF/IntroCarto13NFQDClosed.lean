import GroupApproximation.Manuscript.NonMF.IntroCarto13NFQD
import GroupApproximation.Manuscript.NonMF.IntroCarto10BKQDClosed
import GroupApproximation.Manuscript.NonMF.IntroCarto11BKQuestionClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# NF ⇒ quasidiagonal: the downstream intro endpoints, closed

Lane `nm-intro-13`. The `_of_nfQuasidiagonal` and `_of_nfImpliesQuasidiagonal`
endpoints of lanes 10, 11 and 12 take the NF ⇒ QD interface as a hypothesis.
`IntroCarto13.nfqdQuasidiagonalStatement` and
`IntroCarto13.nfqdImpliesQuasidiagonalStatement` discharge it, so each endpoint
below is unconditional.

* `nfqd_isQuasidiagonalCStarAlgebra_of_nuclear_of_mf`: nuclear and MF give QD.
* `nfqd_isNFAlgebra_iff_nuclear_and_quasidiagonal`: NF ⇔ nuclear ∧ QD.
* `nfqd_nuclear_and_mf_iff_nuclear_and_quasidiagonal`.
* `nfqd_bkQuestion_iff_nuclearMF` and `nfqd_bkQuestion_iff_stablyFinite_iff_mf`:
  the Blackadar--Kirchberg question restated.
* `nfqd_nfSubsetNuclearStablyFiniteQD`: NF algebras are separable, nuclear,
  stably finite and quasidiagonal.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto13

open GroupApproximation.CStarExactness

universe u

/-- **Nuclear and MF implies quasidiagonal** (unconditional). -/
theorem nfqd_isQuasidiagonalCStarAlgebra_of_nuclear_of_mf
    {A : Type u} [CStarAlgebra A]
    (hnuc : IsNuclearCStarAlgebra A) (hMF : IsMFAlgebra A) :
    RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  IntroCarto10.isQuasidiagonalCStarAlgebra_of_nuclear_of_mf_of_nfQuasidiagonal
    nfqdQuasidiagonalStatement hnuc hMF

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto13.nfqd_isQuasidiagonalCStarAlgebra_of_nuclear_of_mf

/-- **NF means nuclear and quasidiagonal** (unconditional). -/
theorem nfqd_isNFAlgebra_iff_nuclear_and_quasidiagonal
    {A : Type u} [CStarAlgebra A] :
    IsNFAlgebra A ↔
      IsNuclearCStarAlgebra A ∧ RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  IntroCarto10.isNFAlgebra_iff_nuclear_and_quasidiagonal_of_nfQuasidiagonal
    nfqdQuasidiagonalStatement

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto13.nfqd_isNFAlgebra_iff_nuclear_and_quasidiagonal

/-- **For nuclear algebras, MF and quasidiagonal coincide** (unconditional). -/
theorem nfqd_nuclear_and_mf_iff_nuclear_and_quasidiagonal
    {A : Type u} [CStarAlgebra A] :
    IsNuclearCStarAlgebra A ∧ IsMFAlgebra A ↔
      IsNuclearCStarAlgebra A ∧ RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  IntroCarto10.nuclear_and_mf_iff_nuclear_and_quasidiagonal_of_nfQuasidiagonal
    nfqdQuasidiagonalStatement

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto13.nfqd_nuclear_and_mf_iff_nuclear_and_quasidiagonal

/-- **The BK QD question, restated for nuclear algebras** (unconditional). -/
theorem nfqd_bkQuestion_iff_nuclearMF :
    RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        IsNuclearCStarAlgebra A → IsStablyFiniteCStarAlgebra A → IsMFAlgebra A :=
  IntroCarto11.blackadarKirchbergQuasidiagonalQuestion_iff_nuclearMF_of_nfQuasidiagonal
    nfqdQuasidiagonalStatement

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto13.nfqd_bkQuestion_iff_nuclearMF

/-- **The BK QD question as a coincidence of classes** (unconditional). -/
theorem nfqd_bkQuestion_iff_stablyFinite_iff_mf :
    RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion.{u} ↔
      ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
        IsNuclearCStarAlgebra A →
          (IsStablyFiniteCStarAlgebra A ↔ IsMFAlgebra A) :=
  IntroCarto11.blackadarKirchbergQuasidiagonalQuestion_iff_stablyFinite_iff_mf_of_nfQuasidiagonal
    nfqdQuasidiagonalStatement

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto13.nfqd_bkQuestion_iff_stablyFinite_iff_mf

/-- **tex 310--312, the NF inclusions with quasidiagonality** (unconditional).
Every NF C⋆-algebra is separable, nuclear, stably finite and quasidiagonal. -/
theorem nfqd_nfSubsetNuclearStablyFiniteQD
    {A : Type u} [CStarAlgebra A] (hA : IsNFAlgebra A) :
    TopologicalSpace.SeparableSpace A ∧ IsNuclearCStarAlgebra A ∧
      IsStablyFiniteCStarAlgebra A ∧ RelatedTWW.IsQuasidiagonalCStarAlgebra A :=
  IntroCarto12.manuscriptSentence_nfSubsetNuclearStablyFiniteQD_of_nfImpliesQuasidiagonal
    nfqdImpliesQuasidiagonalStatement hA

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto13.nfqd_nfSubsetNuclearStablyFiniteQD

end IntroCarto13
end NonMF
end Manuscript
end GroupApproximation
