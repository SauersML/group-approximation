import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Analysis.MatrixCoronaDedekindFinite
import GroupApproximation.Analysis.MFAlgebraMatrixAmplification
import GroupApproximation.Analysis.ShulmanFillNormingPrintedPairRefuted
import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequenceRankFour
import GroupApproximation.Manuscript.OneSidedMFRadical.CountableNonMF
import GroupApproximation.Meta.AxiomGuard

/-!
# MF and NF algebras, the MF problem, and MF groups (Related work)

`non_mf_groups_exist.tex`, section *Related work*.

**Lines 310--311** (census row `27d456b915c0`):

> Blackadar and Kirchberg introduced the notions of MF and NF algebras in a
> 1994 Oberwolfach abstract [BK94].

The notions are `GroupApproximation.IsMFAlgebra` (separable, with a faithful
possibly nonunital *-homomorphism into a norm matrix corona) and
`GroupApproximation.IsNFAlgebra` (separable, with finite-local completely
positive contractive approximations through matrix algebras that are
approximately multiplicative).  `manuscriptSentence_mfAndNFAlgebraNotions`
checks that the definitions behave as intended: NF algebras are separable,
nuclear and MF; `ℂ` and every matrix algebra `M_{m+1}(ℂ)` are MF; and MF
algebras are stably finite.

**Lines 319--321** (census row `ba77c51e9726`):

> The question without nuclearity, whether every stably finite
> C*-algebra is MF, is the MF problem, also posed by Blackadar and
> Kirchberg [GoldbringHart, §6].

`MFProblem` is the question (MF includes separability, so the question is
posed for separable algebras).  `manuscriptSentence_mfProblem` proves the
necessary direction (MF ⇒ stably finite, so the question is the converse),
the reduction recorded in the next printed sentence (a positive answer makes
every countable group MF, via the reduced group C*-algebra), and the negative
answer, reused from `thm:headline`
(`OneSidedMFRadical.manuscriptNotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour`).

**Lines 325--327** (census row `c8241b12c037`):

> Carrión, Dadarlat, and Eckhardt introduced MF groups [CDE], and whether
> every countable group is MF remained open [Korchagin, BDL].

The notion is `GroupApproximation.IsCDEOperatorMF` (the unitaries of a norm
matrix corona contain a copy of the group).  `EveryCountableGroupIsMF` is the
question; `manuscriptSentence_mfGroupQuestion` answers it negatively and
exhibits a countable non-MF group, reusing
`OneSidedMFRadical.manuscriptNotEveryCountableGroupIsMF` and
`OneSidedMFRadical.manuscriptCountableNonMFGroupExists`.  "Remained open" is
history and is not formalized.

No literature input and no `Statement` hypothesis is used.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedAttribution

open CStarExactness
open ReducedGroupCStarTrace

universe u

/-- **MF algebras are stably finite.**  An isometry in a matrix amplification
of an MF algebra is a unitary. -/
theorem isStablyFiniteCStarAlgebra_of_isMFAlgebra {A : Type u} [CStarAlgebra A]
    (hA : IsMFAlgebra A) : IsStablyFiniteCStarAlgebra A :=
  fun k _v hv =>
    MatrixCoronaFinite.cstarMatrix_mul_star_eq_one_of_hasMFEmbedding hA.2 (Fin (k + 1)) hv

/-- **tex 310--311: the notions of MF and NF algebras.**  NF algebras are
separable, nuclear and MF; `ℂ` and all matrix algebras over `ℂ` are MF; MF
algebras are stably finite. -/
theorem manuscriptSentence_mfAndNFAlgebraNotions :
    (∀ (A : Type) [CStarAlgebra A], IsNFAlgebra A →
        TopologicalSpace.SeparableSpace A ∧ IsNuclearCStarAlgebra A ∧ IsMFAlgebra A) ∧
      IsMFAlgebra ℂ ∧
      (∀ m : ℕ, IsMFAlgebra (CStarMatrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) ∧
      (∀ (A : Type) [CStarAlgebra A], IsMFAlgebra A → IsStablyFiniteCStarAlgebra A) :=
  ⟨fun _ _ hA => hA.separable_nuclear_and_mf,
    ShulmanFill.isMFAlgebra_complex,
    fun m => MFAlgebraMatrixAmplification.isMFAlgebra_cstarMatrix (m + 1)
      ShulmanFill.isMFAlgebra_complex,
    fun _ _ hA => isStablyFiniteCStarAlgebra_of_isMFAlgebra hA⟩

/-- **The MF problem** (tex 319--321): every separable stably finite
C*-algebra is MF. -/
def MFProblem : Prop :=
  ∀ (A : Type) [CStarAlgebra A],
    TopologicalSpace.SeparableSpace A → IsStablyFiniteCStarAlgebra A → IsMFAlgebra A

/-- **The MF group question** (tex 325--327): every countable group is MF. -/
def EveryCountableGroupIsMF : Prop :=
  ∀ (G : Type) [Group G] [Countable G], IsCDEOperatorMF G

/-- A positive answer to the MF problem would make every countable group MF,
because the reduced group C*-algebra is separable and stably finite. -/
theorem everyCountableGroupIsMF_of_mfProblem (h : MFProblem) :
    EveryCountableGroupIsMF :=
  fun G _ _ =>
    isCDEOperatorMF_of_hasMFEmbedding_reducedGroupCStar G
      (h (ReducedGroupCStar G) (reducedGroupCStar_separable_stablyFinite G).1
        (reducedGroupCStar_separable_stablyFinite G).2).2

/-- **tex 319--321: the MF problem.**  MF algebras are stably finite, so the
MF problem asks for the converse; a positive answer would make every countable
group MF; and the answer is negative. -/
theorem manuscriptSentence_mfProblem :
    (∀ (A : Type) [CStarAlgebra A], IsMFAlgebra A → IsStablyFiniteCStarAlgebra A) ∧
      (MFProblem → EveryCountableGroupIsMF) ∧
      ¬ MFProblem :=
  ⟨fun _ _ hA => isStablyFiniteCStarAlgebra_of_isMFAlgebra hA,
    everyCountableGroupIsMF_of_mfProblem,
    OneSidedMFRadical.manuscriptNotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour⟩

/-- **tex 325--327: MF groups and the question whether every countable group
is MF.**  The question has a negative answer: some countable group is not
MF. -/
theorem manuscriptSentence_mfGroupQuestion :
    ¬ EveryCountableGroupIsMF ∧
      ∃ (G : Type) (_ : Group G) (_ : Countable G), ¬ IsCDEOperatorMF G :=
  ⟨OneSidedMFRadical.manuscriptNotEveryCountableGroupIsMF,
    OneSidedMFRadical.manuscriptCountableNonMFGroupExists⟩

end RelatedAttribution
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedAttribution.isStablyFiniteCStarAlgebra_of_isMFAlgebra
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedAttribution.manuscriptSentence_mfAndNFAlgebraNotions
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedAttribution.everyCountableGroupIsMF_of_mfProblem
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedAttribution.manuscriptSentence_mfProblem
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedAttribution.manuscriptSentence_mfGroupQuestion
