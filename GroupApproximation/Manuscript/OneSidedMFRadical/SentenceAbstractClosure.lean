import GroupApproximation.Manuscript.OneSidedMFRadical.CountableNonMF
import GroupApproximation.Manuscript.OneSidedMFRadical.PrescribedQuotients

/-!
# Sentence closure for the abstract

Standalone wrappers for the mathematical sentences in census rows 1--10.
The draft notice and authorial framing are not propositions; every declaration
below is a projection of an unconditional manuscript endpoint.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint

local instance abstractCountable : Countable H := countable

/-- **Sentence 1.**  A countable group exists which is not MF in the printed
operator-norm sense. -/
theorem manuscriptSentence1_countableNonMF_exists :
    CountableNonMFGroupExists :=
  manuscriptCountableNonMFGroupExists

/-- **Sentence 2.**  Membership in the printed MF radical means being sent to
the identity by every homomorphism into every norm-matrix corona. -/
theorem manuscriptSentence2_MFRadical_membership
    {G : Type} [Group G] (x : G) :
    x ∈ manuscriptCoronaMFResidual G ↔ ManuscriptCoronaMFInvisible x :=
  mem_manuscriptCoronaMFResidual_iff

/-- **Sentence 3.**  The one-sided compression criterion puts every normal
property-`(T)` subgroup of the printed defect into the MF radical. -/
theorem manuscriptSentence3_oneSidedCompression_forces_radical
    (G : Type) [Group G] [Countable G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (K : Subgroup G) [K.Normal]
    (hK : HasKazhdanPropertyT.{0, 0} ↥K)
    (hKD : K ≤ printedDefect L) :
    K ≤ manuscriptCoronaMFResidual G :=
  (manuscriptOneSidedCompressionCriterion G L hL).1 K hK hKD

/-- **Sentence 4.**  When the printed defect normally fills the Kazhdan
ambient group, the MF radical is the whole group. -/
theorem manuscriptSentence4_normalGeneration_forces_fullRadical
    (G : Type) [Group G] [Countable G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (hG : HasKazhdanPropertyT.{0, 0} G)
    (hdefect : printedDefect L = ⊤) :
    manuscriptCoronaMFResidual G = ⊤ :=
  (manuscriptOneSidedCompressionCriterion G L hL).2.2 hG hdefect

/-- **Sentence 5.**  The exact elementary group over the binary Leavitt
algebra realizes the full-radical situation. -/
theorem manuscriptSentence5_binaryLeavitt_realization :
    BinaryLeavittFullRadical :=
  manuscriptBinaryLeavittFullRadical

/-- **Sentence 6.**  The resulting exact group is simple. -/
theorem manuscriptSentence6_resultingGroup_simple :
    IsSimpleGroup H :=
  manuscriptPropositionSimple

/-- **Sentence 7.**  The resulting exact group has property `(T)`. -/
theorem manuscriptSentence7_resultingGroup_propertyT :
    HasKazhdanPropertyT.{0, 0} H :=
  hasKazhdanPropertyT

/-- **Sentence 8.**  Every homomorphism from the resulting group to a
countable MF group is trivial. -/
theorem manuscriptSentence8_everyHomToMF_trivial
    (M : Type) [Group M] [Countable M] (hM : IsCDEOperatorMF M)
    (f : H →* M) (x : H) :
    f x = 1 :=
  (manuscriptBinaryLeavittFullRadical.2.2.2.2.2.1 M hM f x)

/-- **Sentence 9.**  It is false that every countable group is MF. -/
theorem manuscriptSentence9_notEveryCountableGroupIsMF :
    NotEveryCountableGroupIsMF :=
  manuscriptNotEveryCountableGroupIsMF

/-- **Sentence 10.**  The camouflage amalgam realizes every prescribed
countable visible quotient for all homomorphisms to MF targets. -/
theorem manuscriptSentence10_prescribedMFQuotients :
    PrescribedMFQuotients :=
  manuscriptPrescribedMFQuotients

end OneSidedMFRadical
end Manuscript
end GroupApproximation
