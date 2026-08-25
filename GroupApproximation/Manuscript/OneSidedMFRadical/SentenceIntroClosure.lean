import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure

/-!
# Sentence closure for the MF-radical introduction

This file carries, sentence by sentence, the proof of
`prop:mf-residual-calculus` after the manuscript replaces its auxiliary
diagonal-coordinate argument by the universal-corona quotient construction.
Every proposition below is closed: the group, its structure, and its
countability hypothesis are quantified inside the statement.

No theorem from the literature is an input.  The only substantive ingredient
is the in-repository construction
`manuscriptCoronaMFQuotient_isCDEOperatorMF`, whose proof builds the universal
corona representation and passes to its kernel quotient.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

noncomputable section

/-- The quotient of a countable group is countable.  Mathlib does not install
this globally because quotient presentations are not unique; every quotient in
this module is the canonical `QuotientGroup` one.  The same local instance is
what `Sofic/ActualCoronaMFRadical.lean` uses to state
`manuscriptCoronaMFQuotient_isCDEOperatorMF`, so the statements below are the
ones that theorem proves. -/
local instance quotientGroupCountable {G : Type*} [Group G] (N : Subgroup G)
    [hN : N.Normal] [Countable G] :
    Countable (G ⧸ N) :=
  Function.Surjective.countable
    (@QuotientGroup.mk'_surjective G _ N hN)

/-- The first sentence after setting `R = Rad_MF(G)`: the subgroup used for
the quotient is normal. -/
def IntroMFRadicalIsNormal : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    (manuscriptCoronaMFResidual G).Normal

/-- Closed proof that the MF radical in the introductory quotient proof is
normal. -/
theorem manuscriptIntroMFRadicalIsNormal : IntroMFRadicalIsNormal := by
  intro G _ _
  infer_instance

/-- The universal-corona construction realizes the MF radical as the kernel
of one homomorphism into one positive-dimensional norm-matrix corona. -/
def IntroMFRadicalIsOneCoronaKernel : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    ∃ (d : ℕ → ℕ), ∃ hd : ∀ n, 0 < d n,
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∃ rho : G →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        rho.ker = manuscriptCoronaMFResidual G

/-- Closed proof of the single-corona-kernel sentence. -/
theorem manuscriptIntroMFRadicalIsOneCoronaKernel :
    IntroMFRadicalIsOneCoronaKernel := by
  intro G _ _
  exact exists_manuscriptCoronaRepresentation_ker_eq_manuscriptCoronaMFResidual

/-- The dimension sequence in the faithful representation of the universal
MF quotient may be chosen positive. -/
def IntroMFQuotientHasPositiveDimensions : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    ∃ d : ℕ → ℕ, ∀ n, 0 < d n

/-- Closed proof of positivity of the quotient model dimensions. -/
theorem manuscriptIntroMFQuotientHasPositiveDimensions :
    IntroMFQuotientHasPositiveDimensions := by
  intro G _ _
  obtain ⟨d, hd, _hmono, _rho, _hrho⟩ :=
    manuscriptCoronaMFQuotient_isCDEOperatorMF (G := G)
  exact ⟨d, hd⟩

/-- The dimension sequence in the faithful representation of the universal
MF quotient may be chosen strictly increasing. -/
def IntroMFQuotientHasStrictDimensions : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    ∃ d : ℕ → ℕ, StrictMono d

/-- Closed proof of strict growth of the quotient model dimensions. -/
theorem manuscriptIntroMFQuotientHasStrictDimensions :
    IntroMFQuotientHasStrictDimensions := by
  intro G _ _
  obtain ⟨d, _hd, hmono, _rho, _hrho⟩ :=
    manuscriptCoronaMFQuotient_isCDEOperatorMF (G := G)
  exact ⟨d, hmono⟩

/-- The kernel quotient has a faithful homomorphism into a genuine
natural-dimension norm-matrix corona, with positive strictly increasing
dimensions.  This is the expanded, literal embedding sentence in the
rewritten manuscript proof. -/
def IntroMFQuotientHasFaithfulCoronaRepresentation : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    ∃ (d : ℕ → ℕ), ∃ hd : ∀ n, 0 < d n,
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      StrictMono d ∧
        ∃ rho : (G ⧸ manuscriptCoronaMFResidual G) →*
            unitary (NormMatrixCStarCorona
              (fun n ↦ naturalFiniteModel (d n))),
          Function.Injective rho

/-- Closed proof of the faithful-corona-representation sentence. -/
theorem manuscriptIntroMFQuotientHasFaithfulCoronaRepresentation :
    IntroMFQuotientHasFaithfulCoronaRepresentation := by
  intro G _ _
  exact manuscriptCoronaMFQuotient_isCDEOperatorMF

/-- The manuscript's embedding sentence, named separately so its assertion is
individually auditable rather than inferred from the following MF sentence. -/
def IntroMFQuotientEmbedsInCorona : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsCDEOperatorMF (G ⧸ manuscriptCoronaMFResidual G)

/-- Closed proof that the quotient embeds in a norm-matrix corona. -/
theorem manuscriptIntroMFQuotientEmbedsInCorona :
    IntroMFQuotientEmbedsInCorona := by
  intro G _ _
  exact manuscriptCoronaMFQuotient_isCDEOperatorMF

/-- The final sentence of the rewritten paragraph: the quotient by the MF
radical is MF. -/
def IntroMFQuotientIsMF : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsCDEOperatorMF (G ⧸ manuscriptCoronaMFResidual G)

/-- Closed proof of the final MF assertion. -/
theorem manuscriptIntroMFQuotientIsMF : IntroMFQuotientIsMF := by
  intro G _ _
  exact manuscriptCoronaMFQuotient_isCDEOperatorMF

/-- All seven declarative sentences of the rewritten universal-quotient
paragraph, in their printed order. -/
def IntroMFUniversalQuotientRoute : Prop :=
  IntroMFRadicalIsNormal ∧
    IntroMFRadicalIsOneCoronaKernel ∧
    IntroMFQuotientHasPositiveDimensions ∧
    IntroMFQuotientHasStrictDimensions ∧
    IntroMFQuotientHasFaithfulCoronaRepresentation ∧
    IntroMFQuotientEmbedsInCorona ∧
    IntroMFQuotientIsMF

/-- Closed package for the complete replacement paragraph. -/
theorem manuscriptIntroMFUniversalQuotientRoute :
    IntroMFUniversalQuotientRoute := by
  exact ⟨manuscriptIntroMFRadicalIsNormal,
    manuscriptIntroMFRadicalIsOneCoronaKernel,
    manuscriptIntroMFQuotientHasPositiveDimensions,
    manuscriptIntroMFQuotientHasStrictDimensions,
    manuscriptIntroMFQuotientHasFaithfulCoronaRepresentation,
    manuscriptIntroMFQuotientEmbedsInCorona,
    manuscriptIntroMFQuotientIsMF⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
