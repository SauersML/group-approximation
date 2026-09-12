import GroupApproximation.Computability.ArithmeticalHierarchy
import GroupApproximation.Computability.MFRecognitionImpossible
import GroupApproximation.Computability.MFRadicalGodel
import GroupApproximation.Computability.MicrostateNormalForm
import GroupApproximation.Computability.MicrostateNaturalize
import GroupApproximation.Sofic.MFCamouflageConsequences
import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Algebra.CountableInstances

/-!
# Finite-dimensional representations can be computationally blind

This is the paper-facing endpoint for the computability results surrounding
operator-norm matricial approximation.  It deliberately leads with the one
fixed MF-radical computer, then exposes the recognition barrier, the universal
MF-visible quotient, a structural camouflage theorem, and the theory-relative
incompleteness theorem.

All declarations in this file are theorem packages assembled from closed
results.  No non-MF group, Boone theorem, Adian--Rabin transformation,
recursion theorem, or soundness principle is accepted as an axiom.
-/

namespace GroupApproximation
namespace FiniteDimensionalApproximationIncomplete

open PresentationCodes

/- `Multiplicative ℤ` is countable.  Proved once as
`GroupApproximation.CountableInstances.multiplicativeIntCountable` and taken
here with the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.multiplicativeIntCountable

/-! ## The headline fixed-group theorem -/

/-- **Universal computation hidden from finite-dimensional approximation.**
There is one fixed finitely presented non-MF group, a computable family of
explicit controller words, and a corresponding family of group elements such
that every element lies in the derived layer of the MF residual, while its
identity truth value is the halting problem. -/
theorem fixed_MF_radical_computer :
    Group.IsFinitelyPresented MFRadicalComputer.Carrier ∧
      ¬ IsOperatorMF MFRadicalComputer.Carrier ∧
      Computable MFRadicalComputer.controlRawWord ∧
      (∀ p, NormMFInvisible (MFRadicalComputer.word p)) ∧
      (∀ p, MFRadicalComputer.word p ∈
        ⁅normMFResidual MFRadicalComputer.Carrier,
          (⊤ : Subgroup MFRadicalComputer.Carrier)⁆) ∧
      (∀ p, MFRadicalComputer.word p = 1 ↔
        MFRadicalComputer.controlMachine.Halts p) ∧
      ¬ ComputablePred fun p : ℕ × ℕ =>
        MFRadicalComputer.word p = 1 :=
  MFRadicalComputer.closed_package

/-- The code-indexed form has exact universal partial-recursive semantics and
is the interface consumed by the Gödel theorem. -/
theorem fixed_MF_radical_computer_on_program_codes :
    Group.IsFinitelyPresented MFRadicalComputer.Carrier ∧
      ¬ IsOperatorMF MFRadicalComputer.Carrier ∧
      Computable MFRadicalComputer.codeRawWord ∧
      (∀ c : Nat.Partrec.Code,
        NormMFInvisible (MFRadicalComputer.codeWord c)) ∧
      (∀ c : Nat.Partrec.Code, MFRadicalComputer.codeWord c ∈
        ⁅normMFResidual MFRadicalComputer.Carrier,
          (⊤ : Subgroup MFRadicalComputer.Carrier)⁆) ∧
      (∀ c : Nat.Partrec.Code, MFRadicalComputer.codeWord c = 1 ↔
        (Nat.Partrec.Code.eval c 0).Dom) :=
  MFRadicalComputer.code_closed_package

/-! ## Structural camouflage -/

/-- A fixed camouflage witness with a cyclic visible quotient. -/
noncomputable abbrev CamouflageCarrier : Type :=
  MFCamouflage.Hotel.Cyclic

/-- The single distinguished relation generating the invisible kernel of the
fixed camouflage witness. -/
noncomputable abbrev camouflageDefect : CamouflageCarrier :=
  MFCamouflage.defect MFCamouflage.Hotel.sourceDefect (Multiplicative ℤ)

/-- The split projection from the fixed camouflage witness to its cyclic
MF-visible quotient. -/
noncomputable abbrev camouflageProjection :
    CamouflageCarrier →* Multiplicative ℤ :=
  MFCamouflage.projection MFCamouflage.Hotel.sourceDefect (Multiplicative ℤ)

/-- **Finite-dimensional camouflage.**  The fixed source is finitely
presented and non-MF, its visible cyclic quotient is MF, and its exact MF
radical is the normal closure of one nontrivial word.  The projection is
split, hence in particular surjective.

The radical is stated using the same universal-ultraproduct definition as the
fixed radical computer; the proof transports the concrete genuine-corona
calculation through the countable-group comparison theorem. -/
theorem fixed_finite_dimensional_camouflage :
    Group.IsFinitelyPresented CamouflageCarrier ∧
      IsOperatorMF (Multiplicative ℤ) ∧
      ¬ IsOperatorMF CamouflageCarrier ∧
      camouflageDefect ≠ 1 ∧
      normMFResidual CamouflageCarrier =
        Subgroup.normalClosure ({camouflageDefect} : Set CamouflageCarrier) ∧
      Function.Surjective camouflageProjection := by
  have hVisible : IsOperatorMF (Multiplicative ℤ) :=
    LiteralLEFExtension.integerQuotient_isOperatorMF
  have hVisibleCDE : IsCDEOperatorMF (Multiplicative ℤ) :=
    (isCDEOperatorMF_iff_isOperatorMF _).mpr hVisible
  refine ⟨MFCamouflage.Hotel.isFinitelyPresented (Multiplicative ℤ),
    hVisible, MFCamouflage.Hotel.not_isOperatorMF _ hVisible,
    MFCamouflage.Hotel.camouflage_defect_ne_one _, ?_,
    MFCamouflage.projection_surjective _ _⟩
  rw [← coronaMFResidual_eq_normMFResidual,
    ← actualCoronaMFResidual_eq_coronaMFResidual]
  exact MFCamouflage.Hotel.actualCoronaMFResidual_eq_normalClosure
    (Multiplicative ℤ) hVisibleCDE

/-- **Every countable MF observer sees only the visible cyclic quotient.**
Precomposition with the fixed split projection is a bijection on homomorphism
sets into every countable operator-MF target.  Thus the non-MF source and its
MF quotient have exactly the same maps to every target in this class. -/
theorem fixed_camouflage_observers_blind
    {T : Type} [Group T] [Countable T] (hT : IsOperatorMF T) :
    Function.Bijective
      (fun f : Multiplicative ℤ →* T ↦ f.comp camouflageProjection) :=
  MFCamouflage.Hotel.operatorMF_precomp_bijective
    (Multiplicative ℤ) hT

/-- At the literal approximation level, every representation into every
genuine norm-matrix corona also factors uniquely through the visible cyclic
quotient.  This is the precise finite-dimensional observation theorem used by
the paper; it does not assert unformalized all-fields representation-scheme
comparisons. -/
theorem fixed_camouflage_corona_observers_blind
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    Function.Bijective
      (fun f : Multiplicative ℤ →*
          unitary (NormMatrixCStarCorona (fun n ↦ X n)) ↦
        f.comp camouflageProjection) := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  exact MFCamouflage.actualCorona_precomp_bijective
    MFCamouflage.Hotel.sourceDefect (Multiplicative ℤ)
    MFCamouflage.Hotel.source_actualCoronaMFResidual_eq_top X hX

/-- The closed camouflage package includes the structural witness and its
universal observation theorem in one proposition. -/
theorem closed_camouflage_package :
    (Group.IsFinitelyPresented CamouflageCarrier ∧
      IsOperatorMF (Multiplicative ℤ) ∧
      ¬ IsOperatorMF CamouflageCarrier ∧
      camouflageDefect ≠ 1 ∧
      normMFResidual CamouflageCarrier =
        Subgroup.normalClosure ({camouflageDefect} : Set CamouflageCarrier) ∧
      Function.Surjective camouflageProjection) ∧
      (∀ (T : Type) [Group T] [Countable T], IsOperatorMF T →
        Function.Bijective
          (fun f : Multiplicative ℤ →* T ↦
            f.comp camouflageProjection)) := by
  exact ⟨fixed_finite_dimensional_camouflage,
    fun _ _ _ hT ↦ fixed_camouflage_observers_blind hT⟩

/-! ## Recognition -/

/- The unconditional finite-presentation recognition barrier is re-exported
under its established name: MF is undecidable, NONMF is not recursively
enumerable, and consequently there is no sound and complete computably
checkable certificate system for NONMF. -/
export MFRecognitionImpossible
  (mf_recognition_not_computable no_mf_decider nonMF_presentations_not_re
    no_nonMF_enumerator no_total_nonMF_enumerator
    no_nonMF_certificate_system mf_recognition_impossible)

/-- The oracle-free analytic normal form behind the second-level
arithmetization: MF holds exactly when every finite raw-word challenge is
answered either by a word-problem certificate or by a finite-dimensional
microstate. -/
theorem finite_scale_normal_form (P : PresentationCode) :
    IsOperatorMF (Carrier P) ↔
      ∀ W k, MFMicrostate.Answers P W k :=
  MFMicrostate.isOperatorMF_iff_forall_answers P

/-! ## The universal visible quotient -/

/-- Radical membership is exactly equality in the universal MF-visible
quotient. -/
theorem mem_radical_iff_visible_quotient_eq_one
    {G : Type*} [Group G] (g : G) :
    g ∈ normMFResidual G ↔ normMFQuotientMk G g = 1 :=
  (QuotientGroup.eq_one_iff g).symm

/-- For countable groups the universal visible quotient is itself MF, and
every map to an MF group factors through it uniquely. -/
theorem universal_MF_visible_quotient
    {G : Type*} [Group G] [Countable G] :
    IsOperatorMF (normMFQuotient G) ∧
      ∀ {H : Type*} [Group H] (f : G →* H), IsOperatorMF H →
        ∃! fBar : normMFQuotient G →* H,
          fBar.comp (normMFQuotientMk G) = f := by
  exact ⟨normMFQuotient_isOperatorMF,
    fun f hH ↦ existsUnique_normMFQuotient_factorization_to_isOperatorMF f hH⟩

/-! ## Incompleteness -/

/-- Every computably enumerable proof system sound for the concrete
nontriviality statements about the fixed radical computer misses a true word
in the derived layer of that same MF residual. -/
theorem incompleteness_in_the_fixed_MF_radical
    (T : MFRadicalGodel.ProofSystem) (hsound : T.Sound) :
    ∃ c : Nat.Partrec.Code,
      MFRadicalComputer.codeWord c ≠ 1 ∧
        NormMFInvisible (MFRadicalComputer.codeWord c) ∧
        MFRadicalComputer.codeWord c ∈
          ⁅normMFResidual MFRadicalComputer.Carrier,
            (⊤ : Subgroup MFRadicalComputer.Carrier)⁆ ∧
        ¬ T.Proves c :=
  MFRadicalGodel.exists_true_unprovable_radical_word T hsound

/-- Closed paper core: the fixed radical computer and the assertion that every
sound computably enumerable proof system misses a true nontriviality statement
inside it. -/
theorem closed_core :
    (Group.IsFinitelyPresented MFRadicalComputer.Carrier ∧
      ¬ IsOperatorMF MFRadicalComputer.Carrier ∧
      Computable MFRadicalComputer.codeRawWord ∧
      (∀ c : Nat.Partrec.Code,
        NormMFInvisible (MFRadicalComputer.codeWord c)) ∧
      (∀ c : Nat.Partrec.Code, MFRadicalComputer.codeWord c ∈
        ⁅normMFResidual MFRadicalComputer.Carrier,
          (⊤ : Subgroup MFRadicalComputer.Carrier)⁆) ∧
      (∀ c : Nat.Partrec.Code, MFRadicalComputer.codeWord c = 1 ↔
        (Nat.Partrec.Code.eval c 0).Dom)) ∧
      (∀ T : MFRadicalGodel.ProofSystem, T.Sound →
        ∃ c : Nat.Partrec.Code,
          MFRadicalComputer.codeWord c ≠ 1 ∧
            NormMFInvisible (MFRadicalComputer.codeWord c) ∧
            ¬ T.Proves c) := by
  exact ⟨fixed_MF_radical_computer_on_program_codes,
    fun T hsound ↦ MFRadicalGodel.closed_package.2 T hsound⟩

end FiniteDimensionalApproximationIncomplete
end GroupApproximation
