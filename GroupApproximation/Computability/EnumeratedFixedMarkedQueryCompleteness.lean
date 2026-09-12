import GroupApproximation.Computability.EnumeratedFixedMarkedQuery
import GroupApproximation.Computability.ExactSwitchQueryCompleteness
import GroupApproximation.Computability.RecursiveSwitchPresentation
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Second-level completeness on standard enumerated presentations

The exact event switch is compiled by s-m-n into the standard
`Nat.Partrec.Code` presentation syntax.  The end-to-end presented-group
equivalence transports arbitrary marked homomorphisms, so this file proves
the exact `INF`/`FIN` truth table for the executable query itself.  No finite
Higman embedding, Chiodo theorem, or external index-set theorem is used.
-/

namespace GroupApproximation
namespace EnumeratedFixedMarkedQueryCompleteness

open Nat.Partrec
open ArithmeticalHierarchy
open SecondLevelIndexSets

noncomputable section

/-- The universal fixed marked query on standard presentation codes. -/
def StandardKills (c : Code) : Prop :=
  FixedMarkedQueryHierarchy.Kills EnumeratedFixedMarkedQuery.literalQuery c

/-- The existential fixed marked query on standard presentation codes. -/
def StandardSurvives (c : Code) : Prop :=
  FixedMarkedQueryHierarchy.Survives EnumeratedFixedMarkedQuery.literalQuery c

/-- Marked survival is invariant under a group equivalence of targets. -/
theorem homSurvives_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) :
    (∃ φ : LiteralNonMFPresentation.MarkedGroup →* G,
        φ LiteralNonMFPresentation.mark ≠ 1) ↔
      ∃ ψ : LiteralNonMFPresentation.MarkedGroup →* H,
        ψ LiteralNonMFPresentation.mark ≠ 1 := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨e.toMonoidHom.comp φ, ?_⟩
    intro h
    apply hφ
    apply e.injective
    simpa using h
  · rintro ⟨ψ, hψ⟩
    refine ⟨e.symm.toMonoidHom.comp ψ, ?_⟩
    intro h
    apply hψ
    apply e.symm.injective
    simpa using h

/-- The executable standard-code query transports exactly to the semantic
event switch, with no restriction on the target homomorphism. -/
theorem compiled_survives_iff_switchSurvives (c : Code) :
    StandardSurvives (RecursiveSwitchPresentation.switchEnumeratorCode c) ↔
      ExactSwitchQueryCompleteness.SwitchSurvives c := by
  rw [StandardSurvives,
    EnumeratedFixedMarkedQuery.survives_iff_homSurvives]
  exact homSurvives_congr
    (RecursiveSwitchPresentation.standardCarrierEquivSwitch c)

/-- The complementary universal query also transports exactly. -/
theorem compiled_kills_iff_switchKills (c : Code) :
    StandardKills (RecursiveSwitchPresentation.switchEnumeratorCode c) ↔
      ExactSwitchQueryCompleteness.SwitchKills c := by
  rw [StandardKills, FixedMarkedQueryHierarchy.kills_iff_not_survives,
    show FixedMarkedQueryHierarchy.Survives
      EnumeratedFixedMarkedQuery.literalQuery
        (RecursiveSwitchPresentation.switchEnumeratorCode c) =
      StandardSurvives (RecursiveSwitchPresentation.switchEnumeratorCode c)
      from rfl,
    compiled_survives_iff_switchSurvives]
  change (¬ ExactLiteralSwitchQuery.Survives
      (ExactSwitchQueryCompleteness.SwitchTarget c)) ↔
    ExactLiteralSwitchQuery.Kills
      (ExactSwitchQueryCompleteness.SwitchTarget c)
  have h := not_congr
    (ExactLiteralSwitchQuery.survives_iff_not_kills
      (ExactSwitchQueryCompleteness.SwitchTarget c))
  classical
  simpa only [not_not] using h

/-- Exact `INF` behavior of the compiled standard presentation. -/
theorem compiled_kills_iff_infiniteDomain (c : Code) :
    StandardKills (RecursiveSwitchPresentation.switchEnumeratorCode c) ↔
      InfiniteDomain c :=
  (compiled_kills_iff_switchKills c).trans
    (ExactSwitchQueryCompleteness.switchKills_iff_infiniteDomain c)

/-- Exact `FIN` behavior of the compiled standard presentation. -/
theorem compiled_survives_iff_finiteDomain (c : Code) :
    StandardSurvives (RecursiveSwitchPresentation.switchEnumeratorCode c) ↔
      FiniteDomain c :=
  (compiled_survives_iff_switchSurvives c).trans
    (ExactSwitchQueryCompleteness.switchSurvives_iff_finiteDomain c)

/-- KILL is `Π⁰₂`-hard on the standard recursive-presentation syntax. -/
theorem standardKills_pi02Hard : Pi02Hard StandardKills := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ := infiniteDomain_pi02Hard p hp
  refine ⟨fun n => RecursiveSwitchPresentation.switchEnumeratorCode (f n),
    RecursiveSwitchPresentation.computable_switchEnumeratorCode.comp hf,
    fun n => ?_⟩
  exact (hcorrect n).trans
    (compiled_kills_iff_infiniteDomain (f n)).symm

/-- KILL is `Π⁰₂`-complete on standard enumerated presentations. -/
theorem standardKills_pi02Complete : Pi02Complete StandardKills :=
  ⟨EnumeratedFixedMarkedQuery.kills_pi02, standardKills_pi02Hard⟩

/-- SURV is `Σ⁰₂`-hard on the standard recursive-presentation syntax. -/
theorem standardSurvives_sigma02Hard : Sigma02Hard StandardSurvives := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ := finiteDomain_sigma02Hard p hp
  refine ⟨fun n => RecursiveSwitchPresentation.switchEnumeratorCode (f n),
    RecursiveSwitchPresentation.computable_switchEnumeratorCode.comp hf,
    fun n => ?_⟩
  exact (hcorrect n).trans
    (compiled_survives_iff_finiteDomain (f n)).symm

/-- SURV is `Σ⁰₂`-complete on standard enumerated presentations. -/
theorem standardSurvives_sigma02Complete : Sigma02Complete StandardSurvives :=
  ⟨EnumeratedFixedMarkedQuery.survives_sigma02,
    standardSurvives_sigma02Hard⟩

/-- Every positive SURV instance is an actual non-MF group; completeness is
therefore not merely syntactic. -/
theorem not_isOperatorMF_of_standardSurvives (c : Code)
    (h : StandardSurvives c) :
    ¬ IsOperatorMF (EnumeratedPresentationCodes.Carrier c) :=
  EnumeratedFixedMarkedQuery.not_isOperatorMF_of_survives c h

/-- Operator-MF, viewed as a predicate of standard presentation codes. -/
def OperatorMFCode (c : Code) : Prop :=
  IsOperatorMF (EnumeratedPresentationCodes.Carrier c)

/-- Failure of Operator-MF on standard presentation codes. -/
def NonOperatorMFCode (c : Code) : Prop := ¬ OperatorMFCode c

/-- On the compiled range, Operator-MF holds exactly in the infinite-domain
branch: that target is literally subsingleton. -/
theorem compiled_operatorMF_iff_infiniteDomain (c : Code) :
    OperatorMFCode (RecursiveSwitchPresentation.switchEnumeratorCode c) ↔
      InfiniteDomain c := by
  constructor
  · intro hMF
    by_contra hinfinite
    have hfinite : FiniteDomain c := by
      simpa only [InfiniteDomain, FiniteDomain, Set.not_infinite] using hinfinite
    have hsurvives : StandardSurvives
        (RecursiveSwitchPresentation.switchEnumeratorCode c) :=
      (compiled_survives_iff_finiteDomain c).2 hfinite
    exact (not_isOperatorMF_of_standardSurvives _ hsurvives) hMF
  · intro hinfinite
    let e := RecursiveSwitchPresentation.standardCarrierEquivSwitch c
    letI : Subsingleton (ExactSwitchQueryCompleteness.SwitchTarget c) :=
      ExactLiteralEFinInfSwitch.subsingleton_of_infiniteEvents _
        (CodeDovetailStageEvents.infiniteDomain_infiniteEvents c hinfinite)
    letI : Subsingleton
        (EnumeratedPresentationCodes.Carrier
          (RecursiveSwitchPresentation.switchEnumeratorCode c)) :=
      ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
    letI : Finite
        (EnumeratedPresentationCodes.Carrier
          (RecursiveSwitchPresentation.switchEnumeratorCode c)) :=
      Finite.of_injective
        (fun _ : EnumeratedPresentationCodes.Carrier
          (RecursiveSwitchPresentation.switchEnumeratorCode c) => PUnit.unit)
        (fun _ _ _ => Subsingleton.elim _ _)
    exact isOperatorMF_of_finite_standard _

/-- Equivalently, non-Operator-MF is exact on the finite-domain branch. -/
theorem compiled_nonOperatorMF_iff_finiteDomain (c : Code) :
    NonOperatorMFCode (RecursiveSwitchPresentation.switchEnumeratorCode c) ↔
      FiniteDomain c := by
  have h := not_congr (compiled_operatorMF_iff_infiniteDomain c)
  simpa only [NonOperatorMFCode, FiniteDomain, InfiniteDomain,
    Set.not_infinite] using h

/-- Operator-MF recognition on arbitrary standard codes is `Π⁰₂`-hard.
No global upper-bound claim is made. -/
theorem operatorMFCode_pi02Hard : Pi02Hard OperatorMFCode := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ := infiniteDomain_pi02Hard p hp
  refine ⟨fun n => RecursiveSwitchPresentation.switchEnumeratorCode (f n),
    RecursiveSwitchPresentation.computable_switchEnumeratorCode.comp hf,
    fun n => ?_⟩
  exact (hcorrect n).trans
    (compiled_operatorMF_iff_infiniteDomain (f n)).symm

/-- Non-Operator-MF recognition on arbitrary standard codes is
`Σ⁰₂`-hard.  Again, this asserts no global upper bound. -/
theorem nonOperatorMFCode_sigma02Hard : Sigma02Hard NonOperatorMFCode := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ := finiteDomain_sigma02Hard p hp
  refine ⟨fun n => RecursiveSwitchPresentation.switchEnumeratorCode (f n),
    RecursiveSwitchPresentation.computable_switchEnumeratorCode.comp hf,
    fun n => ?_⟩
  exact (hcorrect n).trans
    (compiled_nonOperatorMF_iff_finiteDomain (f n)).symm

/-- The complete compiled truth table on the standard syntax. -/
theorem exact_standard_second_level_switch (c : Code) :
    (StandardKills (RecursiveSwitchPresentation.switchEnumeratorCode c) ↔
        InfiniteDomain c) ∧
      (StandardSurvives (RecursiveSwitchPresentation.switchEnumeratorCode c) ↔
        FiniteDomain c) ∧
      (StandardSurvives (RecursiveSwitchPresentation.switchEnumeratorCode c) →
        ¬ IsOperatorMF
          (EnumeratedPresentationCodes.Carrier
            (RecursiveSwitchPresentation.switchEnumeratorCode c))) :=
  ⟨compiled_kills_iff_infiniteDomain c,
    compiled_survives_iff_finiteDomain c,
    not_isOperatorMF_of_standardSurvives _⟩

end

end EnumeratedFixedMarkedQueryCompleteness
end GroupApproximation
