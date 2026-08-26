import GroupApproximation.Computability.EnumeratedFixedMarkedQueryCompleteness
import GroupApproximation.Computability.ExactSwitchAlgorithmicConsequences

/-!
# Strict algorithmic consequences on standard enumerated presentations

The standard-input completeness theorem supplies a computable compiler from
the exact switch family to ordinary `Nat.Partrec.Code` presentation codes.
This file pulls hypothetical semidecision procedures, deciders, and finite
certificate systems back along that compiler.  The contradictions are the
internal nonhalting separations already proved for the exact switch; no
external arithmetical-hierarchy separation is used.
-/

namespace GroupApproximation
namespace EnumeratedFixedMarkedQueryConsequences

open Nat.Partrec
open ArithmeticalHierarchy
open EnumeratedFixedMarkedQueryCompleteness
open ExactSwitchAlgorithmicConsequences

noncomputable section

/-! ## Generic computable-pullback principles -/

theorem not_re_of_computable_pullback
    {A B : Type*} [Primcodable A] [Primcodable B]
    {p : B → Prop} {q : A → Prop} (f : A → B)
    (hf : Computable f) (hcorrect : ∀ a, p (f a) ↔ q a)
    (hq : ¬ REPred q) : ¬ REPred p := by
  intro hp
  have hpullback : REPred fun a => p (f a) :=
    MarkovMFConsequences.rePred_comp hp hf
  exact hq (hpullback.of_eq hcorrect)

theorem not_core_of_computable_pullback
    {A B : Type*} [Primcodable A] [Primcodable B]
    {p : B → Prop} {q : A → Prop} (f : A → B)
    (hf : Computable f) (hcorrect : ∀ a, p (f a) ↔ q a)
    (hq : ¬ Pi01 q) : ¬ Pi01 p := by
  intro hp
  have hpullback : REPred fun a => ¬ p (f a) :=
    MarkovMFConsequences.rePred_comp hp hf
  exact hq (hpullback.of_eq fun a => not_congr (hcorrect a))

theorem not_computable_of_not_re
    {A : Type*} [Primcodable A] {p : A → Prop}
    (hp : ¬ REPred p) : ¬ ComputablePred p :=
  fun h => hp h.to_re

theorem no_certificate_system_of_not_re
    {A : Type} [Primcodable A] {p : A → Prop}
    (hp : ¬ REPred p) :
    ¬ ∃ (Cert : Type) (_ : Primcodable Cert) (V : A → Cert → Bool),
      Computable₂ V ∧ ∀ a, (∃ π, V a π = true) ↔ p a := by
  rintro ⟨Cert, hCert, V, hV, hspec⟩
  exact hp ((WordProblemRE.rePred_exists_eq_true hV).of_eq hspec)

/-! ## Pullback identifications -/

abbrev compileSwitch : Code → Code :=
  RecursiveSwitchPresentation.switchEnumeratorCode

theorem computable_compileSwitch : Computable compileSwitch :=
  RecursiveSwitchPresentation.computable_switchEnumeratorCode

theorem compiled_operatorMF_iff_switchWeakMF (c : Code) :
    OperatorMFCode (compileSwitch c) ↔ SwitchWeakMF c := by
  have hweak : SwitchWeakMF c ↔ SecondLevelIndexSets.InfiniteDomain c :=
    (ExactSwitchAlgorithmicConsequences.switchKills_iff_weakMF c).symm.trans
      (ExactSwitchQueryCompleteness.switchKills_iff_infiniteDomain c)
  exact (compiled_operatorMF_iff_infiniteDomain c).trans hweak.symm

theorem compiled_nonOperatorMF_iff_switchNonMF (c : Code) :
    NonOperatorMFCode (compileSwitch c) ↔ SwitchNonMF c := by
  have hnon : SwitchNonMF c ↔ SecondLevelIndexSets.FiniteDomain c :=
    (ExactSwitchAlgorithmicConsequences.switchSurvives_iff_nonMF c).symm.trans
      (ExactSwitchQueryCompleteness.switchSurvives_iff_finiteDomain c)
  exact (compiled_nonOperatorMF_iff_finiteDomain c).trans hnon.symm

/-! ## Global KILL and SURV are neither RE nor coRE -/

theorem standardKills_not_re : ¬ REPred StandardKills :=
  not_re_of_computable_pullback compileSwitch computable_compileSwitch
    compiled_kills_iff_switchKills
    ExactSwitchAlgorithmicConsequences.switchKills_not_re

theorem standardKills_not_core : ¬ Pi01 StandardKills :=
  not_core_of_computable_pullback compileSwitch computable_compileSwitch
    compiled_kills_iff_switchKills
    ExactSwitchAlgorithmicConsequences.switchKills_not_core

theorem standardSurvives_not_re : ¬ REPred StandardSurvives :=
  not_re_of_computable_pullback compileSwitch computable_compileSwitch
    compiled_survives_iff_switchSurvives
    ExactSwitchAlgorithmicConsequences.switchSurvives_not_re

theorem standardSurvives_not_core : ¬ Pi01 StandardSurvives :=
  not_core_of_computable_pullback compileSwitch computable_compileSwitch
    compiled_survives_iff_switchSurvives
    ExactSwitchAlgorithmicConsequences.switchSurvives_not_core

theorem standardKills_not_computable : ¬ ComputablePred StandardKills :=
  not_computable_of_not_re standardKills_not_re

theorem standardSurvives_not_computable : ¬ ComputablePred StandardSurvives :=
  not_computable_of_not_re standardSurvives_not_re

/-! ## Actual Operator-MF and non-Operator-MF are neither RE nor coRE -/

theorem operatorMFCode_not_re : ¬ REPred OperatorMFCode :=
  not_re_of_computable_pullback compileSwitch computable_compileSwitch
    compiled_operatorMF_iff_switchWeakMF
    ExactSwitchAlgorithmicConsequences.switchWeakMF_not_re

theorem operatorMFCode_not_core : ¬ Pi01 OperatorMFCode :=
  not_core_of_computable_pullback compileSwitch computable_compileSwitch
    compiled_operatorMF_iff_switchWeakMF
    ExactSwitchAlgorithmicConsequences.switchWeakMF_not_core

theorem nonOperatorMFCode_not_re : ¬ REPred NonOperatorMFCode :=
  not_re_of_computable_pullback compileSwitch computable_compileSwitch
    compiled_nonOperatorMF_iff_switchNonMF
    ExactSwitchAlgorithmicConsequences.switchNonMF_not_re

theorem nonOperatorMFCode_not_core : ¬ Pi01 NonOperatorMFCode :=
  not_core_of_computable_pullback compileSwitch computable_compileSwitch
    compiled_nonOperatorMF_iff_switchNonMF
    ExactSwitchAlgorithmicConsequences.switchNonMF_not_core

theorem operatorMFCode_not_computable : ¬ ComputablePred OperatorMFCode :=
  not_computable_of_not_re operatorMFCode_not_re

theorem nonOperatorMFCode_not_computable :
    ¬ ComputablePred NonOperatorMFCode :=
  not_computable_of_not_re nonOperatorMFCode_not_re

/-! ## No complete finite checkable certificate systems -/

theorem no_standardKills_certificate_system :
    ¬ ∃ (Cert : Type) (_ : Primcodable Cert) (V : Code → Cert → Bool),
      Computable₂ V ∧
        ∀ c, (∃ π, V c π = true) ↔ StandardKills c :=
  no_certificate_system_of_not_re standardKills_not_re

theorem no_standardSurvives_certificate_system :
    ¬ ∃ (Cert : Type) (_ : Primcodable Cert) (V : Code → Cert → Bool),
      Computable₂ V ∧
        ∀ c, (∃ π, V c π = true) ↔ StandardSurvives c :=
  no_certificate_system_of_not_re standardSurvives_not_re

theorem no_operatorMFCode_certificate_system :
    ¬ ∃ (Cert : Type) (_ : Primcodable Cert) (V : Code → Cert → Bool),
      Computable₂ V ∧
        ∀ c, (∃ π, V c π = true) ↔ OperatorMFCode c :=
  no_certificate_system_of_not_re operatorMFCode_not_re

theorem no_nonOperatorMFCode_certificate_system :
    ¬ ∃ (Cert : Type) (_ : Primcodable Cert) (V : Code → Cert → Bool),
      Computable₂ V ∧
        ∀ c, (∃ π, V c π = true) ↔ NonOperatorMFCode c :=
  no_certificate_system_of_not_re nonOperatorMFCode_not_re

/-- Closed standard-input algorithmic endpoint. -/
theorem standard_algorithmic_package :
    (¬ REPred StandardKills ∧ ¬ Pi01 StandardKills ∧
      ¬ ComputablePred StandardKills) ∧
    (¬ REPred StandardSurvives ∧ ¬ Pi01 StandardSurvives ∧
      ¬ ComputablePred StandardSurvives) ∧
    (¬ REPred OperatorMFCode ∧ ¬ Pi01 OperatorMFCode ∧
      ¬ ComputablePred OperatorMFCode) ∧
    (¬ REPred NonOperatorMFCode ∧ ¬ Pi01 NonOperatorMFCode ∧
      ¬ ComputablePred NonOperatorMFCode) :=
  ⟨⟨standardKills_not_re, standardKills_not_core,
      standardKills_not_computable⟩,
    ⟨standardSurvives_not_re, standardSurvives_not_core,
      standardSurvives_not_computable⟩,
    ⟨operatorMFCode_not_re, operatorMFCode_not_core,
      operatorMFCode_not_computable⟩,
    ⟨nonOperatorMFCode_not_re, nonOperatorMFCode_not_core,
      nonOperatorMFCode_not_computable⟩⟩

end

end EnumeratedFixedMarkedQueryConsequences
end GroupApproximation
