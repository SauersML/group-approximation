import GroupApproximation.Computability.AdianRabinGeneral
import GroupApproximation.Computability.BooneWordProblemUndecidable
import GroupApproximation.Computability.HereditaryPropertySwitchCompleteness
import GroupApproximation.Computability.WordProblemRE
import GroupApproximation.Meta.AxiomGuard

/-!
# The full recognition hierarchy of an arbitrary Markov group property

`AdianRabinGeneral` gives first-level undecidability and non-enumerability from
Markov data.  `HereditaryPropertySwitchCompleteness` independently gives
second-level hardness and an exact complete event-ray family.  They consume the
same group-theoretic input.  This file combines them into one audited endpoint.

For every group property equipped with `MarkovData`, the package contains:

* undecidability on finite presentation codes;
* failure of r.e.-ness of the negative finite-code set;
* `Pi02`/`Sigma02` hardness on arbitrary enumerated presentation codes;
* `Pi02`/`Sigma02` completeness on the canonical compiled switch family; and
* an explicit computable Adian--Rabin reduction from the uniform word problem.
-/

namespace GroupApproximation
namespace MarkovRecognitionHierarchy

open ArithmeticalHierarchy
open AdianRabinGeneral
open HereditaryPropertySwitchCompleteness
open PresentationCodes

variable {P : (H : Type) → [Group H] → Prop}

/-- The canonical second-level switch data carried by Markov data. -/
noncomputable abbrev switchData (D : MarkovData P) : SwitchPropertyData P :=
  SwitchPropertyData.ofMarkovData D

/-- The proposition collecting every first- and second-level consequence of a
single Markov datum. -/
noncomputable abbrev RecognitionHierarchyPackage (D : MarkovData P) : Prop :=
    (¬ ComputablePred (codeProperty P)) ∧
    (¬ REPred (fun c ↦ ¬ codeProperty P c)) ∧
    Pi02Hard (EnumeratedCodeProperty P) ∧
    Sigma02Hard (fun c ↦ ¬ EnumeratedCodeProperty P c) ∧
    Pi02Complete (RestrictedProperty (switchData D)) ∧
    Sigma02Complete (RestrictedComplement (switchData D)) ∧
    Nonempty
      (MarkovMFConsequences.AdianRabinReduction
        AdianRabinWordProblem.wordProblemPred (codeProperty P))

/-- **The full hierarchy package for an arbitrary Markov property.** -/
theorem recognition_hierarchy_package (D : MarkovData P) :
    RecognitionHierarchyPackage D := by
  have hswitch := switch_completeness_package (switchData D)
  exact ⟨recognition_undecidable_of_wordProblem D
      Computability.not_computablePred_wordProblemPred,
    negative_side_not_re_of_wordProblem D
      WordProblemRE.not_rePred_compl_wordProblemPred,
    hswitch.2.2.1,
    hswitch.2.2.2,
    hswitch.1,
    hswitch.2.1,
    ⟨reduction D⟩⟩

/-- The finite-code consequences and enumerated-code consequences are both
projections of the same Markov-data construction. -/
theorem finite_and_enumerated_hardness_package (D : MarkovData P) :
    (¬ ComputablePred (codeProperty P)) ∧
    (¬ REPred (fun c ↦ ¬ codeProperty P c)) ∧
    Pi02Hard (EnumeratedCodeProperty P) ∧
    Sigma02Hard (fun c ↦ ¬ EnumeratedCodeProperty P c) := by
  have h := recognition_hierarchy_package D
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Exact completeness of the canonical event-ray family, paired with the
explicit first-level reduction that uses the same Markov datum. -/
theorem complete_switch_and_adianRabinReduction (D : MarkovData P) :
    Pi02Complete (RestrictedProperty (switchData D)) ∧
    Sigma02Complete (RestrictedComplement (switchData D)) ∧
    Nonempty
      (MarkovMFConsequences.AdianRabinReduction
        AdianRabinWordProblem.wordProblemPred (codeProperty P)) := by
  have h := recognition_hierarchy_package D
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end MarkovRecognitionHierarchy
end GroupApproximation

open GroupApproximation.MarkovRecognitionHierarchy

#audit_axioms recognition_hierarchy_package
#audit_axioms finite_and_enumerated_hardness_package
#audit_axioms complete_switch_and_adianRabinReduction
