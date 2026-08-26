import GroupApproximation.Computability.MarkovRecognitionHierarchy
import GroupApproximation.Computability.RFPresentationPi02

/-!
# The recognition hierarchy for residual finiteness

Residual finiteness has two complementary effective descriptions in this
library.  On finite presentation codes it has an unconditional `Pi02` upper
bound and a non-r.e. complement.  As a hereditary Markov property, on arbitrary
enumerated presentation codes it has `Pi02`/`Sigma02` hardness and an exactly
complete canonical switch family.

This file packages those facts from one closed datum.  It deliberately does
not turn enumerated-code hardness into finite-code hardness: that would require
the still-open finite-output residually-finite Higman compiler.
-/

namespace GroupApproximation
namespace RFRecognitionHierarchy

open ArithmeticalHierarchy
open AdianRabinGeneral
open HereditaryPropertySwitchCompleteness
open MarkovRecognitionHierarchy
open PresentationCodes
open RFPresentationPi02

/-- Residual finiteness as a group property in the generic Markov interface. -/
abbrev ResiduallyFiniteProperty (H : Type) [Group H] : Prop :=
  Group.ResiduallyFinite H

/-- A fixed finite-presentation witness against residual finiteness. -/
noncomputable def forbiddenRFCode : PresentationCode :=
  Classical.choose exists_non_residuallyFinite_code

theorem forbiddenRFCode_not_residuallyFinite :
    ¬ Group.ResiduallyFinite (Carrier forbiddenRFCode) :=
  Classical.choose_spec exists_non_residuallyFinite_code

/-- Closed Markov data for residual finiteness. -/
noncomputable def rfHierarchyData : MarkovData ResiduallyFiniteProperty :=
  rfMarkovData forbiddenRFCode forbiddenRFCode_not_residuallyFinite

/-- Finite-code strictness together with the full generic Markov recognition
hierarchy, carried by a single closed datum. -/
noncomputable abbrev RFRecognitionHierarchyPackage : Prop :=
  RFPresentationStrictPosition ∧
    RecognitionHierarchyPackage rfHierarchyData

/-- **The full cross-coding recognition package for residual finiteness.** -/
theorem rf_recognition_hierarchy : RFRecognitionHierarchyPackage :=
  ⟨rfPresentationStrictPosition,
    recognition_hierarchy_package rfHierarchyData⟩

/-- The precise boundary currently formalized: second-level upper bounds on
finite presentation codes, and second-level hardness on arbitrary enumerated
presentation codes. -/
theorem rf_finite_bounds_and_enumerated_hardness :
    Pi02 (fun c : PresentationCode => Group.ResiduallyFinite (Carrier c)) ∧
    Sigma02 (fun c : PresentationCode =>
      ¬ Group.ResiduallyFinite (Carrier c)) ∧
    Pi02Hard (EnumeratedCodeProperty ResiduallyFiniteProperty) ∧
    Sigma02Hard
      (fun c => ¬ EnumeratedCodeProperty ResiduallyFiniteProperty c) := by
  have h := recognition_hierarchy_package rfHierarchyData
  exact ⟨pi02_residuallyFinite, sigma02_not_residuallyFinite,
    h.2.2.1, h.2.2.2.1⟩

/-- Exact second-level completeness on the canonical event-ray switch family,
paired with an explicit reduction from the uniform word problem. -/
theorem rf_switch_completeness_and_reduction :
    Pi02Complete (RestrictedProperty (switchData rfHierarchyData)) ∧
    Sigma02Complete (RestrictedComplement (switchData rfHierarchyData)) ∧
    Nonempty
      (MarkovMFConsequences.AdianRabinReduction
        AdianRabinWordProblem.wordProblemPred
        (codeProperty ResiduallyFiniteProperty)) :=
  complete_switch_and_adianRabinReduction rfHierarchyData

end RFRecognitionHierarchy
end GroupApproximation

open GroupApproximation.RFRecognitionHierarchy

#audit_axioms forbiddenRFCode_not_residuallyFinite
#audit_axioms rf_recognition_hierarchy
#audit_axioms rf_finite_bounds_and_enumerated_hardness
#audit_axioms rf_switch_completeness_and_reduction
