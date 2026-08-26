import GroupApproximation.Computability.HyperlinearMarkov
import GroupApproximation.Computability.HyperlinearRecognitionSecondLevel

/-!
# The full recognition hierarchy for hyperlinearity

The finite-presentation Adian--Rabin theorem and the enumerated-presentation
second-level Rice theorem have the same phase transition: existence of a
non-hyperlinear group.  This file identifies their conclusions directly.

Thus undecidability on finite presentation codes, failure of recursive
enumerability on the negative finite-code side, second-level hardness on
enumerated codes, existence of Markov data, and existence of an explicit
Adian--Rabin reduction are all equivalent statements.  The final theorem
packages the universal and counterexample regimes across both coding levels.
-/

namespace GroupApproximation
namespace HyperlinearRecognitionHierarchy

open ArithmeticalHierarchy
open HyperlinearMarkov
open HyperlinearRecognitionSecondLevel

/-- Finite-code undecidability is exactly enumerated-code `Pi02` hardness. -/
theorem finite_not_computable_iff_enumerated_pi02Hard :
    (¬ ComputablePred HyperlinearCodeProperty) ↔
      Pi02Hard HyperlinearEnumeratedCodeProperty :=
  exists_not_isHyperlinear_iff_codeProperty_not_computable.symm.trans
    exists_not_isHyperlinear_iff_hyperlinearEnumeratedCodeProperty_pi02Hard

/-- Failure of r.e.-ness for negative finite codes is exactly `Sigma02`
hardness for negative enumerated codes. -/
theorem finite_negative_not_re_iff_enumerated_negative_sigma02Hard :
    (¬ REPred (fun c ↦ ¬ HyperlinearCodeProperty c)) ↔
      Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) :=
  exists_not_isHyperlinear_iff_nonhyperlinearCodeProperty_not_re.symm.trans
    exists_not_isHyperlinear_iff_nonhyperlinearEnumeratedCodeProperty_sigma02Hard

/-- A concrete forbidden finite-presentation code exists exactly in the
enumerated `Pi02`-hard regime. -/
theorem exists_finite_forbiddenCode_iff_enumerated_pi02Hard :
    (∃ c : PresentationCodes.PresentationCode,
      ¬ IsHyperlinear (PresentationCodes.Carrier c)) ↔
      Pi02Hard HyperlinearEnumeratedCodeProperty :=
  exists_nonhyperlinear_code_iff_codeProperty_not_computable.trans
    finite_not_computable_iff_enumerated_pi02Hard

/-- Hyperlinearity admits Adian--Rabin Markov data exactly in the
second-level-hard regime. -/
theorem nonempty_markovData_iff_enumerated_pi02Hard :
    Nonempty (AdianRabinGeneral.MarkovData HyperlinearProperty) ↔
      Pi02Hard HyperlinearEnumeratedCodeProperty :=
  exists_not_isHyperlinear_iff_nonempty_markovData.symm.trans
    exists_not_isHyperlinear_iff_hyperlinearEnumeratedCodeProperty_pi02Hard

/-- Existence of the explicit uniform-word-problem reduction is exactly
enumerated `Pi02` hardness. -/
theorem nonempty_adianRabinReduction_iff_enumerated_pi02Hard :
    Nonempty
        (MarkovMFConsequences.AdianRabinReduction
          AdianRabinWordProblem.wordProblemPred HyperlinearCodeProperty) ↔
      Pi02Hard HyperlinearEnumeratedCodeProperty :=
  exists_not_isHyperlinear_iff_nonempty_adianRabinReduction.symm.trans
    exists_not_isHyperlinear_iff_hyperlinearEnumeratedCodeProperty_pi02Hard

/-- Finite-code decidability occurs exactly when enumerated recognition is not
`Pi02`-hard. -/
theorem finite_computable_iff_enumerated_not_pi02Hard :
    ComputablePred HyperlinearCodeProperty ↔
      ¬ Pi02Hard HyperlinearEnumeratedCodeProperty := by
  constructor
  · intro hcomp hhard
    exact (finite_not_computable_iff_enumerated_pi02Hard.mpr hhard) hcomp
  · intro hnothard
    have hall :=
      all_isHyperlinear_iff_not_hyperlinearEnumeratedCodeProperty_pi02Hard.mpr
        hnothard
    have hnone : ¬ ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G := by
      push Not
      exact hall
    exact hyperlinearCodeProperty_computable_of_no_counterexample hnone

/-- The negative finite-code set is r.e. exactly when the negative enumerated
predicate is not `Sigma02`-hard. -/
theorem finite_negative_re_iff_enumerated_negative_not_sigma02Hard :
    REPred (fun c ↦ ¬ HyperlinearCodeProperty c) ↔
      ¬ Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) := by
  constructor
  · intro hre hhard
    exact (finite_negative_not_re_iff_enumerated_negative_sigma02Hard.mpr hhard) hre
  · intro hnothard
    have hall :=
      all_isHyperlinear_iff_not_nonhyperlinearEnumeratedCodeProperty_sigma02Hard.mpr
        hnothard
    have hnone : ¬ ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G := by
      push Not
      exact hall
    exact no_counterexample_iff_nonhyperlinearCodeProperty_re.mp hnone

/-- **Unconditional hierarchy-wide recognition dichotomy.**  Exactly the open
existence question chooses between a fully computable finite-code regime with
no second-level hardness, and a finite-code-undecidable, negative-non-r.e.,
second-level-hard regime carrying an explicit Adian--Rabin reduction. -/
theorem hyperlinear_recognition_hierarchy_dichotomy :
    ((∀ (G : Type) (_ : Group G), IsHyperlinear G) ∧
      ComputablePred HyperlinearCodeProperty ∧
      REPred (fun c ↦ ¬ HyperlinearCodeProperty c) ∧
      ¬ Pi02Hard HyperlinearEnumeratedCodeProperty ∧
      ¬ Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q)) ∨
    ((∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ∧
      ¬ ComputablePred HyperlinearCodeProperty ∧
      ¬ REPred (fun c ↦ ¬ HyperlinearCodeProperty c) ∧
      Pi02Hard HyperlinearEnumeratedCodeProperty ∧
      Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) ∧
      Nonempty
        (MarkovMFConsequences.AdianRabinReduction
          AdianRabinWordProblem.wordProblemPred HyperlinearCodeProperty)) := by
  classical
  by_cases h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G
  · exact Or.inr ⟨h,
      hyperlinearCodeProperty_not_computable_of_exists h,
      nonhyperlinearCodeProperty_not_re_of_exists h,
      hyperlinearEnumeratedCodeProperty_pi02Hard_of_exists h,
      nonhyperlinearEnumeratedCodeProperty_sigma02Hard_of_exists h,
      exists_not_isHyperlinear_iff_nonempty_adianRabinReduction.mp h⟩
  · have hall : ∀ (G : Type) (_ : Group G), IsHyperlinear G := by
      push Not at h
      exact h
    exact Or.inl ⟨hall,
      hyperlinearCodeProperty_computable_of_no_counterexample (by
        push Not
        exact hall),
      no_counterexample_iff_nonhyperlinearCodeProperty_re.mp (by
        push Not
        exact hall),
      all_isHyperlinear_iff_not_hyperlinearEnumeratedCodeProperty_pi02Hard.mp hall,
      all_isHyperlinear_iff_not_nonhyperlinearEnumeratedCodeProperty_sigma02Hard.mp hall⟩

end HyperlinearRecognitionHierarchy
end GroupApproximation

open GroupApproximation.HyperlinearRecognitionHierarchy

#audit_axioms finite_not_computable_iff_enumerated_pi02Hard
#audit_axioms finite_negative_not_re_iff_enumerated_negative_sigma02Hard
#audit_axioms exists_finite_forbiddenCode_iff_enumerated_pi02Hard
#audit_axioms nonempty_markovData_iff_enumerated_pi02Hard
#audit_axioms nonempty_adianRabinReduction_iff_enumerated_pi02Hard
#audit_axioms finite_computable_iff_enumerated_not_pi02Hard
#audit_axioms finite_negative_re_iff_enumerated_negative_not_sigma02Hard
#audit_axioms hyperlinear_recognition_hierarchy_dichotomy
