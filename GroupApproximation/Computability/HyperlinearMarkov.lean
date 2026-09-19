import GroupApproximation.Computability.AdianRabinGeneral
import GroupApproximation.Computability.BooneWordProblemUndecidable
import GroupApproximation.Computability.WordProblemRE
import GroupApproximation.Covers.HyperlinearTableCover
import GroupApproximation.Sofic.FreeGroupResiduallyFinite

/-!
# Hyperlinearity is Markov exactly when a counterexample exists

The finite-table cover theorem turns any non-hyperlinear group into a finitely
presented one.  That is precisely the missing negative datum in the general
Adian--Rabin theorem.  Hence existence of a non-hyperlinear group forces
undecidability of hyperlinearity on finite presentation codes.

Conversely, if no non-hyperlinear group exists, the code predicate is the
constant-true computable predicate.  Thus the existence problem and the
recognition problem are equivalent.
-/

namespace GroupApproximation
namespace HyperlinearMarkov

open PresentationCodes AdianRabinGeneral

/-- Hyperlinearity as a property of abstract groups in `Type`. -/
abbrev HyperlinearProperty : (H : Type) → [Group H] → Prop :=
  fun H _ ↦ IsHyperlinear H

/-- Hyperlinearity on finite presentation codes. -/
abbrev HyperlinearCodeProperty : PresentationCode → Prop :=
  codeProperty HyperlinearProperty

/-- The trivial finite presentation is hyperlinear. -/
theorem isHyperlinear_trivialCode : IsHyperlinear (Carrier trivialCode) := by
  haveI := subsingleton_carrier_trivialCode
  haveI : Finite (Carrier trivialCode) := Finite.of_subsingleton
  exact isHyperlinear_of_finite (Carrier trivialCode)

/-- Hyperlinearity is Markov once a single forbidden finite-presentation code
is supplied. -/
noncomputable def hyperlinearMarkovData (c : PresentationCode)
    (hc : ¬ IsHyperlinear (Carrier c)) : MarkovData HyperlinearProperty where
  hereditary f hf hK := isHyperlinear_of_injective f hf hK
  free α _ := isHyperlinear_of_isSofic (isSofic_freeGroup α)
  positiveCode := trivialCode
  positive := isHyperlinear_trivialCode
  forbidden := c
  forbidden_not := hc

/-- A finitely presented non-hyperlinear group supplies an actual forbidden
presentation code. -/
theorem exists_nonhyperlinear_code {H : Type} [Group H]
    [Group.IsFinitelyPresented H] (hH : ¬ IsHyperlinear H) :
    ∃ c : PresentationCode, ¬ IsHyperlinear (Carrier c) := by
  obtain ⟨c, ⟨e⟩⟩ := exists_code_mulEquiv H
  refine ⟨c, fun hc ↦ hH ?_⟩
  exact isHyperlinear_of_injective e.symm.toMonoidHom e.symm.injective hc

/-- Any non-hyperlinear group, with no presentation hypothesis, supplies a
forbidden finite-presentation code. -/
theorem exists_nonhyperlinear_code_of_exists
    (h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    ∃ c : PresentationCode, ¬ IsHyperlinear (Carrier c) := by
  obtain ⟨H, _, hfp, hH⟩ :=
    exists_not_isHyperlinear_iff_exists_finitelyPresented.mp h
  letI : Group.IsFinitelyPresented H := hfp
  exact exists_nonhyperlinear_code hH

/-- Non-hyperlinear existence canonically provides all of hyperlinearity's
Adian--Rabin input data. -/
noncomputable def hyperlinearMarkovDataOfExists
    (h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    MarkovData HyperlinearProperty := by
  let c := Classical.choose (exists_nonhyperlinear_code_of_exists h)
  exact hyperlinearMarkovData c
    (Classical.choose_spec (exists_nonhyperlinear_code_of_exists h))

/-- **Forward recognition theorem.**  If a non-hyperlinear group exists, then
hyperlinearity of finite presentation codes is undecidable. -/
theorem hyperlinearCodeProperty_not_computable_of_exists
    (h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    ¬ ComputablePred HyperlinearCodeProperty :=
  recognition_undecidable_of_wordProblem (hyperlinearMarkovDataOfExists h)
    Computability.not_computablePred_wordProblemPred

/-- Under the same existence hypothesis, the non-hyperlinear finite
presentation codes are not recursively enumerable. -/
theorem nonhyperlinearCodeProperty_not_re_of_exists
    (h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    ¬ REPred (fun c ↦ ¬ HyperlinearCodeProperty c) :=
  negative_side_not_re_of_wordProblem (hyperlinearMarkovDataOfExists h)
    WordProblemRE.not_rePred_compl_wordProblemPred

/-- If there is no non-hyperlinear group, hyperlinearity recognition is the
computable constant-true predicate. -/
theorem hyperlinearCodeProperty_computable_of_no_counterexample
    (h : ¬ ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    ComputablePred HyperlinearCodeProperty := by
  push Not at h
  letI : DecidablePred HyperlinearCodeProperty :=
    fun c ↦ isTrue (h (Carrier c) inferInstance)
  exact ⟨inferInstance, Computable.const true⟩

/-- If hyperlinearity recognition is undecidable, some group must fail
hyperlinearity: otherwise its code predicate is computably constant true. -/
theorem exists_not_isHyperlinear_of_codeProperty_not_computable
    (h : ¬ ComputablePred HyperlinearCodeProperty) :
    ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G := by
  by_contra hnone
  exact h (hyperlinearCodeProperty_computable_of_no_counterexample hnone)

/-- **Recognition/existence equivalence.**  Non-hyperlinear groups exist if and
only if hyperlinearity on finite presentation codes is undecidable. -/
theorem exists_not_isHyperlinear_iff_codeProperty_not_computable :
    (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      ¬ ComputablePred HyperlinearCodeProperty :=
  ⟨hyperlinearCodeProperty_not_computable_of_exists,
    exists_not_isHyperlinear_of_codeProperty_not_computable⟩

/-- **Enumeration/existence equivalence.**  Non-hyperlinear groups exist if
and only if the non-hyperlinear finite-presentation codes are not recursively
enumerable. -/
theorem exists_not_isHyperlinear_iff_nonhyperlinearCodeProperty_not_re :
    (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      ¬ REPred (fun c ↦ ¬ HyperlinearCodeProperty c) := by
  constructor
  · exact nonhyperlinearCodeProperty_not_re_of_exists
  · intro hnotre
    by_contra hnone
    exact hnotre
      (hyperlinearCodeProperty_computable_of_no_counterexample hnone).not.to_re

/-- The easy side of the dichotomy: no counterexample exists exactly when
hyperlinearity recognition is computable. -/
theorem no_counterexample_iff_hyperlinearCodeProperty_computable :
    (¬ ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      ComputablePred HyperlinearCodeProperty := by
  constructor
  · exact hyperlinearCodeProperty_computable_of_no_counterexample
  · intro hcomp hexists
    exact (hyperlinearCodeProperty_not_computable_of_exists hexists) hcomp

/-- Equivalently, the negative code set is recursively enumerable precisely
on the no-counterexample side. -/
theorem no_counterexample_iff_nonhyperlinearCodeProperty_re :
    (¬ ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      REPred (fun c ↦ ¬ HyperlinearCodeProperty c) := by
  constructor
  · intro hnone
    exact (hyperlinearCodeProperty_computable_of_no_counterexample hnone).not.to_re
  · intro hre hexists
    exact (nonhyperlinearCodeProperty_not_re_of_exists hexists) hre

/-- Hyperlinearity has Adian--Rabin Markov data exactly when a
non-hyperlinear group exists. -/
theorem exists_not_isHyperlinear_iff_nonempty_markovData :
    (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      Nonempty (MarkovData HyperlinearProperty) := by
  constructor
  · intro h
    exact ⟨hyperlinearMarkovDataOfExists h⟩
  · rintro ⟨D⟩
    exact ⟨Carrier D.forbidden, inferInstance, D.forbidden_not⟩

/-- **Reduction/existence equivalence.**  A non-hyperlinear group exists
exactly when there is an explicit computable Adian--Rabin reduction from the
uniform word problem to hyperlinearity of finite presentation codes. -/
theorem exists_not_isHyperlinear_iff_nonempty_adianRabinReduction :
    (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      Nonempty
        (MarkovMFConsequences.AdianRabinReduction
          AdianRabinWordProblem.wordProblemPred HyperlinearCodeProperty) := by
  constructor
  · intro h
    exact ⟨reduction (hyperlinearMarkovDataOfExists h)⟩
  · rintro ⟨R⟩
    exact ⟨Carrier R.markov.negativeCode, inferInstance, R.markov.negative⟩

/-- **Finite-presentation recognition equivalence.**  A forbidden finite
presentation exists exactly when hyperlinearity recognition is undecidable.
Unlike the group-level statement, this packages the negative witness in the
same concrete code space on which recognition is formulated. -/
theorem exists_nonhyperlinear_code_iff_codeProperty_not_computable :
    (∃ c : PresentationCode, ¬ IsHyperlinear (Carrier c)) ↔
      ¬ ComputablePred HyperlinearCodeProperty := by
  constructor
  · rintro ⟨c, hc⟩
    exact hyperlinearCodeProperty_not_computable_of_exists
      ⟨Carrier c, inferInstance, hc⟩
  · intro h
    exact exists_nonhyperlinear_code_of_exists
      (exists_not_isHyperlinear_of_codeProperty_not_computable h)

/-- A forbidden finite-presentation code exists exactly when the negative
hyperlinearity code set fails to be recursively enumerable. -/
theorem exists_nonhyperlinear_code_iff_nonhyperlinearCodeProperty_not_re :
    (∃ c : PresentationCode, ¬ IsHyperlinear (Carrier c)) ↔
      ¬ REPred (fun c ↦ ¬ HyperlinearCodeProperty c) := by
  constructor
  · rintro ⟨c, hc⟩
    exact nonhyperlinearCodeProperty_not_re_of_exists
      ⟨Carrier c, inferInstance, hc⟩
  · intro h
    exact exists_nonhyperlinear_code_of_exists
      (exists_not_isHyperlinear_iff_nonhyperlinearCodeProperty_not_re.mpr h)

/-- The concrete forbidden-code formulation of the reduction dichotomy. -/
theorem exists_nonhyperlinear_code_iff_nonempty_adianRabinReduction :
    (∃ c : PresentationCode, ¬ IsHyperlinear (Carrier c)) ↔
      Nonempty
        (MarkovMFConsequences.AdianRabinReduction
          AdianRabinWordProblem.wordProblemPred HyperlinearCodeProperty) := by
  constructor
  · rintro ⟨c, hc⟩
    exact exists_not_isHyperlinear_iff_nonempty_adianRabinReduction.mp
      ⟨Carrier c, inferInstance, hc⟩
  · intro h
    exact exists_nonhyperlinear_code_of_exists
      (exists_not_isHyperlinear_iff_nonempty_adianRabinReduction.mpr h)

end HyperlinearMarkov
end GroupApproximation

open GroupApproximation.HyperlinearMarkov

#audit_axioms hyperlinearCodeProperty_not_computable_of_exists
#audit_axioms nonhyperlinearCodeProperty_not_re_of_exists
#audit_axioms exists_not_isHyperlinear_iff_codeProperty_not_computable
#audit_axioms exists_not_isHyperlinear_iff_nonhyperlinearCodeProperty_not_re
#audit_axioms no_counterexample_iff_hyperlinearCodeProperty_computable
#audit_axioms no_counterexample_iff_nonhyperlinearCodeProperty_re
#audit_axioms exists_not_isHyperlinear_iff_nonempty_markovData
#audit_axioms exists_not_isHyperlinear_iff_nonempty_adianRabinReduction
#audit_axioms exists_nonhyperlinear_code_iff_codeProperty_not_computable
#audit_axioms exists_nonhyperlinear_code_iff_nonhyperlinearCodeProperty_not_re
#audit_axioms exists_nonhyperlinear_code_iff_nonempty_adianRabinReduction
