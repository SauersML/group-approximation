import GroupApproximation.Computability.AdianRabinGeneral
import GroupApproximation.Computability.SoficMarkov
import GroupApproximation.Sofic.Hyperlinear

/-!
# Undecidability of hyperlinearity is equivalent to a non-hyperlinear presentation

The research route `non-hyperlinear-from-hyperlinear-recognition-undecidable`
(toward the program goal `non-hyperlinear-group`) is the observation that if
every group were hyperlinear, the property of finite presentation codes
"the presented group is hyperlinear" would be constantly true, hence
computable.  So any proof that this property is not computable — for
instance a halting-problem reduction in the style of `MIP* = RE` — yields a
finite presentation code whose group is not hyperlinear, without naming it.

Conversely, one non-hyperlinear code makes hyperlinearity a Markov property
(heredity `isHyperlinear_of_injective`, free groups are sofic hence
hyperlinear, the trivial code is positive), so the Adian--Rabin theorem of
`Computability.AdianRabinGeneral` gives undecidability from the word
problem.  Together: hyperlinearity of finite presentations is undecidable iff
some finite presentation presents a non-hyperlinear group.  This is the
finite-presentation instance of the research claim
`approximation-property-recognition-dichotomy`.
-/

namespace GroupApproximation
namespace HyperlinearUndecidabilityRoute

open PresentationCodes AdianRabinGeneral SoficMarkov

/-- A predicate that holds everywhere is computable. -/
theorem computablePred_of_forall {α : Type} [Primcodable α] {p : α → Prop}
    (h : ∀ a, p a) : ComputablePred p := by
  classical
  refine ⟨inferInstance, ?_⟩
  exact (Computable.const true).of_eq (fun a => by simp [h a])

/-- The hyperlinearity predicate on finite presentation codes. -/
def hyperlinearCode : PresentationCode → Prop :=
  codeProperty (fun (K : Type) (_ : Group K) ↦ IsHyperlinear K)

/-- **If hyperlinearity of finitely presented groups is not computable, some
finite presentation code presents a non-hyperlinear group.** -/
theorem exists_nonhyperlinear_code_of_not_computablePred
    (h : ¬ ComputablePred hyperlinearCode) :
    ∃ c : PresentationCode, ¬ IsHyperlinear (Carrier c) := by
  by_contra hcon
  push_neg at hcon
  exact h (computablePred_of_forall hcon)

/-- The group-level form: a non-hyperlinear group exists. -/
theorem exists_nonhyperlinear_group_of_not_computablePred
    (h : ¬ ComputablePred hyperlinearCode) :
    ∃ (H : Type) (_ : Group H), ¬ IsHyperlinear H := by
  obtain ⟨c, hc⟩ := exists_nonhyperlinear_code_of_not_computablePred h
  exact ⟨Carrier c, inferInstance, hc⟩

/-- The trivial code presents a hyperlinear group. -/
theorem isHyperlinear_trivialCode : IsHyperlinear (Carrier trivialCode) :=
  isHyperlinear_of_isSofic isSofic_trivialCode

/-- **Hyperlinearity is a Markov property**, given a code for a
non-hyperlinear group. -/
noncomputable def hyperlinearMarkovData (c : PresentationCode)
    (hc : ¬ IsHyperlinear (Carrier c)) :
    MarkovData (fun (H : Type) (_ : Group H) ↦ IsHyperlinear H) where
  hereditary f hf hK := isHyperlinear_of_injective f hf hK
  free α _ := isHyperlinear_of_isSofic (isSofic_freeGroup α)
  positiveCode := trivialCode
  positive := isHyperlinear_trivialCode
  forbidden := c
  forbidden_not := hc

/-- **Hyperlinearity of finite presentations is undecidable iff some finite
presentation presents a non-hyperlinear group**, given undecidability of the
word problem (Novikov--Boone). -/
theorem not_computablePred_iff_exists_nonhyperlinear_code
    (hw : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ ComputablePred hyperlinearCode ↔
      ∃ c : PresentationCode, ¬ IsHyperlinear (Carrier c) := by
  constructor
  · exact exists_nonhyperlinear_code_of_not_computablePred
  · rintro ⟨c, hc⟩
    exact recognition_undecidable_of_wordProblem (hyperlinearMarkovData c hc) hw

end HyperlinearUndecidabilityRoute
end GroupApproximation
