import GroupApproximation.Computability.HyperlinearMarkov
import GroupApproximation.Computability.HereditaryRecognitionPhaseDiagram

/-!
# The exact second-level hardness phase transition for hyperlinearity

The arbitrary-seed event-ray compiler applies to hyperlinearity because the
property passes to subgroups and holds for the trivial group.  The finite-table
cover theorem supplies a forbidden finite-presentation code from *any*
non-hyperlinear group.  Consequently, if a counterexample exists, recognising
hyperlinearity on recursively enumerated presentations is `Pi02`-hard and
recognising non-hyperlinearity is `Sigma02`-hard.

The converses are purely recursion-theoretic.  If every group is hyperlinear,
the first predicate is constantly true and the second constantly false; neither
can be hard at its respective second level.  Thus second-level hardness is not
merely a consequence of a counterexample: it is equivalent to one.
-/

namespace GroupApproximation
namespace HyperlinearRecognitionSecondLevel

open ArithmeticalHierarchy
open PresentationCodes
open HereditaryRecognitionPhaseDiagram

/-- Hyperlinearity on standard recursively enumerated presentation codes. -/
abbrev HyperlinearEnumeratedCodeProperty :
    EnumeratedPresentationCodes.PresentationCode → Prop :=
  fun q ↦ IsHyperlinear (EnumeratedPresentationCodes.Carrier q)

/-- Hyperlinearity has the finite-counterexample-cover property, by the finite
table obstruction theorem. -/
theorem hyperlinear_hasFiniteCounterexampleCover :
    HasFiniteCounterexampleCover HyperlinearMarkov.HyperlinearProperty :=
  HyperlinearMarkov.exists_nonhyperlinear_code_of_exists

/-- A non-hyperlinear group makes hyperlinearity `Pi02`-hard on recursively
enumerated presentation codes. -/
theorem hyperlinearEnumeratedCodeProperty_pi02Hard_of_exists
    (h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    Pi02Hard HyperlinearEnumeratedCodeProperty :=
  pi02Hard_of_exists_of_finiteCover
    HyperlinearMarkov.HyperlinearProperty
    (fun f hf hK ↦ isHyperlinear_of_injective f hf hK)
    (isHyperlinear_of_finite PUnit) hyperlinear_hasFiniteCounterexampleCover h

/-- Under the same hypothesis, non-hyperlinearity is `Sigma02`-hard on the
same standard codes. -/
theorem nonhyperlinearEnumeratedCodeProperty_sigma02Hard_of_exists
    (h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) :=
  pi02Hard_compl (hyperlinearEnumeratedCodeProperty_pi02Hard_of_exists h)

/-- Second-level hardness of hyperlinearity forces a non-hyperlinear group:
otherwise the target predicate is constantly true. -/
theorem exists_not_isHyperlinear_of_hyperlinearEnumeratedCodeProperty_pi02Hard
    (h : Pi02Hard HyperlinearEnumeratedCodeProperty) :
    ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G :=
  exists_failure_of_pi02Hard h

/-- Second-level hardness of non-hyperlinearity likewise forces a
counterexample: without one its target predicate is constantly false. -/
theorem exists_not_isHyperlinear_of_nonhyperlinearEnumeratedCodeProperty_sigma02Hard
    (h : Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q)) :
    ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G :=
  exists_failure_of_sigma02Hard_compl h

/-- **Exact hardness phase transition.**  A non-hyperlinear group exists iff
hyperlinearity of recursively enumerated presentations is `Pi02`-hard. -/
theorem exists_not_isHyperlinear_iff_hyperlinearEnumeratedCodeProperty_pi02Hard :
    (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      Pi02Hard HyperlinearEnumeratedCodeProperty :=
  ⟨hyperlinearEnumeratedCodeProperty_pi02Hard_of_exists,
    exists_not_isHyperlinear_of_hyperlinearEnumeratedCodeProperty_pi02Hard⟩

/-- The complementary exact phase transition at `Sigma02`. -/
theorem exists_not_isHyperlinear_iff_nonhyperlinearEnumeratedCodeProperty_sigma02Hard :
    (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) :=
  ⟨nonhyperlinearEnumeratedCodeProperty_sigma02Hard_of_exists,
    exists_not_isHyperlinear_of_nonhyperlinearEnumeratedCodeProperty_sigma02Hard⟩

/-- Both sides of the conditional second-level classification at once. -/
theorem hyperlinear_second_level_hardness_package_of_exists
    (h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    Pi02Hard HyperlinearEnumeratedCodeProperty ∧
      Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) :=
  ⟨hyperlinearEnumeratedCodeProperty_pi02Hard_of_exists h,
    nonhyperlinearEnumeratedCodeProperty_sigma02Hard_of_exists h⟩

/-! ## The unconditional recognition phase diagram -/

/-- If every group is hyperlinear, the enumerated hyperlinearity predicate is
the computable constant-true predicate. -/
theorem hyperlinearEnumeratedCodeProperty_computable_of_universal
    (h : ∀ (G : Type) (_ : Group G), IsHyperlinear G) :
    ComputablePred HyperlinearEnumeratedCodeProperty :=
  enumeratedCodeProperty_computable_of_universal
    HyperlinearMarkov.HyperlinearProperty h

/-- In the universal regime, the negative predicate is computably empty. -/
theorem nonhyperlinearEnumeratedCodeProperty_computable_of_universal
    (h : ∀ (G : Type) (_ : Group G), IsHyperlinear G) :
    ComputablePred (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) :=
  enumeratedCodeProperty_compl_computable_of_universal
    HyperlinearMarkov.HyperlinearProperty h

/-- The two exhaustive recognition regimes.  This theorem is unconditional:
which branch holds is precisely the open non-hyperlinear-group problem. -/
theorem hyperlinear_recognition_phase_dichotomy :
    ((∀ (G : Type) (_ : Group G), IsHyperlinear G) ∧
      ComputablePred HyperlinearEnumeratedCodeProperty ∧
      REPred (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q)) ∨
    ((∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ∧
      Pi02Hard HyperlinearEnumeratedCodeProperty ∧
      Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q)) :=
  recognition_phase_dichotomy HyperlinearMarkov.HyperlinearProperty
    (fun f hf hK ↦ isHyperlinear_of_injective f hf hK)
    (isHyperlinear_of_finite PUnit) hyperlinear_hasFiniteCounterexampleCover

/-- The two branches of `hyperlinear_recognition_phase_dichotomy` are
disjoint. -/
theorem hyperlinear_recognition_phase_branches_disjoint :
    ¬ ((∀ (G : Type) (_ : Group G), IsHyperlinear G) ∧
      (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G)) := by
  rintro ⟨hall, G, groupG, hG⟩
  exact hG (hall G groupG)

/-! ## Completeness once the effective upper bound is supplied -/

/-- Any `Pi02` upper bound upgrades the hard branch to completeness. -/
theorem hyperlinearEnumeratedCodeProperty_pi02Complete_of_exists
    (hupper : Pi02 HyperlinearEnumeratedCodeProperty)
    (h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    Pi02Complete HyperlinearEnumeratedCodeProperty :=
  ⟨hupper, hyperlinearEnumeratedCodeProperty_pi02Hard_of_exists h⟩

/-- With the effective upper bound fixed, `Pi02`-completeness is equivalent to
the existence of a non-hyperlinear group. -/
theorem exists_not_isHyperlinear_iff_hyperlinearEnumeratedCodeProperty_pi02Complete
    (hupper : Pi02 HyperlinearEnumeratedCodeProperty) :
    (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      Pi02Complete HyperlinearEnumeratedCodeProperty :=
  exists_failure_iff_pi02Complete HyperlinearMarkov.HyperlinearProperty
    (fun f hf hK ↦ isHyperlinear_of_injective f hf hK)
    (isHyperlinear_of_finite PUnit) hyperlinear_hasFiniteCounterexampleCover hupper

/-- The same upper bound gives the complementary `Sigma02` classification. -/
theorem exists_not_isHyperlinear_iff_nonhyperlinearEnumeratedCodeProperty_sigma02Complete
    (hupper : Pi02 HyperlinearEnumeratedCodeProperty) :
    (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      Sigma02Complete (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) :=
  exists_failure_iff_sigma02Complete_compl HyperlinearMarkov.HyperlinearProperty
    (fun f hf hK ↦ isHyperlinear_of_injective f hf hK)
    (isHyperlinear_of_finite PUnit) hyperlinear_hasFiniteCounterexampleCover hupper

end HyperlinearRecognitionSecondLevel
end GroupApproximation

open GroupApproximation.HyperlinearRecognitionSecondLevel

#audit_axioms hyperlinearEnumeratedCodeProperty_pi02Hard_of_exists
#audit_axioms nonhyperlinearEnumeratedCodeProperty_sigma02Hard_of_exists
#audit_axioms exists_not_isHyperlinear_iff_hyperlinearEnumeratedCodeProperty_pi02Hard
#audit_axioms exists_not_isHyperlinear_iff_nonhyperlinearEnumeratedCodeProperty_sigma02Hard
#audit_axioms hyperlinear_second_level_hardness_package_of_exists
#audit_axioms hyperlinear_recognition_phase_dichotomy
#audit_axioms hyperlinear_recognition_phase_branches_disjoint
#audit_axioms exists_not_isHyperlinear_iff_hyperlinearEnumeratedCodeProperty_pi02Complete
#audit_axioms exists_not_isHyperlinear_iff_nonhyperlinearEnumeratedCodeProperty_sigma02Complete
