import GroupApproximation.Computability.HyperlinearMarkov
import GroupApproximation.Computability.SoficRecognitionSecondLevel

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

/-- Hyperlinearity on standard recursively enumerated presentation codes. -/
abbrev HyperlinearEnumeratedCodeProperty :
    EnumeratedPresentationCodes.PresentationCode → Prop :=
  fun q ↦ IsHyperlinear (EnumeratedPresentationCodes.Carrier q)

/-- The empty numerical predicate belongs to `Pi02`. -/
private theorem pi02_false : Pi02 (fun _ : ℕ ↦ False) := by
  letI : DecidablePred (fun _ : ℕ × ℕ ↦ False) := fun _ ↦ isFalse id
  have hcomp : ComputablePred (fun _ : ℕ × ℕ ↦ False) :=
    ⟨inferInstance, Computable.const false⟩
  exact ⟨fun _ ↦ False, hcomp.to_re, by simp⟩

/-- A constantly true predicate cannot be `Pi02`-hard. -/
private theorem not_pi02Hard_of_forall
    {T : Type*} [Primcodable T] {p : T → Prop} (hall : ∀ t, p t) :
    ¬ Pi02Hard p := by
  intro hhard
  obtain ⟨f, _, hf⟩ := hhard (fun _ : ℕ ↦ False) pi02_false
  exact (hf 0).mpr (hall (f 0))

/-- A constantly false predicate cannot be `Sigma02`-hard. -/
private theorem not_sigma02Hard_of_forall_not
    {T : Type*} [Primcodable T] {p : T → Prop} (hall : ∀ t, ¬ p t) :
    ¬ Sigma02Hard p := by
  intro hhard
  have htrue : Sigma02 (fun _ : ℕ ↦ True) := by
    unfold Sigma02
    simpa only [not_true] using pi02_false
  obtain ⟨f, _, hf⟩ := hhard (fun _ : ℕ ↦ True) htrue
  exact hall (f 0) ((hf 0).mp trivial)

/-- A non-hyperlinear group makes hyperlinearity `Pi02`-hard on recursively
enumerated presentation codes. -/
theorem hyperlinearEnumeratedCodeProperty_pi02Hard_of_exists
    (h : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) :
    Pi02Hard HyperlinearEnumeratedCodeProperty := by
  obtain ⟨seed, hseed⟩ := HyperlinearMarkov.exists_nonhyperlinear_code_of_exists h
  exact SoficRecognitionSecondLevel.pi02Hard_of_hereditary
    HyperlinearMarkov.HyperlinearProperty
    (fun f hf hK ↦ isHyperlinear_of_injective f hf hK)
    (isHyperlinear_of_finite PUnit) seed hseed

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
    ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G := by
  by_contra hnone
  push Not at hnone
  exact (not_pi02Hard_of_forall
    (fun q ↦ hnone (EnumeratedPresentationCodes.Carrier q) inferInstance)) h

/-- Second-level hardness of non-hyperlinearity likewise forces a
counterexample: without one its target predicate is constantly false. -/
theorem exists_not_isHyperlinear_of_nonhyperlinearEnumeratedCodeProperty_sigma02Hard
    (h : Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q)) :
    ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G := by
  by_contra hnone
  push Not at hnone
  exact (not_sigma02Hard_of_forall_not
    (fun q hq ↦ hq (hnone (EnumeratedPresentationCodes.Carrier q) inferInstance))) h

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
    ComputablePred HyperlinearEnumeratedCodeProperty := by
  letI : DecidablePred HyperlinearEnumeratedCodeProperty := fun q ↦
    isTrue (h (EnumeratedPresentationCodes.Carrier q) inferInstance)
  exact ⟨inferInstance, Computable.const true⟩

/-- In the universal regime, the negative predicate is computably empty. -/
theorem nonhyperlinearEnumeratedCodeProperty_computable_of_universal
    (h : ∀ (G : Type) (_ : Group G), IsHyperlinear G) :
    ComputablePred (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) := by
  letI : DecidablePred (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) := fun q ↦
    isFalse (fun hn ↦ hn (h (EnumeratedPresentationCodes.Carrier q) inferInstance))
  exact ⟨inferInstance, Computable.const false⟩

/-- The two exhaustive recognition regimes.  This theorem is unconditional:
which branch holds is precisely the open non-hyperlinear-group problem. -/
theorem hyperlinear_recognition_phase_dichotomy :
    ((∀ (G : Type) (_ : Group G), IsHyperlinear G) ∧
      ComputablePred HyperlinearEnumeratedCodeProperty ∧
      REPred (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q)) ∨
    ((∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ∧
      Pi02Hard HyperlinearEnumeratedCodeProperty ∧
      Sigma02Hard (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q)) := by
  classical
  by_cases hcounter : ∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G
  · exact Or.inr ⟨hcounter,
      hyperlinearEnumeratedCodeProperty_pi02Hard_of_exists hcounter,
      nonhyperlinearEnumeratedCodeProperty_sigma02Hard_of_exists hcounter⟩
  · push Not at hcounter
    exact Or.inl ⟨hcounter,
      hyperlinearEnumeratedCodeProperty_computable_of_universal hcounter,
      (nonhyperlinearEnumeratedCodeProperty_computable_of_universal hcounter).to_re⟩

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
      Pi02Complete HyperlinearEnumeratedCodeProperty := by
  constructor
  · exact hyperlinearEnumeratedCodeProperty_pi02Complete_of_exists hupper
  · intro h
    exact exists_not_isHyperlinear_of_hyperlinearEnumeratedCodeProperty_pi02Hard h.2

/-- The same upper bound gives the complementary `Sigma02` classification. -/
theorem exists_not_isHyperlinear_iff_nonhyperlinearEnumeratedCodeProperty_sigma02Complete
    (hupper : Pi02 HyperlinearEnumeratedCodeProperty) :
    (∃ (G : Type) (_ : Group G), ¬ IsHyperlinear G) ↔
      Sigma02Complete (fun q ↦ ¬ HyperlinearEnumeratedCodeProperty q) := by
  constructor
  · intro h
    exact pi02Complete_compl
      (hyperlinearEnumeratedCodeProperty_pi02Complete_of_exists hupper h)
  · intro h
    exact
      exists_not_isHyperlinear_of_nonhyperlinearEnumeratedCodeProperty_sigma02Hard h.2

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
