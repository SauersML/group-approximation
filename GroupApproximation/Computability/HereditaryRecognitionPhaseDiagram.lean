import GroupApproximation.Computability.SoficRecognitionSecondLevel
import GroupApproximation.Meta.AxiomGuard

/-!
# A second-level recognition phase theorem for hereditary group properties

Let `P` pass to subgroups, hold for the trivial group, and have the finite-cover
property that every abstract counterexample yields a finite presentation code
for a counterexample.  Then the following are equivalent:

* some group fails `P`;
* recognising `P` from a recursively enumerated presentation is `Pi02`-hard;
* recognising failure of `P` there is `Sigma02`-hard.

The forward direction is the arbitrary-forbidden-seed event-ray compiler.  The
reverse direction is a general effective obstruction: a constantly true target
cannot be `Pi02`-hard and a constantly false target cannot be `Sigma02`-hard.
This file also packages the two exhaustive recognition regimes and the upgrade
from hardness to completeness once a `Pi02` upper bound is known.
-/

namespace GroupApproximation
namespace HereditaryRecognitionPhaseDiagram

open ArithmeticalHierarchy
open PresentationCodes

/-- A group property evaluated on standard recursively enumerated presentation
codes. -/
abbrev EnumeratedCodeProperty (P : (H : Type) → [Group H] → Prop) :
    EnumeratedPresentationCodes.PresentationCode → Prop :=
  fun q ↦ P (EnumeratedPresentationCodes.Carrier q)

/-- The assertion that every abstract counterexample to `P` can be replaced by
a counterexample carried by a finite presentation code. -/
def HasFiniteCounterexampleCover (P : (H : Type) → [Group H] → Prop) : Prop :=
  (∃ (G : Type) (_ : Group G), ¬ P G) →
    ∃ seed : PresentationCode, ¬ P (Carrier seed)

/-- The empty numerical predicate belongs to `Pi02`. -/
theorem pi02_false : Pi02 (fun _ : ℕ ↦ False) := by
  letI : DecidablePred (fun _ : ℕ × ℕ ↦ False) := fun _ ↦ isFalse id
  have hcomp : ComputablePred (fun _ : ℕ × ℕ ↦ False) :=
    ⟨inferInstance, Computable.const false⟩
  exact ⟨fun _ ↦ False, hcomp.to_re, by simp⟩

/-- A constantly true target predicate cannot be `Pi02`-hard. -/
theorem not_pi02Hard_of_forall
    {T : Type*} [Primcodable T] {p : T → Prop} (hall : ∀ t, p t) :
    ¬ Pi02Hard p := by
  intro hhard
  obtain ⟨f, _, hf⟩ := hhard (fun _ : ℕ ↦ False) pi02_false
  exact (hf 0).mpr (hall (f 0))

/-- A constantly false target predicate cannot be `Sigma02`-hard. -/
theorem not_sigma02Hard_of_forall_not
    {T : Type*} [Primcodable T] {p : T → Prop} (hall : ∀ t, ¬ p t) :
    ¬ Sigma02Hard p := by
  intro hhard
  have htrue : Sigma02 (fun _ : ℕ ↦ True) := by
    unfold Sigma02
    simpa only [not_true] using pi02_false
  obtain ⟨f, _, hf⟩ := hhard (fun _ : ℕ ↦ True) htrue
  exact hall (f 0) ((hf 0).mp trivial)

/-- Hardness of `P` recognition itself produces an abstract counterexample,
with no heredity or cover assumption. -/
theorem exists_failure_of_pi02Hard
    {P : (H : Type) → [Group H] → Prop}
    (h : Pi02Hard (EnumeratedCodeProperty P)) :
    ∃ (G : Type) (_ : Group G), ¬ P G := by
  by_contra hnone
  push Not at hnone
  exact (not_pi02Hard_of_forall
    (fun q ↦ hnone (EnumeratedPresentationCodes.Carrier q) inferInstance)) h

/-- Hardness of failure recognition likewise produces a counterexample. -/
theorem exists_failure_of_sigma02Hard_compl
    {P : (H : Type) → [Group H] → Prop}
    (h : Sigma02Hard (fun q ↦ ¬ EnumeratedCodeProperty P q)) :
    ∃ (G : Type) (_ : Group G), ¬ P G := by
  by_contra hnone
  push Not at hnone
  exact (not_sigma02Hard_of_forall_not
    (fun q hq ↦ hq (hnone (EnumeratedPresentationCodes.Carrier q) inferInstance))) h

/-- A hereditary property with a finite counterexample cover becomes
`Pi02`-hard as soon as any counterexample exists. -/
theorem pi02Hard_of_exists_of_finiteCover
    (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (hcover : HasFiniteCounterexampleCover P)
    (h : ∃ (G : Type) (_ : Group G), ¬ P G) :
    Pi02Hard (EnumeratedCodeProperty P) := by
  obtain ⟨seed, hseed⟩ := hcover h
  exact SoficRecognitionSecondLevel.pi02Hard_of_hereditary
    P hered hone seed hseed

/-- The complementary hardness consequence. -/
theorem sigma02Hard_compl_of_exists_of_finiteCover
    (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (hcover : HasFiniteCounterexampleCover P)
    (h : ∃ (G : Type) (_ : Group G), ¬ P G) :
    Sigma02Hard (fun q ↦ ¬ EnumeratedCodeProperty P q) :=
  pi02Hard_compl (pi02Hard_of_exists_of_finiteCover P hered hone hcover h)

/-- **Generic exact hardness phase transition.** -/
theorem exists_failure_iff_pi02Hard
    (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (hcover : HasFiniteCounterexampleCover P) :
    (∃ (G : Type) (_ : Group G), ¬ P G) ↔
      Pi02Hard (EnumeratedCodeProperty P) :=
  ⟨pi02Hard_of_exists_of_finiteCover P hered hone hcover,
    exists_failure_of_pi02Hard⟩

/-- The complementary generic exact hardness phase transition. -/
theorem exists_failure_iff_sigma02Hard_compl
    (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (hcover : HasFiniteCounterexampleCover P) :
    (∃ (G : Type) (_ : Group G), ¬ P G) ↔
      Sigma02Hard (fun q ↦ ¬ EnumeratedCodeProperty P q) :=
  ⟨sigma02Hard_compl_of_exists_of_finiteCover P hered hone hcover,
    exists_failure_of_sigma02Hard_compl⟩

/-- In the universal regime, recognition is computably constant true. -/
theorem enumeratedCodeProperty_computable_of_universal
    (P : (H : Type) → [Group H] → Prop)
    (h : ∀ (G : Type) (_ : Group G), P G) :
    ComputablePred (EnumeratedCodeProperty P) := by
  letI : DecidablePred (EnumeratedCodeProperty P) := fun q ↦
    isTrue (h (EnumeratedPresentationCodes.Carrier q) inferInstance)
  exact ⟨inferInstance, Computable.const true⟩

/-- In the universal regime, failure recognition is computably empty. -/
theorem enumeratedCodeProperty_compl_computable_of_universal
    (P : (H : Type) → [Group H] → Prop)
    (h : ∀ (G : Type) (_ : Group G), P G) :
    ComputablePred (fun q ↦ ¬ EnumeratedCodeProperty P q) := by
  letI : DecidablePred (fun q ↦ ¬ EnumeratedCodeProperty P q) := fun q ↦
    isFalse (fun hn ↦ hn (h (EnumeratedPresentationCodes.Carrier q) inferInstance))
  exact ⟨inferInstance, Computable.const false⟩

/-- **Generic unconditional recognition phase diagram.** -/
theorem recognition_phase_dichotomy
    (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (hcover : HasFiniteCounterexampleCover P) :
    ((∀ (G : Type) (_ : Group G), P G) ∧
      ComputablePred (EnumeratedCodeProperty P) ∧
      REPred (fun q ↦ ¬ EnumeratedCodeProperty P q)) ∨
    ((∃ (G : Type) (_ : Group G), ¬ P G) ∧
      Pi02Hard (EnumeratedCodeProperty P) ∧
      Sigma02Hard (fun q ↦ ¬ EnumeratedCodeProperty P q)) := by
  classical
  by_cases hcounter : ∃ (G : Type) (_ : Group G), ¬ P G
  · exact Or.inr ⟨hcounter,
      pi02Hard_of_exists_of_finiteCover P hered hone hcover hcounter,
      sigma02Hard_compl_of_exists_of_finiteCover P hered hone hcover hcounter⟩
  · push Not at hcounter
    exact Or.inl ⟨hcounter,
      enumeratedCodeProperty_computable_of_universal P hcounter,
      (enumeratedCodeProperty_compl_computable_of_universal P hcounter).to_re⟩

/-- A `Pi02` upper bound upgrades the generic exact hardness equivalence to an
exact completeness equivalence. -/
theorem exists_failure_iff_pi02Complete
    (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (hcover : HasFiniteCounterexampleCover P)
    (hupper : Pi02 (EnumeratedCodeProperty P)) :
    (∃ (G : Type) (_ : Group G), ¬ P G) ↔
      Pi02Complete (EnumeratedCodeProperty P) := by
  constructor
  · intro h
    exact ⟨hupper, pi02Hard_of_exists_of_finiteCover P hered hone hcover h⟩
  · intro h
    exact exists_failure_of_pi02Hard h.2

/-- The complementary exact completeness equivalence. -/
theorem exists_failure_iff_sigma02Complete_compl
    (P : (H : Type) → [Group H] → Prop)
    (hered : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (hone : P PUnit) (hcover : HasFiniteCounterexampleCover P)
    (hupper : Pi02 (EnumeratedCodeProperty P)) :
    (∃ (G : Type) (_ : Group G), ¬ P G) ↔
      Sigma02Complete (fun q ↦ ¬ EnumeratedCodeProperty P q) := by
  constructor
  · intro h
    exact pi02Complete_compl
      ⟨hupper, pi02Hard_of_exists_of_finiteCover P hered hone hcover h⟩
  · intro h
    exact exists_failure_of_sigma02Hard_compl h.2

end HereditaryRecognitionPhaseDiagram
end GroupApproximation

open GroupApproximation.HereditaryRecognitionPhaseDiagram

#audit_axioms exists_failure_iff_pi02Hard
#audit_axioms exists_failure_iff_sigma02Hard_compl
#audit_axioms recognition_phase_dichotomy
#audit_axioms exists_failure_iff_pi02Complete
#audit_axioms exists_failure_iff_sigma02Complete_compl
