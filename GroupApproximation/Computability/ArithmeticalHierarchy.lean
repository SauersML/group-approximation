import Mathlib.Computability.RE

/-!
# The first two arithmetical levels for repository predicates

Mathlib supplies recursively enumerable predicates but no named `Σ⁰₂` and
`Π⁰₂` wrappers.  This file uses the normal form needed by the MF paper:
a predicate is `Π⁰₂` when it is a universal quantification of a uniformly
recursively enumerable relation.  Since an RE relation is itself an
existential quantification of a computable matrix, this is exactly the usual
`∀∃` definition.  `Σ⁰₂` is defined by complementation.
-/

namespace GroupApproximation
namespace ArithmeticalHierarchy

variable {A : Type*} [Primcodable A]

/-- The first existential level: recursively enumerable predicates. -/
def Sigma01 (p : A → Prop) : Prop := REPred p

/-- The first universal level: predicates with recursively enumerable
complement. -/
def Pi01 (p : A → Prop) : Prop := REPred fun a ↦ ¬ p a

/-- A predicate is `Π⁰₂` if it is uniformly a universal family of RE
predicates.  The witness relation takes the original input and the universal
scale parameter. -/
def Pi02 (p : A → Prop) : Prop :=
  ∃ q : A × ℕ → Prop, REPred q ∧ ∀ a, p a ↔ ∀ n, q (a, n)

/-- The second existential level, defined by complementing `Pi02`. -/
def Sigma02 (p : A → Prop) : Prop := Pi02 fun a ↦ ¬ p a

theorem pi02_of_re_family {p : A → Prop} {q : A × ℕ → Prop}
    (hq : REPred q) (h : ∀ a, p a ↔ ∀ n, q (a, n)) : Pi02 p :=
  ⟨q, hq, h⟩

theorem pi02_congr {p r : A → Prop} (h : ∀ a, p a ↔ r a) :
    Pi02 p ↔ Pi02 r := by
  constructor
  · rintro ⟨q, hq, hp⟩
    exact ⟨q, hq, fun a ↦ (h a).symm.trans (hp a)⟩
  · rintro ⟨q, hq, hr⟩
    exact ⟨q, hq, fun a ↦ (h a).trans (hr a)⟩

theorem sigma02_congr {p r : A → Prop} (h : ∀ a, p a ↔ r a) :
    Sigma02 p ↔ Sigma02 r := by
  apply pi02_congr
  intro a
  exact not_congr (h a)

theorem sigma01_congr {p r : A → Prop} (h : ∀ a, p a ↔ r a) :
    Sigma01 p ↔ Sigma01 r := by
  exact ⟨fun hp ↦ hp.of_eq h, fun hr ↦ hr.of_eq fun a ↦ (h a).symm⟩

theorem pi01_congr {p r : A → Prop} (h : ∀ a, p a ↔ r a) :
    Pi01 p ↔ Pi01 r := by
  exact ⟨fun hp ↦ hp.of_eq fun a ↦ not_congr (h a),
    fun hr ↦ hr.of_eq fun a ↦ not_congr (h a).symm⟩

/-- Complement duality at the second level. -/
theorem sigma02_compl_iff (p : A → Prop) :
    Sigma02 (fun a ↦ ¬ p a) ↔ Pi02 p := by
  unfold Sigma02
  apply pi02_congr
  intro a
  tauto

/-- A `Π⁰₂` upper bound together with non-enumerability of the negative
side yields both strict first-level separations used in the MF paper. -/
theorem strict_first_level_pair {p : A → Prop}
    (hp : Pi02 p) (hneg : ¬ REPred fun a ↦ ¬ p a) :
    (Pi02 p ∧ ¬ Pi01 p) ∧
      (Sigma02 (fun a ↦ ¬ p a) ∧
        ¬ Sigma01 (fun a ↦ ¬ p a)) := by
  refine ⟨⟨hp, hneg⟩, ⟨(sigma02_compl_iff p).2 hp, ?_⟩⟩
  simpa only [Sigma01] using hneg

end ArithmeticalHierarchy
end GroupApproximation
