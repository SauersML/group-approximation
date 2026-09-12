import Mathlib.Computability.RE
import Mathlib.Computability.Reduce

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

/-! ## Many-one hardness and completeness

The carrier-parametric `HardOn` definitions are useful when a reduction is
naturally presented on a particular effective source type.  The unqualified
notions use predicates on `ℕ`, the standard domain for arithmetical-hierarchy
completeness.  Targets may live on any `Primcodable` type.
-/

/-- A predicate is `Π⁰₂`-hard on an effective source carrier if every `Π⁰₂`
predicate on that carrier computably many-one reduces to it. -/
def Pi02HardOn (Source : Type*) [Primcodable Source]
    {Target : Type*} [Primcodable Target] (q : Target → Prop) : Prop :=
  ∀ p : Source → Prop, Pi02 p → p ≤₀ q

/-- A predicate is `Σ⁰₂`-hard on an effective source carrier if every `Σ⁰₂`
predicate on that carrier computably many-one reduces to it. -/
def Sigma02HardOn (Source : Type*) [Primcodable Source]
    {Target : Type*} [Primcodable Target] (q : Target → Prop) : Prop :=
  ∀ p : Source → Prop, Sigma02 p → p ≤₀ q

/-- Standard `Π⁰₂` many-one hardness, with numerical source indices. -/
def Pi02Hard {Target : Type*} [Primcodable Target] (q : Target → Prop) : Prop :=
  Pi02HardOn ℕ q

/-- Standard `Σ⁰₂` many-one hardness, with numerical source indices. -/
def Sigma02Hard {Target : Type*} [Primcodable Target] (q : Target → Prop) : Prop :=
  Sigma02HardOn ℕ q

/-- Membership in `Π⁰₂` together with computable many-one hardness. -/
def Pi02Complete {Target : Type*} [Primcodable Target] (q : Target → Prop) : Prop :=
  Pi02 q ∧ Pi02Hard q

/-- Membership in `Σ⁰₂` together with computable many-one hardness. -/
def Sigma02Complete {Target : Type*} [Primcodable Target] (q : Target → Prop) : Prop :=
  Sigma02 q ∧ Sigma02Hard q

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

/-! ## Complement transport -/

/-- A computable many-one reduction also reduces the complementary
predicates, using the same computable transformation. -/
theorem manyOneReducible_compl
    {B : Type*} [Primcodable B] {p : A → Prop} {q : B → Prop}
    (h : p ≤₀ q) : (fun a ↦ ¬ p a) ≤₀ (fun b ↦ ¬ q b) := by
  obtain ⟨f, hf, hcorrect⟩ := h
  exact ⟨f, hf, fun a ↦ not_congr (hcorrect a)⟩

/-- Conversely, a reduction between complements is a reduction between the
original predicates.  Classical logic is used only to remove double
negations in the correctness equivalence. -/
theorem manyOneReducible_of_compl
    {B : Type*} [Primcodable B] {p : A → Prop} {q : B → Prop}
    (h : (fun a ↦ ¬ p a) ≤₀ (fun b ↦ ¬ q b)) : p ≤₀ q := by
  obtain ⟨f, hf, hcorrect⟩ := h
  refine ⟨f, hf, fun a ↦ ?_⟩
  classical
  simpa only [not_not] using not_congr (hcorrect a)

/-- Complementation transports `Π⁰₂` hardness on any fixed effective source
carrier to `Σ⁰₂` hardness. -/
theorem pi02HardOn_compl
    {Source : Type*} [Primcodable Source]
    {Target : Type*} [Primcodable Target] {q : Target → Prop}
    (h : Pi02HardOn Source q) :
    Sigma02HardOn Source (fun b ↦ ¬ q b) := by
  intro p hp
  have hred : (fun a ↦ ¬ p a) ≤₀ q := h (fun a ↦ ¬ p a) hp
  obtain ⟨f, hf, hcorrect⟩ := hred
  refine ⟨f, hf, fun a ↦ ?_⟩
  classical
  simpa only [not_not] using not_congr (hcorrect a)

/-- Complementation transports `Σ⁰₂` hardness on any fixed effective source
carrier to `Π⁰₂` hardness. -/
theorem sigma02HardOn_compl
    {Source : Type*} [Primcodable Source]
    {Target : Type*} [Primcodable Target] {q : Target → Prop}
    (h : Sigma02HardOn Source q) :
    Pi02HardOn Source (fun b ↦ ¬ q b) := by
  intro p hp
  have hpcompl : Sigma02 (fun a ↦ ¬ p a) :=
    (sigma02_compl_iff p).2 hp
  have hred : (fun a ↦ ¬ p a) ≤₀ q := h (fun a ↦ ¬ p a) hpcompl
  obtain ⟨f, hf, hcorrect⟩ := hred
  refine ⟨f, hf, fun a ↦ ?_⟩
  classical
  simpa only [not_not] using not_congr (hcorrect a)

/-- Numerical-index form of `pi02HardOn_compl`. -/
theorem pi02Hard_compl
    {Target : Type*} [Primcodable Target] {q : Target → Prop}
    (h : Pi02Hard q) : Sigma02Hard (fun b ↦ ¬ q b) :=
  pi02HardOn_compl h

/-- Numerical-index form of `sigma02HardOn_compl`. -/
theorem sigma02Hard_compl
    {Target : Type*} [Primcodable Target] {q : Target → Prop}
    (h : Sigma02Hard q) : Pi02Hard (fun b ↦ ¬ q b) :=
  sigma02HardOn_compl h

/-- The complement of a `Π⁰₂`-complete predicate is `Σ⁰₂`-complete. -/
theorem pi02Complete_compl
    {Target : Type*} [Primcodable Target] {q : Target → Prop}
    (h : Pi02Complete q) : Sigma02Complete (fun b ↦ ¬ q b) :=
  ⟨(sigma02_compl_iff q).2 h.1, pi02Hard_compl h.2⟩

/-- The complement of a `Σ⁰₂`-complete predicate is `Π⁰₂`-complete. -/
theorem sigma02Complete_compl
    {Target : Type*} [Primcodable Target] {q : Target → Prop}
    (h : Sigma02Complete q) : Pi02Complete (fun b ↦ ¬ q b) :=
  ⟨h.1, sigma02Hard_compl h.2⟩

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
