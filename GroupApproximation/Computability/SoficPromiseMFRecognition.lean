import GroupApproximation.Computability.EnumeratedFixedMarkedQueryCompleteness
import GroupApproximation.Computability.SoficPromiseTwoType

/-!
# Second-level MF recognition under a sofic promise

The recursive switch compiler only produces sofic groups.  On that promised
range, Operator-MF is exactly infinitude of a program domain and non-Operator-MF
is exactly finiteness.  This file separates the generic promised-reduction
bookkeeping from that semantic input and packages both the restricted-family
completeness statements and the corresponding global promise-hardness.
-/

namespace GroupApproximation
namespace SoficPromiseMFRecognition

open Nat.Partrec
open ArithmeticalHierarchy
open SecondLevelIndexSets
open EnumeratedFixedMarkedQueryCompleteness

noncomputable section

/-! ## Generic promised many-one reductions -/

/-- A computable many-one reduction whose outputs all satisfy `promise`. -/
def ManyOneReducibleUnder
    {Source Target : Type*} [Primcodable Source] [Primcodable Target]
    (promise : Target → Prop) (p : Source → Prop) (q : Target → Prop) : Prop :=
  ∃ f : Source → Target, Computable f ∧
    (∀ x, promise (f x)) ∧ ∀ x, p x ↔ q (f x)

/-- Promised `Π⁰₂`-hardness on a specified effective source carrier. -/
def Pi02HardOnUnder (Source : Type*) [Primcodable Source]
    {Target : Type*} [Primcodable Target]
    (promise q : Target → Prop) : Prop :=
  ∀ p : Source → Prop, Pi02 p → ManyOneReducibleUnder promise p q

/-- Promised `Σ⁰₂`-hardness on a specified effective source carrier. -/
def Sigma02HardOnUnder (Source : Type*) [Primcodable Source]
    {Target : Type*} [Primcodable Target]
    (promise q : Target → Prop) : Prop :=
  ∀ p : Source → Prop, Sigma02 p → ManyOneReducibleUnder promise p q

/-- Standard numerical-source `Π⁰₂`-hardness under a promise. -/
def Pi02HardUnder {Target : Type*} [Primcodable Target]
    (promise q : Target → Prop) : Prop :=
  Pi02HardOnUnder ℕ promise q

/-- Standard numerical-source `Σ⁰₂`-hardness under a promise. -/
def Sigma02HardUnder {Target : Type*} [Primcodable Target]
    (promise q : Target → Prop) : Prop :=
  Sigma02HardOnUnder ℕ promise q

/-- Forgetting the promise leaves an ordinary many-one reduction. -/
theorem ManyOneReducibleUnder.toManyOneReducible
    {Source Target : Type*} [Primcodable Source] [Primcodable Target]
    {promise : Target → Prop} {p : Source → Prop} {q : Target → Prop}
    (h : ManyOneReducibleUnder promise p q) : p ≤₀ q := by
  obtain ⟨f, hf, _, hcorrect⟩ := h
  exact ⟨f, hf, hcorrect⟩

/-- The same promised reduction reduces the complementary predicates. -/
theorem manyOneReducibleUnder_compl
    {Source Target : Type*} [Primcodable Source] [Primcodable Target]
    {promise : Target → Prop} {p : Source → Prop} {q : Target → Prop}
    (h : ManyOneReducibleUnder promise p q) :
    ManyOneReducibleUnder promise (fun x ↦ ¬ p x) (fun y ↦ ¬ q y) := by
  obtain ⟨f, hf, hpromise, hcorrect⟩ := h
  exact ⟨f, hf, hpromise, fun x ↦ not_congr (hcorrect x)⟩

/-- Promised hardness implies ordinary hardness after dropping the promise. -/
theorem pi02HardOn_of_pi02HardOnUnder
    {Source Target : Type*} [Primcodable Source] [Primcodable Target]
    {promise q : Target → Prop}
    (h : Pi02HardOnUnder Source promise q) : Pi02HardOn Source q := by
  intro p hp
  exact (h p hp).toManyOneReducible

/-- Promised hardness implies ordinary hardness after dropping the promise. -/
theorem sigma02HardOn_of_sigma02HardOnUnder
    {Source Target : Type*} [Primcodable Source] [Primcodable Target]
    {promise q : Target → Prop}
    (h : Sigma02HardOnUnder Source promise q) : Sigma02HardOn Source q := by
  intro p hp
  exact (h p hp).toManyOneReducible

/-- Ordinary hardness transports through a computable compiler whose complete
range satisfies the promise. -/
theorem pi02HardUnder_of_compiler
    {Intermediate Target : Type*}
    [Primcodable Intermediate] [Primcodable Target]
    {r : Intermediate → Prop} {promise q : Target → Prop}
    (hr : Pi02Hard r) (compile : Intermediate → Target)
    (hcompile : Computable compile) (hpromise : ∀ x, promise (compile x))
    (hcorrect : ∀ x, r x ↔ q (compile x)) :
    Pi02HardUnder promise q := by
  intro p hp
  obtain ⟨f, hf, hfcorrect⟩ := hr p hp
  refine ⟨fun n ↦ compile (f n), hcompile.comp hf, ?_, ?_⟩
  · exact fun n ↦ hpromise (f n)
  · exact fun n ↦ (hfcorrect n).trans (hcorrect (f n))

/-- `Σ⁰₂` version of `pi02HardUnder_of_compiler`. -/
theorem sigma02HardUnder_of_compiler
    {Intermediate Target : Type*}
    [Primcodable Intermediate] [Primcodable Target]
    {r : Intermediate → Prop} {promise q : Target → Prop}
    (hr : Sigma02Hard r) (compile : Intermediate → Target)
    (hcompile : Computable compile) (hpromise : ∀ x, promise (compile x))
    (hcorrect : ∀ x, r x ↔ q (compile x)) :
    Sigma02HardUnder promise q := by
  intro p hp
  obtain ⟨f, hf, hfcorrect⟩ := hr p hp
  refine ⟨fun n ↦ compile (f n), hcompile.comp hf, ?_, ?_⟩
  · exact fun n ↦ hpromise (f n)
  · exact fun n ↦ (hfcorrect n).trans (hcorrect (f n))

/-! ## The two-valued sofic switch family -/

/-- The standard recursive-presentation compiler used by the sofic promise. -/
abbrev compileSoficSwitch : Code → Code :=
  RecursiveSwitchPresentation.switchEnumeratorCode

/-- The semantic promise on standard enumerated presentation codes. -/
def SoficCode (c : Code) : Prop :=
  IsSofic (EnumeratedPresentationCodes.Carrier c)

/-- Operator-MF restricted to the computable sofic switch family. -/
def SoficSwitchMF (c : Code) : Prop :=
  OperatorMFCode (compileSoficSwitch c)

/-- Non-Operator-MF restricted to the same computable sofic switch family. -/
def SoficSwitchNonMF (c : Code) : Prop :=
  NonOperatorMFCode (compileSoficSwitch c)

/-- Every code emitted by the switch compiler satisfies the sofic promise. -/
theorem compileSoficSwitch_isSofic (c : Code) :
    SoficCode (compileSoficSwitch c) :=
  SoficPromiseTwoType.compiled_isSofic c

/-- Exact `INF` truth table for restricted Operator-MF recognition. -/
theorem soficSwitchMF_iff_infiniteDomain (c : Code) :
    SoficSwitchMF c ↔ InfiniteDomain c :=
  compiled_operatorMF_iff_infiniteDomain c

/-- Exact `FIN` truth table for restricted non-Operator-MF recognition. -/
theorem soficSwitchNonMF_iff_finiteDomain (c : Code) :
    SoficSwitchNonMF c ↔ FiniteDomain c :=
  compiled_nonOperatorMF_iff_finiteDomain c

/-- Actual Operator-MF recognition is `Π⁰₂`-complete on this computable
family of sofic groups. -/
theorem soficSwitchMF_pi02Complete : Pi02Complete SoficSwitchMF := by
  constructor
  · exact (pi02_congr soficSwitchMF_iff_infiniteDomain).2
      infiniteDomain_pi02
  · intro p hp
    obtain ⟨f, hf, hcorrect⟩ := infiniteDomain_pi02Hard p hp
    exact ⟨f, hf, fun n ↦
      (hcorrect n).trans (soficSwitchMF_iff_infiniteDomain (f n)).symm⟩

/-- Actual non-Operator-MF recognition is `Σ⁰₂`-complete on the same
computable family of sofic groups. -/
theorem soficSwitchNonMF_sigma02Complete :
    Sigma02Complete SoficSwitchNonMF := by
  constructor
  · exact (sigma02_congr soficSwitchNonMF_iff_finiteDomain).2
      finiteDomain_sigma02
  · intro p hp
    obtain ⟨f, hf, hcorrect⟩ := finiteDomain_sigma02Hard p hp
    exact ⟨f, hf, fun n ↦
      (hcorrect n).trans (soficSwitchNonMF_iff_finiteDomain (f n)).symm⟩

/-! ## Global hardness witnessed entirely inside the sofic promise -/

/-- Operator-MF recognition on arbitrary standard presentation codes remains
`Π⁰₂`-hard even when every output of every reduction is required to be
sofic. -/
theorem operatorMFCode_pi02HardUnderSofic :
    Pi02HardUnder SoficCode OperatorMFCode :=
  pi02HardUnder_of_compiler infiniteDomain_pi02Hard compileSoficSwitch
    RecursiveSwitchPresentation.computable_switchEnumeratorCode
    compileSoficSwitch_isSofic
    fun c ↦ (compiled_operatorMF_iff_infiniteDomain c).symm

/-- Non-Operator-MF recognition remains `Σ⁰₂`-hard under the same
sofic promise. -/
theorem nonOperatorMFCode_sigma02HardUnderSofic :
    Sigma02HardUnder SoficCode NonOperatorMFCode :=
  sigma02HardUnder_of_compiler finiteDomain_sigma02Hard compileSoficSwitch
    RecursiveSwitchPresentation.computable_switchEnumeratorCode
    compileSoficSwitch_isSofic
    fun c ↦ (compiled_nonOperatorMF_iff_finiteDomain c).symm

/-- The closed promise-classification endpoint. -/
theorem sofic_promise_recognition_package :
    Pi02Complete SoficSwitchMF ∧
      Sigma02Complete SoficSwitchNonMF ∧
      Pi02HardUnder SoficCode OperatorMFCode ∧
      Sigma02HardUnder SoficCode NonOperatorMFCode :=
  ⟨soficSwitchMF_pi02Complete, soficSwitchNonMF_sigma02Complete,
    operatorMFCode_pi02HardUnderSofic,
    nonOperatorMFCode_sigma02HardUnderSofic⟩

end

end SoficPromiseMFRecognition
end GroupApproximation
