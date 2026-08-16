import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.OperatorMFPositiveControls
import Mathlib.Computability.RE

/-!
# Conditional Markov consequences for MF recognition

This file isolates the computability-theoretic consequence of an
Adian--Rabin construction from the construction itself.  In particular, no
Adian--Rabin theorem is asserted as an axiom.  A user of this file must supply
an explicit computable transformation of presentation codes together with
its correctness equivalence.
-/

namespace GroupApproximation
namespace MarkovMFConsequences

universe u v

/-- A property of finite-presentation codes.  The syntax and semantics of
codes are deliberately parameters: different exact encodings can share the
same reduction theorem. -/
abbrev PresentationProperty (Code : Type u) := Code → Prop

/-- The minimal nontriviality data attached to a Markov property on
presentation codes.  These witnesses are metadata for an Adian--Rabin
construction; by themselves they imply no undecidability theorem. -/
structure MarkovWitness {Code : Type u}
    (property : PresentationProperty Code) where
  positiveCode : Code
  positive : property positiveCode
  negativeCode : Code
  negative : ¬property negativeCode

/-- Semantics for a recursive finite-presentation coding.  This structure
only interprets codes; computability of syntactic operations belongs in a
specific coding implementation. -/
structure FinitePresentationSemantics (Code : Type u) where
  Carrier : Code → Type v
  group : ∀ code, Group (Carrier code)
  finitelyPresented : ∀ code,
    @Group.IsFinitelyPresented (Carrier code) (group code)

/-- The operator-MF recognition predicate associated to presentation-code
semantics. -/
def operatorMFProperty {Code : Type u}
    (semantics : FinitePresentationSemantics Code) :
    PresentationProperty Code :=
  fun code ↦ @IsOperatorMF (semantics.Carrier code) (semantics.group code)

/-- Explicit input expected from an Adian--Rabin construction.  It contains
the computable code transformation, its pointwise correctness theorem, and
the Markov witnesses used in constructing it.  No inhabitant is postulated
in this file. -/
structure AdianRabinReduction
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    (sourceProperty : Source → Prop)
    (targetProperty : PresentationProperty Code) where
  markov : MarkovWitness targetProperty
  transform : Source → Code
  transform_computable : Computable transform
  correct : ∀ source,
    targetProperty (transform source) ↔ sourceProperty source

/-- Computable predicates pull back along computable functions. -/
theorem computablePred_comp
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {property : Code → Prop} (hproperty : ComputablePred property)
    {transform : Source → Code} (htransform : Computable transform) :
    ComputablePred (fun source ↦ property (transform source)) := by
  obtain ⟨decidableProperty, hdecide⟩ := hproperty
  letI : DecidablePred property := decidableProperty
  exact ⟨inferInstance, hdecide.comp htransform⟩

/-- Recursively enumerable predicates pull back along computable functions. -/
theorem rePred_comp
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {property : Code → Prop} (hproperty : REPred property)
    {transform : Source → Code} (htransform : Computable transform) :
    REPred (fun source ↦ property (transform source)) := by
  exact hproperty.comp htransform

/-- An Adian--Rabin reduction from a noncomputable source predicate makes the
target presentation property undecidable. -/
theorem recognition_undecidable
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop} {targetProperty : Code → Prop}
    (reduction : AdianRabinReduction sourceProperty targetProperty)
    (source_undecidable : ¬ComputablePred sourceProperty) :
    ¬ComputablePred targetProperty := by
  intro htarget
  have hpullback := computablePred_comp htarget reduction.transform_computable
  exact source_undecidable <|
    hpullback.of_eq fun source ↦ reduction.correct source

/-- If the negative side of the source problem is not recursively
enumerable, neither is the negative side of the target presentation
property. -/
theorem negative_side_not_re
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop} {targetProperty : Code → Prop}
    (reduction : AdianRabinReduction sourceProperty targetProperty)
    (source_negative_not_re : ¬REPred (fun source ↦ ¬sourceProperty source)) :
    ¬REPred (fun code ↦ ¬targetProperty code) := by
  intro htarget
  have hpullback := rePred_comp htarget reduction.transform_computable
  apply source_negative_not_re
  exact hpullback.of_eq fun source ↦ not_congr (reduction.correct source)

/-- Specialized undecidability statement for operator-MF recognition under
an explicitly supplied presentation semantics and Adian--Rabin reduction. -/
theorem operatorMF_recognition_undecidable :
    ∀ {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
      {sourceProperty : Source → Prop}
      (semantics : FinitePresentationSemantics Code)
      (_reduction : AdianRabinReduction sourceProperty
        (operatorMFProperty semantics))
      (_source_undecidable : ¬ComputablePred sourceProperty),
      ¬ComputablePred (operatorMFProperty semantics) := by
  intro Source Code _ _ sourceProperty semantics reduction source_undecidable
  exact recognition_undecidable reduction source_undecidable

/-- Specialized non-r.e. statement for negative operator-MF instances. -/
theorem operatorMF_negative_side_not_re
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (semantics : FinitePresentationSemantics Code)
    (reduction : AdianRabinReduction sourceProperty
      (operatorMFProperty semantics))
    (source_negative_not_re : ¬REPred (fun source ↦ ¬sourceProperty source)) :
    ¬REPred (fun code ↦ ¬operatorMFProperty semantics code) :=
  negative_side_not_re reduction source_negative_not_re

/-- Closed form of the non-r.e. statement: every binder after the colon, so the
manuscript can cite it as a complete printed proposition.  Its hypotheses --- a
presentation coding, an Adian--Rabin reduction, and a source whose negative side
is not recursively enumerable --- are visible antecedents, not citations. -/
theorem manuscriptOperatorMFNegativeSideNotRE :
    ∀ {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
      {sourceProperty : Source → Prop}
      (semantics : FinitePresentationSemantics Code)
      (_reduction : AdianRabinReduction sourceProperty
        (operatorMFProperty semantics))
      (_source_negative_not_re :
        ¬REPred (fun source ↦ ¬sourceProperty source)),
      ¬REPred (fun code ↦ ¬operatorMFProperty semantics code) := by
  intro Source Code _ _ sourceProperty semantics reduction hnre
  exact operatorMF_negative_side_not_re semantics reduction hnre

/-! The two group-theoretic inputs normally used to build the MF Markov
witness are already unconditional theorems in this repository.  They are
recorded here without claiming that the syntactic Adian--Rabin transformation
has been formalized. -/

/-- Operator-MF is inherited by subgroups. -/
theorem operatorMF_subgroup_hereditary :
    ∀ {G : Type u} [Group G] (_hG : IsOperatorMF G) (H : Subgroup G),
      IsOperatorMF H := by
  intro G _ hG H
  exact hG.subgroup H

/-- There is an unconditional finitely presented non-operator-MF group. -/
theorem exists_finitelyPresented_nonOperatorMF :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬IsOperatorMF G :=
  ChosenNonMFTheorem.exists_finitelyPresented_not_isOperatorMF

end MarkovMFConsequences
end GroupApproximation
