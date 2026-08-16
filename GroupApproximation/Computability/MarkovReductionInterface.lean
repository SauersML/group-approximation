import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.OperatorMFPositiveControls
import Mathlib.Computability.RE

/-!
# The reduction interface, stated before any particular coding

`Computability.MarkovMFConsequences` draws the manuscript's undecidability
consequence *at the recursive coding of finite presentations*, which is what
Corollary~"undecidability" prints: the corollary says "in the recursive coding
of finite presentations fixed above", and the paragraph after it explains why
an arbitrary semantics would not do.  Drawing the consequence there means that
file has to see the coding, and the coding in turn has to see the vocabulary
the reduction is phrased in.

So the vocabulary lives here, upstream of both: presentation properties, the
Markov witness, the semantics of a coding, the recognition predicate, the
`AdianRabinReduction` package, and the two pullback lemmas that do the work.
Nothing in this file mentions a specific coding, and nothing in it postulates a
reduction; it is the interface, and `Computability.PresentationCodes` is the
implementation.

The split is only about import order.  Every declaration keeps the namespace it
had, `GroupApproximation.MarkovMFConsequences`, because that is where the rest
of the development, the manuscript's margin badges, and the exported endpoint
surface all refer to it.
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

end MarkovMFConsequences
end GroupApproximation
