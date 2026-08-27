import GroupApproximation.Computability.MarkovMFConsequences

/-!
# Conditional recognition consequences for group C-star algebras

Mathlib currently has no general reduced or maximal group C-star-algebra API.
Accordingly, this file does not manufacture one.  Instead it isolates the
computability argument from the operator-algebra semantics: a caller supplies
five predicates on finite-presentation codes, together with explicit
Adian--Rabin reductions proving their behavior.

The auxiliary `SubgroupMarkovData` structure records the usual mathematical
route to the Markov witnesses.  It includes a positive presentation, a
forbidden presentation, subgroup heredity, and the assertion that the
forbidden presentation itself has the negative property.  Thus its derived
`forbidden_excludes` theorem is the actual forbidden-subgroup condition, not
merely a positive/negative pair.

No existence theorem for an Adian--Rabin transformation, no construction of a
group C-star algebra, and no operator-algebra inheritance result is postulated
here.  Those inputs must be supplied as data by a later formalization.
-/

namespace GroupApproximation
namespace CStarRecognitionConsequences

open MarkovMFConsequences

universe u v

/-- The five group-C-star recognition predicates discussed in the manuscript.

The fields are deliberately propositions on presentation codes.  In a future
group-C-star API they can be instantiated by the corresponding semantic
definitions without changing any computability proof below. -/
structure GroupCStarRecognitionPredicates (Code : Type u) where
  /-- The reduced group C-star algebra is MF. -/
  reducedMF : PresentationProperty Code
  /-- The maximal group C-star algebra is MF. -/
  maximalMF : PresentationProperty Code
  /-- The maximal group C-star algebra is finite. -/
  maximalFinite : PresentationProperty Code
  /-- The maximal group C-star algebra is stably finite. -/
  maximalStablyFinite : PresentationProperty Code
  /-- The maximal group C-star algebra is directly finite. -/
  maximalDirectlyFinite : PresentationProperty Code

/-- An abstract subgroup-embedding relation on presentation codes.

Keeping this relation explicit avoids pretending that the repository already
has a construction sending every finite presentation to all of its group
C-star algebras. -/
abbrev SubgroupEmbeddingRelation (Code : Type u) := Code → Code → Prop

/-- Proof data showing that a presentation property has the standard
subgroup-hereditary Markov witness.

`forbiddenCode` is stronger than a mere negative example: subgroup heredity
implies that it cannot embed in any code satisfying `property`. -/
structure SubgroupMarkovData {Code : Type u}
    (embedding : SubgroupEmbeddingRelation Code)
    (property : PresentationProperty Code) where
  positiveCode : Code
  positive : property positiveCode
  forbiddenCode : Code
  forbiddenNegative : ¬property forbiddenCode
  subgroupHereditary : ∀ {small large},
    embedding small large → property large → property small

namespace SubgroupMarkovData

/-- The forbidden presentation cannot embed in any presentation having the
property. -/
theorem forbidden_excludes {Code : Type u}
    {embedding : SubgroupEmbeddingRelation Code}
    {property : PresentationProperty Code}
    (data : SubgroupMarkovData embedding property) {target : Code}
    (hembeds : embedding data.forbiddenCode target) :
    ¬property target := by
  intro htarget
  exact data.forbiddenNegative (data.subgroupHereditary hembeds htarget)

/-- Forgetting subgroup heredity leaves precisely the witness metadata used
by an explicit Adian--Rabin reduction. -/
def toMarkovWitness {Code : Type u}
    {embedding : SubgroupEmbeddingRelation Code}
    {property : PresentationProperty Code}
    (data : SubgroupMarkovData embedding property) :
    MarkovWitness property where
  positiveCode := data.positiveCode
  positive := data.positive
  negativeCode := data.forbiddenCode
  negative := data.forbiddenNegative

/-- Attach an explicit computable transformation and correctness proof to
subgroup-Markov data.  This is the constructor a formal Adian--Rabin
implementation can use; the transformation is still an explicit argument. -/
def toAdianRabinReduction
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    {embedding : SubgroupEmbeddingRelation Code}
    {property : PresentationProperty Code}
    (data : SubgroupMarkovData embedding property)
    (transform : Source → Code) (transformComputable : Computable transform)
    (correct : ∀ source, property (transform source) ↔ sourceProperty source) :
    AdianRabinReduction sourceProperty property where
  markov := data.toMarkovWitness
  transform := transform
  transform_computable := transformComputable
  correct := correct

end SubgroupMarkovData

/-- Subgroup-heredity and Markov-witness data for all five recognition
properties.  This is an honest interface for the operator-algebraic input:
constructing an inhabitant requires proving every inheritance statement and
supplying the relevant forbidden examples. -/
structure GroupCStarSubgroupMarkovData {Code : Type u}
    (embedding : SubgroupEmbeddingRelation Code)
    (predicates : GroupCStarRecognitionPredicates Code) where
  reducedMF : SubgroupMarkovData embedding predicates.reducedMF
  maximalMF : SubgroupMarkovData embedding predicates.maximalMF
  maximalFinite : SubgroupMarkovData embedding predicates.maximalFinite
  maximalStablyFinite :
    SubgroupMarkovData embedding predicates.maximalStablyFinite
  maximalDirectlyFinite :
    SubgroupMarkovData embedding predicates.maximalDirectlyFinite

/-- Explicit Adian--Rabin reductions for all five group-C-star properties.
The source predicate is shared only for convenience; no inhabitant of this
structure is asserted in this file. -/
structure GroupCStarAdianRabinReductions
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    (sourceProperty : Source → Prop)
    (predicates : GroupCStarRecognitionPredicates Code) where
  reducedMF : AdianRabinReduction sourceProperty predicates.reducedMF
  maximalMF : AdianRabinReduction sourceProperty predicates.maximalMF
  maximalFinite :
    AdianRabinReduction sourceProperty predicates.maximalFinite
  maximalStablyFinite :
    AdianRabinReduction sourceProperty predicates.maximalStablyFinite
  maximalDirectlyFinite :
    AdianRabinReduction sourceProperty predicates.maximalDirectlyFinite

/-! ## Undecidability consequences -/

/-- Reduced-group-C-star MF recognition is undecidable when supplied with an
explicit reduction from a noncomputable source predicate. -/
theorem reducedCStarMF_recognition_undecidable
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction : AdianRabinReduction sourceProperty predicates.reducedMF)
    (sourceUndecidable : ¬ComputablePred sourceProperty) :
    ¬ComputablePred predicates.reducedMF :=
  recognition_undecidable reduction sourceUndecidable

/-- Maximal-group-C-star MF recognition is undecidable under the analogous
explicit reduction. -/
theorem maximalCStarMF_recognition_undecidable
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction : AdianRabinReduction sourceProperty predicates.maximalMF)
    (sourceUndecidable : ¬ComputablePred sourceProperty) :
    ¬ComputablePred predicates.maximalMF :=
  recognition_undecidable reduction sourceUndecidable

/-- Recognition of finiteness of the maximal group C-star algebra is
undecidable under an explicit reduction. -/
theorem maximalCStar_finite_recognition_undecidable
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction :
      AdianRabinReduction sourceProperty predicates.maximalFinite)
    (sourceUndecidable : ¬ComputablePred sourceProperty) :
    ¬ComputablePred predicates.maximalFinite :=
  recognition_undecidable reduction sourceUndecidable

/-- Recognition of stable finiteness of the maximal group C-star algebra is
undecidable under an explicit reduction. -/
theorem maximalCStar_stablyFinite_recognition_undecidable
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction :
      AdianRabinReduction sourceProperty predicates.maximalStablyFinite)
    (sourceUndecidable : ¬ComputablePred sourceProperty) :
    ¬ComputablePred predicates.maximalStablyFinite :=
  recognition_undecidable reduction sourceUndecidable

/-- Recognition of direct finiteness of the maximal group C-star algebra is
undecidable under an explicit reduction. -/
theorem maximalCStar_directlyFinite_recognition_undecidable
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction :
      AdianRabinReduction sourceProperty predicates.maximalDirectlyFinite)
    (sourceUndecidable : ¬ComputablePred sourceProperty) :
    ¬ComputablePred predicates.maximalDirectlyFinite :=
  recognition_undecidable reduction sourceUndecidable

/-! ## Failure of recursive enumerability on the negative side -/

/-- Negative reduced-group-C-star MF instances are not recursively
enumerable when the source negative side is not recursively enumerable. -/
theorem reducedCStarMF_negative_side_not_re
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction : AdianRabinReduction sourceProperty predicates.reducedMF)
    (sourceNegativeNotRE : ¬REPred (fun source ↦ ¬sourceProperty source)) :
    ¬REPred (fun code ↦ ¬predicates.reducedMF code) :=
  negative_side_not_re reduction sourceNegativeNotRE

/-- Negative maximal-group-C-star MF instances are not recursively
enumerable under the corresponding explicit reduction. -/
theorem maximalCStarMF_negative_side_not_re
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction : AdianRabinReduction sourceProperty predicates.maximalMF)
    (sourceNegativeNotRE : ¬REPred (fun source ↦ ¬sourceProperty source)) :
    ¬REPred (fun code ↦ ¬predicates.maximalMF code) :=
  negative_side_not_re reduction sourceNegativeNotRE

/-- Negative maximal-C-star finiteness instances are not recursively
enumerable under the corresponding explicit reduction. -/
theorem maximalCStar_finite_negative_side_not_re
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction :
      AdianRabinReduction sourceProperty predicates.maximalFinite)
    (sourceNegativeNotRE : ¬REPred (fun source ↦ ¬sourceProperty source)) :
    ¬REPred (fun code ↦ ¬predicates.maximalFinite code) :=
  negative_side_not_re reduction sourceNegativeNotRE

/-- Negative maximal-C-star stable-finiteness instances are not recursively
enumerable under the corresponding explicit reduction. -/
theorem maximalCStar_stablyFinite_negative_side_not_re
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction :
      AdianRabinReduction sourceProperty predicates.maximalStablyFinite)
    (sourceNegativeNotRE : ¬REPred (fun source ↦ ¬sourceProperty source)) :
    ¬REPred (fun code ↦ ¬predicates.maximalStablyFinite code) :=
  negative_side_not_re reduction sourceNegativeNotRE

/-- Negative maximal-C-star direct-finiteness instances are not recursively
enumerable under the corresponding explicit reduction. -/
theorem maximalCStar_directlyFinite_negative_side_not_re
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reduction :
      AdianRabinReduction sourceProperty predicates.maximalDirectlyFinite)
    (sourceNegativeNotRE : ¬REPred (fun source ↦ ¬sourceProperty source)) :
    ¬REPred (fun code ↦ ¬predicates.maximalDirectlyFinite code) :=
  negative_side_not_re reduction sourceNegativeNotRE

/-! ## Batched forms -/

/-- All five undecidability conclusions, packaged for a common source
predicate and an explicit bundle of reductions. -/
theorem all_groupCStar_recognition_undecidable
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reductions : GroupCStarAdianRabinReductions sourceProperty predicates)
    (sourceUndecidable : ¬ComputablePred sourceProperty) :
    (¬ComputablePred predicates.reducedMF) ∧
      (¬ComputablePred predicates.maximalMF) ∧
      (¬ComputablePred predicates.maximalFinite) ∧
      (¬ComputablePred predicates.maximalStablyFinite) ∧
      (¬ComputablePred predicates.maximalDirectlyFinite) := by
  exact ⟨recognition_undecidable reductions.reducedMF sourceUndecidable,
    recognition_undecidable reductions.maximalMF sourceUndecidable,
    recognition_undecidable reductions.maximalFinite sourceUndecidable,
    recognition_undecidable reductions.maximalStablyFinite sourceUndecidable,
    recognition_undecidable reductions.maximalDirectlyFinite sourceUndecidable⟩

/-- All five negative-side non-r.e. conclusions, packaged for a common
source predicate and explicit reductions. -/
theorem all_groupCStar_negative_sides_not_re
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (predicates : GroupCStarRecognitionPredicates Code)
    (reductions : GroupCStarAdianRabinReductions sourceProperty predicates)
    (sourceNegativeNotRE : ¬REPred (fun source ↦ ¬sourceProperty source)) :
    (¬REPred (fun code ↦ ¬predicates.reducedMF code)) ∧
      (¬REPred (fun code ↦ ¬predicates.maximalMF code)) ∧
      (¬REPred (fun code ↦ ¬predicates.maximalFinite code)) ∧
      (¬REPred (fun code ↦ ¬predicates.maximalStablyFinite code)) ∧
      (¬REPred (fun code ↦ ¬predicates.maximalDirectlyFinite code)) := by
  exact ⟨negative_side_not_re reductions.reducedMF sourceNegativeNotRE,
    negative_side_not_re reductions.maximalMF sourceNegativeNotRE,
    negative_side_not_re reductions.maximalFinite sourceNegativeNotRE,
    negative_side_not_re reductions.maximalStablyFinite sourceNegativeNotRE,
    negative_side_not_re reductions.maximalDirectlyFinite sourceNegativeNotRE⟩

end CStarRecognitionConsequences
end GroupApproximation
