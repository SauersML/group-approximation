import GroupApproximation.Computability.RabinVariantCode
import GroupApproximation.Computability.CoprodCode
import GroupApproximation.Computability.RawTransform
import GroupApproximation.Computability.RawTransformPrimrec
import GroupApproximation.Computability.AdianRabinWordProblem

/-!
# The Adian--Rabin transformation, and its correctness

Everything the variant construction needs is now in coordinates, so the
transformation itself is a composition of two code operations: free-product the
input code with the fixed non-MF code, then run the construction on the result.

`correct` is the reduction's correctness clause, and it is a biconditional with
no hypothesis:

* if the word dies in the group the input code presents, then it dies in the
  free product too, the construction collapses, and the output code presents a
  free group --- which is residually finite, hence operator-MF;
* if it survives, the free product embeds in the output group, so the fixed
  non-MF factor does, and operator-MF would descend to it.

The two clauses are `RabinVariantCode.variantCode_isOperatorMF` and
`RabinVariantCode.isOperatorMF_of_variantCode`; the bridge between the input
code's word problem and the free product's is
`RabinConstructionSource.mk_map_inl_eq_one_iff`, moved across the renumbering by
`PresentedGroupRelabel.mk_relabel_eq_one_iff`.

What is *not* here is `Computable transform`, the fourth field of an
`AdianRabinReduction`.  That is a statement about the syntactic operations, not
about groups, and it is the remaining obligation on this side.
-/

namespace GroupApproximation
namespace AdianRabinVariantTransform

open PresentationCodes PresentationCodeList CoprodCode RabinVariantCode
open PresentedGroupRelabel RabinConstructionSource AdianRabinWordProblem
open MarkovMFConsequences

/-- The fixed forbidden code: the manuscript's finitely presented non-MF group.
It is a constant, so using it costs nothing in computability even though
adequacy produced it by choice. -/
noncomputable abbrev forbidden : PresentationCode := negativeCode

/-- **The transformation.**  Free-product the input with the forbidden group,
then apply the construction to the word. -/
noncomputable def transform (x : PresentationCode × List (ℕ × Bool)) : PresentationCode :=
  variantCode (coprodCode x.1 forbidden) (normWord x.1 x.2)

/-- The relator set of a code, read as a list. -/
theorem relatorSet_eq (c : PresentationCode) :
    relatorSet c = {x | x ∈ relatorListOf c} :=
  coe_relatorFinset c

/-- **The word problem of the input is the word problem of the free product.**
Both directions are `mk_map_inl_eq_one_iff`, moved across the renumbering. -/
theorem coprod_mk_eq_one_iff (c : PresentationCode) (w : List (ℕ × Bool)) :
    PresentedGroup.mk {x | x ∈ relatorListOf (coprodCode c forbidden)}
        (wordOf (coprodCode c forbidden) (normWord c w)) = 1
      ↔ WordProblem c w := by
  rw [wordOf_coprodCode, relSet_coprodCode, mk_relabel_eq_one_iff,
    mk_map_inl_eq_one_iff, WordProblem, relatorSet_eq]

/-- **Correctness of the reduction.**  The output code presents an operator-MF
group exactly when the input word dies in the input group. -/
theorem correct : ∀ x : PresentationCode × List (ℕ × Bool),
    operatorMFProperty semantics (transform x) ↔ WordProblem x.1 x.2 := by
  intro x
  obtain ⟨c, w⟩ := x
  rw [operatorMFProperty_semantics]
  constructor
  · intro hMF
    by_contra hw
    have hne : PresentedGroup.mk {x | x ∈ relatorListOf (coprodCode c forbidden)}
        (wordOf (coprodCode c forbidden) (normWord c w)) ≠ 1 :=
      fun h => hw ((coprod_mk_eq_one_iff c w).1 h)
    have h1 := isOperatorMF_of_variantCode _ _ hne hMF
    have h2 : IsOperatorMF
        (CoprodPresented {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf forbidden}) :=
      h1.comap (coprodCodeEquiv c forbidden).symm.toMonoidHom
        (coprodCodeEquiv c forbidden).symm.injective
    have h3 : IsOperatorMF (PresentedGroup {x | x ∈ relatorListOf forbidden}) :=
      h2.comap (inclRight _ _) (inclRight_injective _ _)
    exact not_isOperatorMF_negativeCode
      (h3.comap (carrierEquivList forbidden).toMonoidHom
        (carrierEquivList forbidden).injective)
  · intro hw
    exact variantCode_isOperatorMF _ _ ((coprod_mk_eq_one_iff c w).2 hw)

/-! ## The same transformation, as list surgery

`transform` is `noncomputable`, and irreparably so in that form: it builds its
output through `codeOfList`, which encodes free-group elements, and `FreeGroup`
over the dependent alphabet `Fin (genCount c)` carries no `Primcodable`
instance.  `RawTransform.rawTransform` performs the same construction by pure
list surgery, and `RawTransform.relSet_rawTransform` says the two codes name the
same relators --- so they present the same group, and correctness transfers. -/

/-- The transformation, as list surgery, at the fixed forbidden code. -/
noncomputable def rawTransform (x : PresentationCode × List (ℕ × Bool)) : PresentationCode :=
  RawTransform.rawTransform x.1 forbidden x.2

/-- **Correctness, for the list-surgery form.**  The statement `transform`
proves, about the code a program can actually build. -/
theorem correct_raw : ∀ x : PresentationCode × List (ℕ × Bool),
    operatorMFProperty semantics (rawTransform x) ↔ WordProblem x.1 x.2 := by
  intro x
  rw [operatorMFProperty_semantics]
  constructor
  · intro h
    refine (correct x).1 ((operatorMFProperty_semantics (transform x)).2 ?_)
    exact h.comap (RawTransform.rawCarrierEquiv x.1 forbidden x.2).symm.toMonoidHom
      (RawTransform.rawCarrierEquiv x.1 forbidden x.2).symm.injective
  · intro h
    exact ((operatorMFProperty_semantics (transform x)).1 ((correct x).2 h)).comap
      (RawTransform.rawCarrierEquiv x.1 forbidden x.2).toMonoidHom
      (RawTransform.rawCarrierEquiv x.1 forbidden x.2).injective

/-! ## The reduction

All four fields are now available: the Markov witness from
`PresentationCodes.markovWitness`, the transformation as list surgery, its
computability from `RawTransformPrimrec`, and correctness above.  Assembling
them leaves the undecidability of MF recognition resting on exactly one input,
the undecidability of the word problem as a predicate on codes. -/

/-- **The Adian--Rabin reduction**, from the word problem on presentation codes
to operator-MF recognition. -/
noncomputable def reduction :
    AdianRabinReduction AdianRabinWordProblem.wordProblemPred
      (operatorMFProperty semantics) where
  markov := markovWitness
  transform := rawTransform
  transform_computable := RawTransformPrimrec.computable_rawTransform forbidden
  correct := correct_raw

/-- **Operator-MF recognition is undecidable**, given only that the word
problem is undecidable as a predicate on presentation codes.  Every
group-theoretic input is discharged; this is the single remaining hypothesis,
and it is a statement about computability, not about groups. -/
theorem operatorMF_recognition_undecidable_of_wordProblem :
    ¬ ComputablePred AdianRabinWordProblem.wordProblemPred →
      ¬ ComputablePred (operatorMFProperty semantics) :=
  fun h => recognition_undecidable reduction h

/-- The same, for the negative side. -/
theorem operatorMF_negative_side_not_re_of_wordProblem :
    ¬ REPred (fun x => ¬ AdianRabinWordProblem.wordProblemPred x) →
      ¬ REPred (fun code => ¬ operatorMFProperty semantics code) :=
  fun h => negative_side_not_re reduction h

end AdianRabinVariantTransform
end GroupApproximation
