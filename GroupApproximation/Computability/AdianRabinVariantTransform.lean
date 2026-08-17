import GroupApproximation.Computability.RabinVariantCode
import GroupApproximation.Computability.CoprodCode
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
theorem correct (x : PresentationCode × List (ℕ × Bool)) :
    operatorMFProperty semantics (transform x) ↔ WordProblem x.1 x.2 := by
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

end AdianRabinVariantTransform
end GroupApproximation
