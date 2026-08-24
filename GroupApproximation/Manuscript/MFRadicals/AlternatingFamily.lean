import GroupApproximation.Sofic.AlternatingLampExactRadical

/-!
# Infinitely many invisible differences

Specialising Theorem C to `K = Aₙ` over the concrete affine doubling datum
gives, for every `n ≥ 5`, a sofic finitely generated non-MF group

  `Wₙ = Aₙ^(V/Γ) ⋊ V`

whose MF radical, finite-dimensional unitary residual, finite residual and
all-fields linear residual all equal the lamp subgroup `Aₙ^(V/Γ)`.  Every `Wₙ`
therefore has the *same* universal MF-visible quotient `V`, while the family is
pairwise noncommensurable: no finite-index subgroup of one member is isomorphic
to a finite-index subgroup of another.

So infinitely many pairwise noncommensurable groups can differ solely inside the
part that every one of those four approximation theories erases.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

open MatricialStabilityRadical AlternatingLampFamily

/-- **The alternating family, exactly computed.**  All four radicals of `Wₙ`
coincide with its lamp subgroup, and `Wₙ` is sofic, finitely generated and not
MF. -/
def AlternatingFamilyExactRadicals : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    IsSofic (WAlt n) ∧ ¬ IsCDEOperatorMF (WAlt n) ∧ Group.FG (WAlt n) ∧
      actualCoronaMFResidual (WAlt n) = lampSub n ∧
      fdUnitaryResidual (WAlt n) = lampSub n ∧
      finiteResidual (WAlt n) = lampSub n ∧
      linearResidual (WAlt n) = lampSub n

theorem manuscriptAlternatingFamilyExactRadicals :
    AlternatingFamilyExactRadicals :=
  fun _ hn => alternatingFamilyPackage hn

/-- **The same visible quotient for every member.** -/
def AlternatingFamilySameVisibleQuotient : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    Nonempty ((WAlt n ⧸ actualCoronaMFResidual (WAlt n)) ≃*
      MarkedCompression.Vertical ExplicitLinearModel.conjD
        ExplicitLinearModel.conjD_injective)

theorem manuscriptAlternatingFamilySameVisibleQuotient :
    AlternatingFamilySameVisibleQuotient :=
  fun _ hn => ⟨universalVisibleQuotientEquiv hn⟩

/-- **Pairwise noncommensurable.**  Distinct degrees give members with no
isomorphic finite-index subgroups at all. -/
def AlternatingFamilyNoncommensurable : Prop :=
  ∀ m n : ℕ, 5 ≤ m → 5 ≤ n → m ≠ n →
    IsEmpty (WAlt m ≃* WAlt n) ∧
      ∀ (A : Subgroup (WAlt m)), A.FiniteIndex →
        ∀ (B : Subgroup (WAlt n)), B.FiniteIndex → IsEmpty (↥A ≃* ↥B)

theorem manuscriptAlternatingFamilyNoncommensurable :
    AlternatingFamilyNoncommensurable := by
  intro m n hm hn hmn
  refine ⟨not_mulEquiv_of_ne hm hn hmn, ?_⟩
  intro A hA B hB
  haveI := hA
  haveI := hB
  exact isEmpty_mulEquiv_finiteIndex_of_ne hm hn hmn

end MFRadicals
end Manuscript
end GroupApproximation
