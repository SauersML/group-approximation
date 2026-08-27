import GroupApproximation.Analysis.NonUnitalMFSupportCornerEmbedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Faithful unital corona embeddings of nontrivial MF algebras

The repository's bare MF-embedding predicate permits nonunital maps.  For a
nontrivial unital C-star algebra, compression to the support projection turns
any faithful nonunital matrix-corona embedding into a faithful unital one.

The nontriviality hypothesis is essential: the zero unital algebra has no
unital homomorphism to a nontrivial matrix corona.
-/

namespace GroupApproximation
namespace MFAlgebraUnitalCoronaEmbedding

noncomputable section

universe u

/-- Every nontrivial MF C-star algebra has a faithful unital representation in
a norm-matrix corona. -/
theorem exists_injective_unital_coronaEmbedding
    {A : Type u} [CStarAlgebra A] [Nontrivial A]
    (hA : IsMFAlgebra A) :
    ∃ (X : ℕ → FiniteModel) (hX : ∀ n, Nonempty (X n)),
      letI : ∀ n, Nonempty (X n) := hX
      ∃ iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n),
        Function.Injective iota := by
  obtain ⟨Y, hY, _hYpos, _hYmono, e, he⟩ := hA.2
  letI : ∀ n, Nonempty (Y n) := hY
  exact
    NonUnitalMFSupportCornerEmbedding.exists_injective_unital_supportCornerEmbedding
      Y e he

end

end MFAlgebraUnitalCoronaEmbedding
end GroupApproximation

#audit_closed_axioms GroupApproximation.MFAlgebraUnitalCoronaEmbedding.exists_injective_unital_coronaEmbedding
