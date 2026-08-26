import GroupApproximation.Analysis.MatrixCoronaAmplificationEmbedding

/-!
# Compatible embeddings survive matrix-corona amplification

The HNN corner argument produces two faithful maps into a matrix algebra over
one norm-matrix corona.  `MatrixCoronaAmplificationEmbedding` embeds that
matrix algebra into a single enlarged norm-matrix corona.  This file records
the exact compatibility-preserving composition needed before applying
Shulman's MF criterion for full amalgamated free products.

No MF permanence theorem is used here.  The result is only the unconditional
matrix-corona reduction which precedes that literature input.
-/

namespace GroupApproximation
namespace CompatibleMatrixCoronaAmplification

open MatrixCoronaAmplificationEmbedding

noncomputable section

universe u v w

variable {C : Type u} {A : Type v} {B : Type w}
  [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-- Compatible faithful maps into matrices over a norm-matrix corona compose
with matrix amplification to give compatible faithful maps into one enlarged
norm-matrix corona.

This is the precise formal replacement for the manuscript phrase
"identify `M_I(Q)` with a norm matrix corona".  The construction only needs
an embedding, not a surjective identification. -/
theorem exists_compatible_embeddings_into_amplified_corona
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (left : A →⋆ₙₐ[ℂ]
      CStarMatrix I I (NormMatrixCStarCorona (fun n ↦ X n)))
    (right : B →⋆ₙₐ[ℂ]
      CStarMatrix I I (NormMatrixCStarCorona (fun n ↦ X n)))
    (hleft : Function.Injective left)
    (hright : Function.Injective right)
    (hcompatible : left.comp iA = right.comp iB) :
    ∃ left' : A →⋆ₙₐ[ℂ]
        NormMatrixCStarCorona (fun n ↦ I × X n),
      ∃ right' : B →⋆ₙₐ[ℂ]
        NormMatrixCStarCorona (fun n ↦ I × X n),
        Function.Injective left' ∧ Function.Injective right' ∧
          left'.comp iA = right'.comp iB := by
  let amp := matrixCoronaAmplification (I := I) X
  refine ⟨amp.comp left, amp.comp right, ?_, ?_, ?_⟩
  · exact (matrixCoronaAmplification_injective X).comp hleft
  · exact (matrixCoronaAmplification_injective X).comp hright
  · rw [NonUnitalStarAlgHom.comp_assoc, hcompatible,
      NonUnitalStarAlgHom.comp_assoc]

end

end CompatibleMatrixCoronaAmplification
end GroupApproximation
