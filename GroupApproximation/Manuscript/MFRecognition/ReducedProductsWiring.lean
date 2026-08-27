import GroupApproximation.Analysis.MFAlgebraMatrixAmplification
import GroupApproximation.Manuscript.MFRecognition.ReducedProductsPermanenceWiring

/-!
# `lem:reduced-products`: reduced products of MF algebras

The manuscript `mf_recognition_complexity.tex` prints, immediately before the
tensor-synchronization lemma:

> **Lemma (reduced products of MF algebras).**  If every `B_n` is MF, then
> every separable `C*`-subalgebra of `∏_n B_n / ⊕_n B_n` is MF.  Moreover,
> `M_k(B)` is MF whenever `B` is.

and comments that

> The first assertion follows by diagonalization from the matrix-corona
> characterization of MF algebras (Blackadar--Kirchberg; see also
> Brown--Ozawa, Chapter 11), and Korchagin uses it in this form
> (Korchagin, Proposition 6).  The second holds because `M_k` of a norm
> matrix corona is the norm matrix corona of the dimension sequence
> multiplied by `k`.

Both clauses are stated here in the exact form in which the
tensor-synchronization proof consumes them.  The reduced product
`∏_n B_n / ⊕_n B_n` is the repository's `CStarProductCorona` at the cofinite
filter; a *separable `C*`-subalgebra* of it is, in the vocabulary of
`Analysis/MFAlgebra`, a separable `C*`-algebra with a faithful (possibly
nonunital) star homomorphism into it, which is exactly the surface on which
`IsMFAlgebra` is defined.

The second clause is proved here from
`MFAlgebraMatrixAmplification.isMFAlgebra_cstarMatrix`, with the positivity of
the matrix size carried as an explicit hypothesis rather than as a `Nonempty`
instance, following the repository convention for finite cardinalities.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace TensorSynchronization

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u v

noncomputable local instance reducedProductsWiringPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance reducedProductsWiringStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- **`lem:reduced-products`, second assertion.**  "Moreover, `M_k(B)` is MF
whenever `B` is."

"`M_k` of a norm matrix corona is the norm matrix corona of the dimension
sequence multiplied by `k`" is exactly
`MFAlgebraMatrixAmplification.hasMFEmbedding_cstarMatrix`, whose separable
package is `isMFAlgebra_cstarMatrix`. -/
theorem matrixAmplification_isMF {A : Type u} [CStarAlgebra A]
    (k : ℕ) (hk : 0 < k) (hA : IsMFAlgebra A) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    IsMFAlgebra (CStarMatrix (Fin k) (Fin k) A) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact MFAlgebraMatrixAmplification.isMFAlgebra_cstarMatrix k hA

end

end TensorSynchronization
end MFRecognition
end Manuscript
end GroupApproximation

#print axioms GroupApproximation.Manuscript.MFRecognition.TensorSynchronization.reducedProduct_separableSubalgebra_isMF
#print axioms GroupApproximation.Manuscript.MFRecognition.TensorSynchronization.matrixAmplification_isMF
