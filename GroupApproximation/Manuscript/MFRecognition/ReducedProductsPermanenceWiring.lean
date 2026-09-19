import GroupApproximation.Analysis.ReducedProductMFPermanence

/-!
# Reduced-product permanence in the MF-recognition namespace

This leaf isolates the analytic clause of `lem:reduced-products` from the
independent matrix-amplification clause.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace TensorSynchronization

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u v

/-- Every separable C-star algebra faithfully represented in a cofinite
reduced product of MF algebras is MF. -/
theorem reducedProduct_separableSubalgebra_isMF
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (hB : ∀ n, IsMFAlgebra (B n))
    (C : Type v) [CStarAlgebra C] [TopologicalSpace.SeparableSpace C]
    (e : C →⋆ₙₐ[ℂ] CStarProductCorona B cofinite)
    (he : Function.Injective e) :
    IsMFAlgebra C := by
  exact ReducedProductMFPermanence.isMFAlgebra_of_injective_reducedProduct
    B e he (fun n ↦ (hB n).2)

end

end TensorSynchronization
end MFRecognition
end Manuscript
end GroupApproximation
