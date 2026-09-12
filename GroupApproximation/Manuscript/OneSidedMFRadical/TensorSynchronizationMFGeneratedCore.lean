import GroupApproximation.Analysis.ReducedProductMFPermanence
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly

/-!
# MF permanence for the tensor-synchronized generated algebra
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint

open Filter PolarLiftingGeneralCStar
open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationAssembly

noncomputable section

universe u v

/-- **The unconditional MF-algebra endpoint of tensor synchronization.** -/
theorem synchronizedGeneratedCStar_isMF
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    {G : Type v} [Countable G]
    (rho : G → unitary (CStarProductCorona B cofinite))
    (hB : ∀ n, HasMFEmbedding (B n)) :
    IsMFAlgebra (SynchronizedGeneratedCStar rho) := by
  letI : CStarAlgebra (SynchronizedGeneratedCStar rho) :=
    synchronizedGeneratedCStar_cStarAlgebra rho
  let i : SynchronizedGeneratedCStar rho →⋆ₙₐ[ℂ]
      CStarProductCorona B cofinite :=
    (SynchronizedGeneratedCStar rho).subtype.toNonUnitalStarAlgHom
  have hi : Function.Injective i := by
    intro x y hxy
    exact Subtype.ext hxy
  letI : TopologicalSpace.SeparableSpace (SynchronizedGeneratedCStar rho) :=
    synchronizedGeneratedCStar_separable rho
  exact ReducedProductMFPermanence.isMFAlgebra_of_injective_reducedProduct
    B i hi hB

end

end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFEndpoint
