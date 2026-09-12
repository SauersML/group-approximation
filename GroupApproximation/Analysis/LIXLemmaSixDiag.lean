import GroupApproximation.Analysis.LIXLemmaSixDiagPath
import GroupApproximation.Analysis.LIXLemmaSixStageZero
import GroupApproximation.Analysis.LIXLimitMatrixFlatten
import GroupApproximation.Analysis.LIXLimitSectionMatrix
import GroupApproximation.Analysis.LIXLimitMatrixTransport
import GroupApproximation.Analysis.LIXEndpointStatement

/-!
# `diag(u, 1)` is null-homotopic in `U(M₂(A₀))`

This is `hdiag`, the second hypothesis of `LIX.lixLimit_hasK1InjWitness`.  All
of its mathematics is `paddedPath`: the null-homotopy of `genU ⊕ 1` inside
`M₄` over the base.  What this file does is read that homotopy in the algebra
where `diagOne` lives, by composing four arrows, each of which carries
`unitaryComponentOne` membership along it:

    Γ(X₀, End 𝟏⁴)  --sectionMatrixSymmHom-->  M₄(C(X₀))
                   --unflattenHom-->          M₂(M₂(C(X₀)))
                   --matrixHom 2 entryHom-->  M₂(A₀)

with `entryHom` the stage-zero identification `M₂(C(X₀)) ≅ A₀` assembled from
`CStarMatrix.reindexₐ`, cs-limit's `sectionMatrixHom` and `toStageZeroHom`.
The last of those exists only because `E₀ = 𝟏`.

The spectral-order priority is not optional here: without it
`PartialOrder (StageAlgebra 0)` resolves through `Subtype.partialOrder` to the
pointwise order on the ambient `C(X₀, CStarMatrix ι ι ℂ)`, and then
`CStarMat 2 (StageAlgebra 0)` is not a C⋆-algebra at all.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder CStarAlgebra

attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The homotopy as a path of unitaries of the section algebra -/

/-- `Γ(X₀, End 𝟏⁴)`, where the padded homotopy lives. -/
abbrev SecFour : Type := STW59.SectionAlgebra (STW59.baseX 0) (Fin 4)

/-- The padded homotopy, read in the section algebra. -/
def paddedSec (t : unitInterval) : SecFour := paddedSection t

@[simp]
theorem paddedSec_apply (t : unitInterval) (w : STW59.baseX 0) :
    paddedSec t w
      = paddedPath4 (t : ℝ) ((w.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5)) := rfl

theorem paddedSec_star_mul (t : unitInterval) : star (paddedSec t) * paddedSec t = 1 :=
  ContinuousMap.ext fun w =>
    paddedPath4_conjTranspose_mul_self w.1.2 t.2.1 t.2.2

theorem paddedSec_mul_star (t : unitInterval) : paddedSec t * star (paddedSec t) = 1 :=
  ContinuousMap.ext fun w =>
    paddedPath4_mul_conjTranspose w.1.2 t.2.1 t.2.2

/-- The homotopy as a family of unitaries of the section algebra. -/
def paddedUnitary (t : unitInterval) : unitary SecFour :=
  ⟨paddedSec t, paddedSec_star_mul t, paddedSec_mul_star t⟩

theorem continuous_paddedUnitary : Continuous paddedUnitary :=
  continuous_induced_rng.mpr paddedSection.continuous

theorem paddedUnitary_one : paddedUnitary 1 = 1 := by
  refine Subtype.ext (ContinuousMap.ext fun w => ?_)
  exact paddedPath4_one _

/-- **The endpoint of the homotopy is null-homotopic in the section algebra.** -/
theorem paddedUnitary_zero_mem :
    paddedUnitary 0 ∈ unitaryComponentOne SecFour := by
  refine mem_unitaryComponentOne_iff.mpr ?_
  have h : Joined (paddedUnitary 0) (paddedUnitary 1) :=
    ⟨⟨⟨paddedUnitary, continuous_paddedUnitary⟩, rfl, rfl⟩⟩
  rw [paddedUnitary_one] at h
  exact h.symm

/-! ## The stage-zero identification `M₂(C(X₀)) ≅ A₀` -/

/-- `EIdx 0 = Fin 2 ⊕ Empty`. -/
def eIdxZeroEquiv : Fin 2 ≃ STW59.EIdx 0 := (Equiv.sumEmpty (Fin 2) Empty).symm

/-- The identification of `M₂(C(X₀))` with the stage-zero algebra. -/
def entryHom : CStarMat 2 C(STW59.baseX 0, ℂ) →⋆ₐ[ℂ] STW59.StageAlgebra 0 :=
  (toStageZeroHom.comp sectionMatrixHom).comp
    (CStarMatrix.reindexₐ ℂ C(STW59.baseX 0, ℂ) eIdxZeroEquiv).toStarAlgHom

/-- The whole chain from `M₄(C(X₀))` to `M₂(A₀)`. -/
def diagChain : CStarMat 4 C(STW59.baseX 0, ℂ) →⋆ₐ[ℂ] CStarMat 2 (STW59.StageAlgebra 0) :=
  (matrixHom 2 entryHom).comp (unflattenHom C(STW59.baseX 0, ℂ))

/-- **The transported homotopy lands in `U₀`.**  Each arrow of the chain
carries `unitaryComponentOne` along it, by
`unitaryHom_mem_unitaryComponentOne`. -/
theorem transported_mem :
    unitaryHom diagChain (unitaryHom sectionMatrixSymmHom (paddedUnitary 0))
      ∈ unitaryComponentOne (CStarMat 2 (STW59.StageAlgebra 0)) :=
  unitaryHom_mem_unitaryComponentOne diagChain
    (sectionMatrixSymm_mem_unitaryComponentOne paddedUnitary_zero_mem)

end

end LIX
end GroupApproximation
