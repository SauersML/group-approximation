import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceCitations
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCitation

/-!
# `thm:hnn-permanence`, Step 2: `P` is MF

This module formalizes the paragraph

> *Step 2: `P` is MF.*  By Shulman's amalgamated-free-product criterion
> [Shulman, Theorem 16], the full amalgamated free product `A₁ *_C A₂` of
> separable `C*`-algebras is MF as soon as there are injective
> `*`-homomorphisms `φ_A` and `φ_B` of `A₁` and `A₂` into one norm matrix
> corona with `φ_A ∘ ι_A = φ_B ∘ ι_B`.  Identify `M₂(𝒬)` with the norm matrix
> corona of the doubled dimension sequence, and let `φ_A : M₂(D) → M₂(𝒬)` be
> the entrywise inclusion and `φ_B : M₂(B₀) → M₂(𝒬)` the entrywise inclusion
> followed by conjugation by `diag(1, W)`.  Both are injective, and on `C`,
> `φ_B(ι_B(c₀,c₁)) = diag(c₀, W Θ⁻¹(c₁) W*) = diag(c₀,c₁) = φ_A(ι_A(c₀,c₁))`,
> because `Θ` is conjugation by `W`.  So `P` is MF, as is its `C*`-subalgebra
> `ePe ≅ U`.

The two maps `φ_A`, `φ_B` and the displayed compatibility computation are
constructed in `HNNPermanenceUeda`, where they are already needed to name the
full amalgam `P`.  The identification of `M₂(𝒬)` with the corona of the
doubled dimension sequence is the repository's
`MFAlgebraMatrixAmplification.matrixCoronaHom`, the same map that proves
`lem:reduced-products`; as everywhere else in this development, MF embeddings
are allowed to be non-unital, as in `HasMFEmbedding`.

The Ueda corner embedding used below is constructed directly.  The remaining
input in this module is Shulman's amalgam MF theorem.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNAmalgamCornerSentences
open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open AmplifiedBlocks
open ReducedGroupCStarTrace

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-! ## `M₂(𝒬)` is the corona of the doubled dimension sequence -/

/-- Printed: *"Identify `M₂(𝒬)` with the norm matrix corona of the doubled
dimension sequence."*  This is the repository's matrix-amplification map at
`k = 2`, whose faithfulness is `matrixCoronaHom_injective`. -/
def doubledCoronaEmbedding (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] :
    CStarMatrix (Fin 2) (Fin 2) (Corona Y) →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ ampModel 2 (Y n)) :=
  MFAlgebraMatrixAmplification.matrixCoronaHom (k := 2) Y

theorem doubledCoronaEmbedding_injective (Y : ℕ → FiniteModel)
    [∀ n, Nonempty (Y n)] :
    Function.Injective (doubledCoronaEmbedding Y) :=
  MFAlgebraMatrixAmplification.matrixCoronaHom_injective (k := 2) Y

/-! ## The two corona factor maps of Step 2 -/

/-- `φ_A`, followed by the identification of `M₂(𝒬)` with a norm matrix
corona. -/
def shulmanFactorLeft (data : CoronaConjugator G S T phi A X) :
    matrixBaseAlgebra data →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ ampModel 2 (X n)) :=
  (doubledCoronaEmbedding X).comp (coronaFactorLeft data).toNonUnitalStarAlgHom

/-- `φ_B`, followed by the same identification. -/
def shulmanFactorRight (data : CoronaConjugator G S T phi A X) :
    matrixEdgeAlgebra data →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ ampModel 2 (X n)) :=
  (doubledCoronaEmbedding X).comp
    (coronaFactorRight data).toNonUnitalStarAlgHom

theorem shulmanFactorLeft_injective
    (data : CoronaConjugator G S T phi A X) :
    Function.Injective (shulmanFactorLeft data) :=
  (doubledCoronaEmbedding_injective X).comp (coronaFactorLeft_injective data)

theorem shulmanFactorRight_injective
    (data : CoronaConjugator G S T phi A X) :
    Function.Injective (shulmanFactorRight data) :=
  (doubledCoronaEmbedding_injective X).comp (coronaFactorRight_injective data)

/-- Printed: the displayed identity `φ_A ∘ ι_A = φ_B ∘ ι_B`, transported along
the identification of `M₂(𝒬)` with a norm matrix corona. -/
theorem shulmanFactor_compatible (data : CoronaConjugator G S T phi A X)
    (c : edgeSumAlgebra data) :
    shulmanFactorLeft data (amalgamLeftInclusion data c) =
      shulmanFactorRight data (amalgamRightInclusion data c) := by
  show doubledCoronaEmbedding X
      (coronaFactorLeft data (amalgamLeftInclusion data c)) =
    doubledCoronaEmbedding X
      (coronaFactorRight data (amalgamRightInclusion data c))
  rw [coronaFactor_compatible_apply]

/-! ## Separability of the three printed algebras -/

theorem sourceEdgeAlgebra_separableSpace [Countable G]
    (data : CoronaConjugator G S T phi A X) :
    TopologicalSpace.SeparableSpace (sourceEdgeAlgebra data) :=
  groupGeneratedCStar_separableSpace ((baseUnitaryHom data).comp S.subtype)

theorem targetEdgeAlgebra_separableSpace [Countable G]
    (data : CoronaConjugator G S T phi A X) :
    TopologicalSpace.SeparableSpace (targetEdgeAlgebra data) :=
  groupGeneratedCStar_separableSpace
    ((baseUnitaryHom data).comp (edgeHom phi))

theorem edgeSumAlgebra_separableSpace [Countable G]
    (data : CoronaConjugator G S T phi A X) :
    TopologicalSpace.SeparableSpace (edgeSumAlgebra data) := by
  letI : TopologicalSpace.SeparableSpace (sourceEdgeAlgebra data) :=
    sourceEdgeAlgebra_separableSpace data
  letI : TopologicalSpace.SeparableSpace (targetEdgeAlgebra data) :=
    targetEdgeAlgebra_separableSpace data
  infer_instance

theorem matrixBaseAlgebra_separableSpace [Countable G]
    (data : CoronaConjugator G S T phi A X) :
    TopologicalSpace.SeparableSpace (matrixBaseAlgebra data) := by
  letI : TopologicalSpace.SeparableSpace (baseAlgebra data) :=
    baseAlgebra_separableSpace data
  letI : ∀ _ : Fin 2, TopologicalSpace.SeparableSpace (baseAlgebra data) :=
    fun _ ↦ baseAlgebra_separableSpace data
  letI : ∀ _ : Fin 2,
      TopologicalSpace.SeparableSpace (Fin 2 → baseAlgebra data) :=
    fun _ ↦ inferInstance
  exact inferInstanceAs (TopologicalSpace.SeparableSpace
    (Fin 2 → Fin 2 → baseAlgebra data))

theorem matrixEdgeAlgebra_separableSpace [Countable G]
    (data : CoronaConjugator G S T phi A X) :
    TopologicalSpace.SeparableSpace (matrixEdgeAlgebra data) := by
  letI : TopologicalSpace.SeparableSpace (sourceEdgeAlgebra data) :=
    sourceEdgeAlgebra_separableSpace data
  letI : ∀ _ : Fin 2,
      TopologicalSpace.SeparableSpace (sourceEdgeAlgebra data) :=
    fun _ ↦ sourceEdgeAlgebra_separableSpace data
  letI : ∀ _ : Fin 2,
      TopologicalSpace.SeparableSpace (Fin 2 → sourceEdgeAlgebra data) :=
    fun _ ↦ inferInstance
  exact inferInstanceAs (TopologicalSpace.SeparableSpace
    (Fin 2 → Fin 2 → sourceEdgeAlgebra data))

/-! ## `P` is MF, and so is `ePe ≅ U` -/

/-- Printed: *"So `P` is MF"*. -/
theorem amalgam_isMFAlgebra (hShulman : ShulmanTheorem16Statement)
    [Countable G]
    (data : CoronaConjugator G S T phi A X) :
    IsMFAlgebra (amalgam data) :=
  hShulman (amalgamLeftInclusion data) (amalgamRightInclusion data)
    (edgeSumAlgebra_separableSpace data)
    (matrixBaseAlgebra_separableSpace data)
    (matrixEdgeAlgebra_separableSpace data)
    (fun n ↦ ampModel 2 (X n))
    (shulmanFactorLeft data) (shulmanFactorRight data)
    (shulmanFactorLeft_injective data) (shulmanFactorRight_injective data)
    (shulmanFactor_compatible data)

/-- Printed: *"as is its `C*`-subalgebra `ePe`"*. -/
theorem corner_isMFAlgebra (hShulman : ShulmanTheorem16Statement)
    [Countable G]
    (data : CoronaConjugator G S T phi A X) :
    IsMFAlgebra (CStarCorner (cornerUnit data) (cornerUnit_star data)
      (cornerUnit_mul data)) :=
  manuscriptSentence_7b20dd3d1d35_cornerIsMF (cornerUnit data)
    (cornerUnit_star data) (cornerUnit_mul data)
    (amalgam_isMFAlgebra hShulman data)

/-- Printed: *"as is its `C*`-subalgebra `ePe ≅ U`"*, in the form used by
Step 3: the universal `C*`-HNN algebra `U` is MF. -/
theorem universalHNN_isMFAlgebra
    (hShulman : ShulmanTheorem16Statement) (hUeda : UedaCornerMapStatement)
    [Countable G] (data : CoronaConjugator G S T phi A X) :
    IsMFAlgebra (universalHNN data) :=
  manuscriptSentence_7b20dd3d1d35_sourceIsMF (cornerUnit data)
    (cornerUnit_star data) (cornerUnit_mul data)
    (amalgam_isMFAlgebra hShulman data)
    (uedaCornerMap hUeda data)
    (uedaCornerMap_injective hUeda data)

/-- The direct Ueda corner embedding and Shulman's theorem prove the MF
statement consumed by the HNN permanence argument. -/
theorem universalHNNIsMFStatement_of_shulman
    (hShulman : ShulmanTheorem16Statement) (hUeda : UedaCornerMapStatement) :
    UniversalHNNIsMFStatement :=
  fun data ↦ universalHNN_isMFAlgebra hShulman hUeda data

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
