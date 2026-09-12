import GroupApproximation.Analysis.LIXCor4PowersShape
import GroupApproximation.Analysis.LIXLimitMatrixFlatten
import GroupApproximation.Analysis.LIXLimitSectionMatrix
import GroupApproximation.Analysis.LIXEndpointStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# `diag(U ⊕ 1, 1)` in `M₂(A₀)` is a block matrix over the base, at every rank

`Analysis/LIXLemmaSixDiag.lean` carries a null-homotopy of `genU ⊕ 1` in `M₄` over the base into
`M₂(A₀)` at rank two.  This file is the chain of ⋆-homomorphisms at every rank `n`:

    Γ(X₀, End (𝟏^n ⊕ 𝟏^n))  --sectionMatrixSymmHom-->  M_{n⊕n}(C(X₀))
                            --unflattenN-->            M₂(M_n(C(X₀)))
                            --matrixHom 2 entryHomN--> M₂(A₀),

with `entryHomN` the stage-zero identification `M_n(C(X₀)) ≅ A₀`, which exists because `E₀ = 𝟏`.
The chain carries `U₀` along it, and it carries the block section `U ⊕ 1` to `diag(U ⊕ 1_{H₀}, 1)`
on the nose (`diagChainN_sectionBlock`).  So `diag(U ⊕ 1_{H₀}, 1) ∈ U₀(M₂(A₀))` follows from
`U ⊕ 1 ∈ U₀` in the section algebra, where paths are pointwise and continuity is `curry`.

## Main results

* `Gen.Eproj_zero_eq_one`, `Gen.toStageZeroHom` — the stage-zero packaging at rank `n`.
* `Gen.flattenN` — `M₂(M_n(A)) ≃⋆ₐ[ℂ] M_{n⊕n}(A)`.
* `Gen.diagChainN`, `Gen.diagChainN_sectionBlock`.
* `Gen.diagOne_sphereUnitary_mem` — **the transport of `U₀`**.
-/

namespace GroupApproximation
namespace LIX
namespace Gen

open scoped Matrix ComplexOrder CStarAlgebra

attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The stage-zero packaging -/

section StageZero

/-- `E₀ = 𝟏` at rank `n`, because `H₀` is indexed by `Empty`. -/
theorem Eproj_zero_eq_one (n : ℕ) : STW59.Gen.Eproj n 0 = 1 := by
  rw [STW59.Gen.Eproj_def, STW59.Gen.Hproj_zero]
  ext a b
  rcases a with a | a
  · rcases b with b | b
    · simp [Matrix.one_apply]
    · exact Empty.elim b
  · exact Empty.elim a

theorem stageProj_zero_eq_one (n : ℕ) : STW59.Gen.stageProj n 0 = 1 := by
  show STW59.ofFunctionMatrix (STW59.Gen.Eproj n 0) = 1
  rw [Eproj_zero_eq_one, STW59.ofFunctionMatrix_one]

private theorem one_mul_mul_one' {A : Type*} [Monoid A] (a : A) : 1 * a * 1 = a := by
  rw [one_mul, mul_one]

theorem mem_stageAlgebra_zero {n : ℕ}
    (a : STW59.SectionAlgebra (STW59.Gen.baseX n 0) (STW59.Gen.EIdx n 0)) :
    a ∈ STW59.cornerAlgebra (STW59.Gen.stageProj n 0) (STW59.Gen.isStarProjection_stageProj n 0) := by
  rw [STW59.Gen.mem_stageAlgebra_iff, stageProj_zero_eq_one]
  exact one_mul_mul_one' a

/-- Every section is an element of `A₀`. -/
def toStageZero {n : ℕ} (a : STW59.SectionAlgebra (STW59.Gen.baseX n 0) (STW59.Gen.EIdx n 0)) :
    STW59.Gen.StageAlgebra n 0 :=
  ⟨a, mem_stageAlgebra_zero a⟩

/-- **The stage-zero packaging as a unital ⋆-homomorphism.** -/
def toStageZeroHom (n : ℕ) :
    STW59.SectionAlgebra (STW59.Gen.baseX n 0) (STW59.Gen.EIdx n 0)
      →⋆ₐ[ℂ] STW59.Gen.StageAlgebra n 0 where
  toFun := toStageZero
  map_one' := by
    refine STW59.corner_ext ?_
    show (1 : STW59.SectionAlgebra (STW59.Gen.baseX n 0) (STW59.Gen.EIdx n 0))
      = STW59.Gen.stageProj n 0
    rw [stageProj_zero_eq_one]
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    refine STW59.corner_ext ?_
    show algebraMap ℂ (STW59.SectionAlgebra (STW59.Gen.baseX n 0) (STW59.Gen.EIdx n 0)) c
      = ((algebraMap ℂ (STW59.Gen.StageAlgebra n 0) c : STW59.Gen.StageAlgebra n 0) :
          STW59.SectionAlgebra (STW59.Gen.baseX n 0) (STW59.Gen.EIdx n 0))
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, STW59.coe_corner_smul,
      STW59.Gen.coe_stageAlgebra_one, stageProj_zero_eq_one]
  map_star' _ := rfl

end StageZero

/-! ## 2. The flattening `M₂(M_n(A)) ≅ M_{n⊕n}(A)` -/

section Flatten

variable {A : Type*} [CStarAlgebra A]

/-- `Fin 2 × Fin n ≃ Fin n ⊕ Fin n`: block `0` on the left, block `1` on the right. -/
def sumProd (n : ℕ) : Fin 2 × Fin n ≃ Fin n ⊕ Fin n where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun := Sum.elim (fun a => ((0 : Fin 2), a)) (fun a => ((1 : Fin 2), a))
  left_inv := by
    rintro ⟨i, a⟩
    fin_cases i <;> rfl
  right_inv := by
    rintro (a | a) <;> rfl

theorem matrixComp_star_n (n : ℕ) (M : Matrix (Fin 2) (Fin 2) (Matrix (Fin n) (Fin n) A)) :
    Matrix.comp (Fin 2) (Fin 2) (Fin n) (Fin n) A (star M)
      = star (Matrix.comp (Fin 2) (Fin 2) (Fin n) (Fin n) A M) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rfl

/-- `Matrix.compAlgEquiv` upgraded to a ⋆-algebra equivalence, for `2 × 2` blocks of size `n`. -/
def matrixCompStarAlgEquivN (A : Type*) [CStarAlgebra A] (n : ℕ) :
    Matrix (Fin 2) (Fin 2) (Matrix (Fin n) (Fin n) A) ≃⋆ₐ[ℂ]
      Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) A :=
  { (Matrix.compAlgEquiv (Fin 2) (Fin n) A ℂ).toRingEquiv with
    map_star' := matrixComp_star_n n
    map_smul' := fun _ _ => rfl }

variable (A) in
/-- **The flattening `M₂(M_n(A)) ≃⋆ₐ[ℂ] M_{n⊕n}(A)`.** -/
def flattenN (n : ℕ) : CStarMat 2 (CStarMat n A) ≃⋆ₐ[ℂ] CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A :=
  (matrixCompStarAlgEquivN A n).trans (CStarMatrix.reindexₐ ℂ A (sumProd n))

variable (A) in
/-- The inverse of the flattening, as a unital ⋆-homomorphism. -/
def unflattenN (n : ℕ) :
    CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A →⋆ₐ[ℂ] CStarMat 2 (CStarMat n A) :=
  (flattenN A n).symm.toStarAlgHom

end Flatten

/-! ## 3. The chain -/

section Chain

variable {n : ℕ}

/-- `Fin n ≃ EIdx n 0 = Fin n ⊕ Empty`. -/
def eIdxZeroEquivN (n : ℕ) : Fin n ≃ STW59.Gen.EIdx n 0 := (Equiv.sumEmpty (Fin n) Empty).symm

/-- The identification of `M_n(C(X₀))` with the stage-zero algebra. -/
def entryHomN (n : ℕ) : CStarMat n C(STW59.Gen.baseX n 0, ℂ) →⋆ₐ[ℂ] STW59.Gen.StageAlgebra n 0 :=
  ((toStageZeroHom n).comp sectionMatrixHom).comp
    (CStarMatrix.reindexₐ ℂ C(STW59.Gen.baseX n 0, ℂ) (eIdxZeroEquivN n)).toStarAlgHom

/-- **The chain** from the section algebra over `𝟏^n ⊕ 𝟏^n` to `M₂(A₀)`. -/
def diagChainN (n : ℕ) :
    STW59.SectionAlgebra (STW59.Gen.baseX n 0) (Fin n ⊕ Fin n)
      →⋆ₐ[ℂ] CStarMat 2 (STW59.Gen.StageAlgebra n 0) :=
  ((matrixHom 2 (entryHomN n)).comp (unflattenN C(STW59.Gen.baseX n 0, ℂ) n)).comp
    sectionMatrixSymmHom

/-- Every arrow of the chain is a rearrangement of indices, so an entry reads off by `rfl`. -/
theorem diagChainN_entry (S : unitary (STW59.SectionAlgebra (STW59.Gen.baseX n 0) (Fin n ⊕ Fin n)))
    (i j : Fin 2) (w : STW59.Gen.baseX n 0) (a b : Fin n) :
    ((unitaryHom (diagChainN n) S : CStarMat 2 (STW59.Gen.StageAlgebra n 0)) i j :
        STW59.SectionAlgebra (STW59.Gen.baseX n 0) (STW59.Gen.EIdx n 0)) w (Sum.inl a) (Sum.inl b)
      = (S : STW59.SectionAlgebra (STW59.Gen.baseX n 0) (Fin n ⊕ Fin n)) w
          (sumProd n (i, a)) (sumProd n (j, b)) := rfl

theorem sphereMatAt_apply (j : ℕ) (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) (a b : Fin n) (w : STW59.Gen.baseX n j) :
    sphereMatAt n j U hU a b w = U w.1 a b := rfl

/-- The block section `U ⊕ 1` over `𝟏^n ⊕ 𝟏^n`. -/
def sectionBlockMat (n : ℕ) (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(STW59.Gen.baseX n 0, ℂ) :=
  Matrix.fromBlocks (sphereMatAt n 0 U hU) 0 0 1

theorem sectionBlockMat_conjTranspose_mul {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hU : Continuous U) (hu : ∀ v, (U v)ᴴ * U v = 1) :
    (sectionBlockMat n U hU)ᴴ * sectionBlockMat n U hU = 1 := by
  rw [sectionBlockMat, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, Matrix.fromBlocks_multiply,
    sphereMatAt_conjTranspose_mul 0 hU hu]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
  exact Matrix.fromBlocks_one

theorem sectionBlockMat_mul_conjTranspose {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hU : Continuous U) (hu : ∀ v, U v * (U v)ᴴ = 1) :
    sectionBlockMat n U hU * (sectionBlockMat n U hU)ᴴ = 1 := by
  rw [sectionBlockMat, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, Matrix.fromBlocks_multiply,
    sphereMatAt_mul_conjTranspose 0 hU hu]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
  exact Matrix.fromBlocks_one

/-- **`U ⊕ 1` as a unitary of the section algebra over `X₀`.** -/
def sectionBlock (n : ℕ) (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) (hu₁ : ∀ v, (U v)ᴴ * U v = 1) (hu₂ : ∀ v, U v * (U v)ᴴ = 1) :
    unitary (STW59.SectionAlgebra (STW59.Gen.baseX n 0) (Fin n ⊕ Fin n)) :=
  ⟨STW59.ofFunctionMatrix (sectionBlockMat n U hU), by
    rw [← STW59.ofFunctionMatrix_star, ← STW59.ofFunctionMatrix_mul, Matrix.star_eq_conjTranspose,
      sectionBlockMat_conjTranspose_mul hU hu₁, STW59.ofFunctionMatrix_one], by
    rw [← STW59.ofFunctionMatrix_star, ← STW59.ofFunctionMatrix_mul, Matrix.star_eq_conjTranspose,
      sectionBlockMat_mul_conjTranspose hU hu₂, STW59.ofFunctionMatrix_one]⟩

-- `simp` below runs under `<;>` over four branches and uses different arguments in different ones;
-- the unusedSimpArgs linter aggregates them and reports some as unused.
set_option linter.unusedSimpArgs false in
/-- **The chain carries `U ⊕ 1` to `diag(U ⊕ 1_{H₀}, 1)` on the nose.** -/
theorem diagChainN_sectionBlock (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) (hu₁ : ∀ v, (U v)ᴴ * U v = 1) (hu₂ : ∀ v, U v * (U v)ᴴ = 1) :
    unitaryHom (diagChainN n) (sectionBlock n U hU hu₁ hu₂) = diagOne (sphereUnitary n U hU hu₁ hu₂) := by
  refine Subtype.ext (CStarMatrix.ext fun i j => ?_)
  refine STW59.corner_ext (ContinuousMap.ext fun w => Matrix.ext fun r s => ?_)
  rcases r with a | e
  swap
  · exact Empty.elim e
  rcases s with b | e
  swap
  · exact Empty.elim e
  rw [diagChainN_entry, coe_diagOne_apply]
  fin_cases i <;> fin_cases j <;>
    simp [sumProd, sectionBlock, sectionBlockMat, sphereMatAt_apply, coe_sphereUnitary,
      coe_sphereStage, STW59.Gen.blockUnitary_def, STW59.Gen.coe_stageAlgebra_one,
      stageProj_zero_eq_one, Matrix.one_apply, CStarMatrix.one_apply, Sum.inl.injEq,
      apply_ite (fun f : C(STW59.Gen.baseX n 0, ℂ) => f w)]

/-- **The transport of `U₀`.**  If `U ⊕ 1` is null-homotopic in the section algebra over `X₀`, then
`diag(U ⊕ 1_{H₀}, 1)` is null-homotopic in `M₂(A₀)`. -/
theorem diagOne_sphereUnitary_mem (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) (hu₁ : ∀ v, (U v)ᴴ * U v = 1) (hu₂ : ∀ v, U v * (U v)ᴴ = 1)
    (h : sectionBlock n U hU hu₁ hu₂
      ∈ unitaryComponentOne (STW59.SectionAlgebra (STW59.Gen.baseX n 0) (Fin n ⊕ Fin n))) :
    diagOne (sphereUnitary n U hU hu₁ hu₂)
      ∈ unitaryComponentOne (CStarMat 2 (STW59.Gen.StageAlgebra n 0)) := by
  rw [← diagChainN_sectionBlock]
  exact unitaryHom_mem_unitaryComponentOne _ h

end Chain

end

end Gen
end LIX
end GroupApproximation

open GroupApproximation.LIX.Gen

#audit_axioms toStageZeroHom
#audit_axioms flattenN
#audit_axioms diagChainN_sectionBlock
#audit_axioms diagOne_sphereUnitary_mem
