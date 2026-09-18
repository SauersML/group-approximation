import GroupApproximation.Analysis.CStarTakesakiIdentification

/-!
# Compressions of ⋆-representations contract the minimal tensor norm

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness", last sentence: for a discrete group, group exactness gives
exactness of the reduced group C⋆-algebra \cite{KWExact}.  The analytic
engine of that implication (Kirchberg--Wassermann, Ozawa) is that a
*compression* of a ⋆-representation,

  `Φ(c) = V⋆ ρ(c) V`,  with `‖V‖ ≤ 1`,

acts contractively on the minimal tensor product in the second leg.  This
file proves that estimate on the algebraic tensor product, together with the
isometric right-leg inclusion of a faithfully represented C⋆-algebra into
the bounded operators.

* `spatialHom_lTensor_compress_apply` --- the product representation of
  `(id ⊗ Φ)(y)` is `(1 ⊗ V⋆) (π ⊗ ρ)(y) (1 ⊗ V)`.
* `minTensorNorm_lTensor_compress_le` --- `‖(id ⊗ Φ) y‖_min ≤ ‖y‖_min`.
* `minTensorNorm_lTensor_of_injective` --- for a faithful ⋆-representation
  `ρ₀ : C → B(K)`, `‖(id ⊗ ρ₀) y‖_min = ‖y‖_min`.

Both estimates reduce the second leg to a single concrete representation by
Takesaki's right-leg domination (`spatialNorm_gnsRep_le_right`) and return
through the unconditional bound `spatialNorm_le_minTensorNorm`.
-/

namespace GroupApproximation.Full.NN09c

open GroupApproximation.CStarTensor GroupApproximation.CStarState
open scoped TensorProduct InnerProductSpace

universe u v w x

section Compression

variable {B : Type u} [CStarAlgebra B] [Nontrivial B]
variable {C : Type v} [CStarAlgebra C] [Nontrivial C]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]
variable {K' : Type x} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
  [CompleteSpace K']

omit [Nontrivial B] [Nontrivial C] in
/-- The product representation of a compressed tensor is the compression of
the product representation: `(π ⊗ id)((id ⊗ Φ) y) = (1 ⊗ V⋆)(π ⊗ ρ)(y)(1 ⊗ V)`
when `Φ c = V⋆ ρ(c) V`. -/
theorem spatialHom_lTensor_compress_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : StarRep B H)
    (ρ : C →⋆ₐ[ℂ] (K' →L[ℂ] K')) (V : K →L[ℂ] K')
    (Φ : C →ₗ[ℂ] (K →L[ℂ] K))
    (hΦ : ∀ c, Φ c = (ContinuousLinearMap.adjoint V).comp ((ρ c).comp V))
    (y : B ⊗[ℂ] C) (W : H ⊗[ℂ] K) :
    spatialHom π (StarRep.ofStarAlgHom (StarAlgHom.id ℂ (K →L[ℂ] K)))
        (LinearMap.lTensor B Φ y) W
      = TensorProduct.mapL (ContinuousLinearMap.id ℂ H)
          (ContinuousLinearMap.adjoint V)
          (spatialHom π (StarRep.ofStarAlgHom ρ) y
            (TensorProduct.mapL (ContinuousLinearMap.id ℂ H) V W)) := by
  induction y using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, zero_apply]
  | tmul a c =>
      rw [LinearMap.lTensor_tmul, spatialHom_tmul, spatialHom_tmul]
      induction W using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul p q =>
          have hc : (StarRep.ofStarAlgHom (StarAlgHom.id ℂ (K →L[ℂ] K))).hom
                (Φ c) q
              = ContinuousLinearMap.adjoint V
                  ((StarRep.ofStarAlgHom ρ).hom c (V q)) :=
            congrArg (fun T : K →L[ℂ] K ↦ T q) (hΦ c)
          rw [TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
            TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
            ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, hc]
      | add W₁ W₂ h₁ h₂ =>
          simp only [map_add, h₁, h₂]
  | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, add_apply, h₁, h₂]

omit [Nontrivial B] [Nontrivial C] in
/-- A contraction `V` gives `‖(1 ⊗ V) W‖ ≤ ‖W‖` on the algebraic Hilbert
tensor product. -/
theorem norm_mapL_id_apply_le {H : Type*} {E : Type*} {F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : E →L[ℂ] F) (hT : ‖T‖ ≤ 1) (W : H ⊗[ℂ] E) :
    ‖TensorProduct.mapL (ContinuousLinearMap.id ℂ H) T W‖ ≤ ‖W‖ := by
  have hid : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hmap : ‖TensorProduct.mapL (ContinuousLinearMap.id ℂ H) T‖ ≤ 1 := by
    refine (TensorProduct.norm_mapL_le _ _).trans ?_
    calc ‖ContinuousLinearMap.id ℂ H‖ * ‖T‖ ≤ 1 * 1 :=
          mul_le_mul hid hT (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc ‖TensorProduct.mapL (ContinuousLinearMap.id ℂ H) T W‖
      ≤ ‖TensorProduct.mapL (ContinuousLinearMap.id ℂ H) T‖ * ‖W‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖W‖ := mul_le_mul_of_nonneg_right hmap (norm_nonneg W)
    _ = ‖W‖ := one_mul _

omit [Nontrivial B] [Nontrivial C] in
/-- The operator-norm form of the compression estimate, for one first leg. -/
theorem norm_spatialHom_lTensor_compress_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : StarRep B H)
    (ρ : C →⋆ₐ[ℂ] (K' →L[ℂ] K')) (V : K →L[ℂ] K') (hV : ‖V‖ ≤ 1)
    (Φ : C →ₗ[ℂ] (K →L[ℂ] K))
    (hΦ : ∀ c, Φ c = (ContinuousLinearMap.adjoint V).comp ((ρ c).comp V))
    (y : B ⊗[ℂ] C) :
    ‖spatialHom π (StarRep.ofStarAlgHom (StarAlgHom.id ℂ (K →L[ℂ] K)))
        (LinearMap.lTensor B Φ y)‖
      ≤ ‖spatialHom π (StarRep.ofStarAlgHom ρ) y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (ContinuousLinearMap.opNorm_nonneg _) fun W ↦ ?_
  rw [spatialHom_lTensor_compress_apply π ρ V Φ hΦ y W]
  have hadj : ‖ContinuousLinearMap.adjoint V‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hV
  have hW := norm_mapL_id_apply_le (H := H) V hV W
  calc ‖TensorProduct.mapL (ContinuousLinearMap.id ℂ H)
          (ContinuousLinearMap.adjoint V)
          (spatialHom π (StarRep.ofStarAlgHom ρ) y
            (TensorProduct.mapL (ContinuousLinearMap.id ℂ H) V W))‖
      ≤ ‖spatialHom π (StarRep.ofStarAlgHom ρ) y
            (TensorProduct.mapL (ContinuousLinearMap.id ℂ H) V W)‖ :=
        norm_mapL_id_apply_le _ hadj _
    _ ≤ ‖spatialHom π (StarRep.ofStarAlgHom ρ) y‖
          * ‖TensorProduct.mapL (ContinuousLinearMap.id ℂ H) V W‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖spatialHom π (StarRep.ofStarAlgHom ρ) y‖ * ‖W‖ :=
        mul_le_mul_of_nonneg_left hW (ContinuousLinearMap.opNorm_nonneg _)

/-- **Compressions contract the minimal tensor norm.**  If `Φ c = V⋆ ρ(c) V`
for a ⋆-representation `ρ` on a Hilbert space and a contraction `V`, then
`‖(id ⊗ Φ) y‖_min ≤ ‖y‖_min`. -/
theorem minTensorNorm_lTensor_compress_le [Nontrivial (K →L[ℂ] K)]
    (ρ : C →⋆ₐ[ℂ] (K' →L[ℂ] K')) (V : K →L[ℂ] K') (hV : ‖V‖ ≤ 1)
    (Φ : C →ₗ[ℂ] (K →L[ℂ] K))
    (hΦ : ∀ c, Φ c = (ContinuousLinearMap.adjoint V).comp ((ρ c).comp V))
    (y : B ⊗[ℂ] C) :
    minTensorNorm (LinearMap.lTensor B Φ y) ≤ minTensorNorm y := by
  rw [minTensorNorm_apply (LinearMap.lTensor B Φ y)]
  refine ciSup_le fun p ↦ ?_
  refine (spatialNorm_gnsRep_le_right (StarAlgHom.id ℂ (K →L[ℂ] K))
    (fun _ _ h ↦ h) p.2 p.1.gnsRep (LinearMap.lTensor B Φ y)).trans ?_
  rw [spatialNorm_apply]
  refine (norm_spatialHom_lTensor_compress_le p.1.gnsRep ρ V hV Φ hΦ y).trans ?_
  rw [← spatialNorm_apply]
  exact spatialNorm_le_minTensorNorm p.1.gnsRep (StarRep.ofStarAlgHom ρ) y

omit [Nontrivial B] [Nontrivial C] [CompleteSpace K] in
/-- Amplifying a ⋆-homomorphism in the second leg does not change the product
representation. -/
theorem spatialHom_lTensor_ofStarAlgHom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace K] (π : StarRep B H)
    (ρ₀ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (Φ : C →ₗ[ℂ] (K →L[ℂ] K))
    (hΦ : ∀ c, Φ c = ρ₀ c) (y : B ⊗[ℂ] C) :
    spatialHom π (StarRep.ofStarAlgHom (StarAlgHom.id ℂ (K →L[ℂ] K)))
        (LinearMap.lTensor B Φ y)
      = spatialHom π (StarRep.ofStarAlgHom ρ₀) y := by
  induction y using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero]
  | tmul a c =>
      have hc : (StarRep.ofStarAlgHom (StarAlgHom.id ℂ (K →L[ℂ] K))).hom (Φ c)
          = (StarRep.ofStarAlgHom ρ₀).hom c := hΦ c
      rw [LinearMap.lTensor_tmul, spatialHom_tmul, spatialHom_tmul, hc]
  | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]

/-- **The right-leg inclusion of a faithfully represented C⋆-algebra is
isometric for the minimal norm**: `‖(id ⊗ ρ₀) y‖_min = ‖y‖_min`. -/
theorem minTensorNorm_lTensor_of_injective [Nontrivial (K →L[ℂ] K)]
    (ρ₀ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) (hρ₀ : Function.Injective ρ₀)
    (Φ : C →ₗ[ℂ] (K →L[ℂ] K)) (hΦ : ∀ c, Φ c = ρ₀ c) (y : B ⊗[ℂ] C) :
    minTensorNorm (LinearMap.lTensor B Φ y) = minTensorNorm y := by
  refine le_antisymm ?_ ?_
  · rw [minTensorNorm_apply (LinearMap.lTensor B Φ y)]
    refine ciSup_le fun p ↦ ?_
    refine (spatialNorm_gnsRep_le_right (StarAlgHom.id ℂ (K →L[ℂ] K))
      (fun _ _ h ↦ h) p.2 p.1.gnsRep (LinearMap.lTensor B Φ y)).trans ?_
    rw [spatialNorm_apply, spatialHom_lTensor_ofStarAlgHom p.1.gnsRep ρ₀ Φ hΦ y,
      ← spatialNorm_apply]
    exact spatialNorm_le_minTensorNorm p.1.gnsRep (StarRep.ofStarAlgHom ρ₀) y
  · rw [minTensorNorm_apply y]
    refine ciSup_le fun p ↦ ?_
    refine (spatialNorm_gnsRep_le_right ρ₀ hρ₀ p.2 p.1.gnsRep y).trans ?_
    rw [spatialNorm_apply, ← spatialHom_lTensor_ofStarAlgHom p.1.gnsRep ρ₀ Φ hΦ y,
      ← spatialNorm_apply]
    exact spatialNorm_le_minTensorNorm p.1.gnsRep
      (StarRep.ofStarAlgHom (StarAlgHom.id ℂ (K →L[ℂ] K))) _

end Compression

end GroupApproximation.Full.NN09c
