import GroupApproximation.Analysis.FiniteMatrixBlockCPRetract
import GroupApproximation.Analysis.CStarUnitalCPContractive
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite Wedderburn products are UCP retracts of one matrix algebra

The binary block construction is iterated here.  For every nonempty finite
product of nonzero full matrix algebras we produce one finite matrix algebra,
a unital star-homomorphic block-diagonal inclusion, and a unital completely
positive retraction.  The retraction is contractive because its composite
with the isometric inclusion is a UCP map into a matrix algebra.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

local instance matrixBlockCStarAlgebraForFiniteRetract
    (Y : Type) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- A unital completely positive retract of a C-star algebra from one full
matrix algebra. -/
structure MatrixUCPRetract (D : Type u) [CStarAlgebra D] where
  model : Type
  [fintype : Fintype model]
  [decidableEq : DecidableEq model]
  [modelNonempty : Nonempty model]
  embedding : D →⋆ₐ[ℂ] Matrix model model ℂ
  retract : Matrix model model ℂ →ₗ[ℂ] D
  retract_completelyPositive : IsCompletelyPositive retract
  retract_embedding : ∀ d, retract (embedding d) = d
  retract_one : retract 1 = 1

attribute [instance] MatrixUCPRetract.fintype MatrixUCPRetract.decidableEq
  MatrixUCPRetract.modelNonempty

/-- The inclusion in a matrix UCP retract is injective. -/
theorem MatrixUCPRetract.embedding_injective
    {D : Type u} [CStarAlgebra D] (R : MatrixUCPRetract D) :
    Function.Injective R.embedding := by
  intro x y h
  rw [← R.retract_embedding x, ← R.retract_embedding y, h]

/-- The associated matrix-valued conditional expectation. -/
def MatrixUCPRetract.expectation
    {D : Type u} [CStarAlgebra D] (R : MatrixUCPRetract D) :
    Matrix R.model R.model ℂ →ₗ[ℂ] Matrix R.model R.model ℂ :=
  (R.embedding : D →ₗ[ℂ] Matrix R.model R.model ℂ).comp R.retract

theorem MatrixUCPRetract.expectation_completelyPositive
    {D : Type u} [CStarAlgebra D] (R : MatrixUCPRetract D) :
    IsCompletelyPositive R.expectation :=
  (isCompletelyPositive_of_starAlgHom R.embedding.toNonUnitalStarAlgHom).comp
    R.retract_completelyPositive

theorem MatrixUCPRetract.expectation_one
    {D : Type u} [CStarAlgebra D] (R : MatrixUCPRetract D) :
    R.expectation 1 = 1 := by
  change R.embedding (R.retract 1) = 1
  rw [R.retract_one, map_one]

/-- The UCP retraction is contractive. -/
theorem MatrixUCPRetract.retract_norm_le
    {D : Type u} [CStarAlgebra D] (R : MatrixUCPRetract D)
    (T : Matrix R.model R.model ℂ) :
    ‖R.retract T‖ ≤ ‖T‖ := by
  let op : Matrix R.model R.model ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ R.model →L[ℂ] EuclideanSpace ℂ R.model) :=
    ((Matrix.toEuclideanCLM (n := R.model) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom :
      Matrix R.model R.model ℂ →ₗ[ℂ]
        (EuclideanSpace ℂ R.model →L[ℂ] EuclideanSpace ℂ R.model))
  let eop := op.comp R.expectation
  have heopCP : IsCompletelyPositive eop :=
    (isCompletelyPositive_of_starAlgHom
      (Matrix.toEuclideanCLM (n := R.model) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom).comp
        R.expectation_completelyPositive
  have heopOne : eop 1 = 1 := by
    change Matrix.toEuclideanCLM (n := R.model) (𝕜 := ℂ) (R.expectation 1) = 1
    rw [R.expectation_one, map_one]
  have hcontract := heopCP.norm_apply_le_of_unital heopOne T
  have hinclude : ‖R.embedding (R.retract T)‖ = ‖R.retract T‖ :=
    NonUnitalStarAlgHom.norm_map R.embedding.toNonUnitalStarAlgHom
      R.embedding_injective (R.retract T)
  calc
    ‖R.retract T‖ = ‖R.embedding (R.retract T)‖ := hinclude.symm
    _ = ‖R.expectation T‖ := rfl
    _ = ‖eop T‖ := by
      change ‖R.expectation T‖ =
        ‖Matrix.toEuclideanCLM (n := R.model) (𝕜 := ℂ) (R.expectation T)‖
      exact (Matrix.l2_opNorm_toEuclideanCLM (R.expectation T)).symm
    _ ≤ ‖T‖ := hcontract

/-! ## Products and the `Fin (n+1)` splitting -/

/-- Product of two complex-linear maps. -/
def prodLinearMap
    {A B C D : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [AddCommMonoid C] [AddCommMonoid D]
    [Module ℂ A] [Module ℂ B] [Module ℂ C] [Module ℂ D]
    (f : A →ₗ[ℂ] C) (g : B →ₗ[ℂ] D) :
    (A × B) →ₗ[ℂ] (C × D) where
  toFun x := (f x.1, g x.2)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Products preserve complete positivity. -/
theorem isCompletelyPositive_prodLinearMap
    {A B C D : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    {f : A →ₗ[ℂ] C} {g : B →ₗ[ℂ] D}
    (hf : IsCompletelyPositive f) (hg : IsCompletelyPositive g) :
    IsCompletelyPositive (prodLinearMap f g) := by
  intro n M hM
  let fstLM : (A × B) →ₗ[ℂ] A :=
    { toFun := Prod.fst
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let sndLM : (A × B) →ₗ[ℂ] B :=
    { toFun := Prod.snd
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  obtain ⟨N, rfl⟩ := hM
  have hfstPos : ∃ P : CStarMatrix (Fin n) (Fin n) C,
      (star N * N).map ⇑(f.comp fstLM) = star P * P :=
    hf n ((star N * N).map ⇑fstLM) ⟨N.map Prod.fst, by
      ext i j
      change fstLM ((star N * N) i j) =
        (star (N.map Prod.fst) * N.map Prod.fst) i j
      rw [cstarMatrix_mul_apply, cstarMatrix_mul_apply]
      simp only [cstarMatrix_star_apply]
      rw [map_sum]
      rfl⟩
  have hsndPos : ∃ Q : CStarMatrix (Fin n) (Fin n) D,
      (star N * N).map ⇑(g.comp sndLM) = star Q * Q :=
    hg n ((star N * N).map ⇑sndLM) ⟨N.map Prod.snd, by
      ext i j
      change sndLM ((star N * N) i j) =
        (star (N.map Prod.snd) * N.map Prod.snd) i j
      rw [cstarMatrix_mul_apply, cstarMatrix_mul_apply]
      simp only [cstarMatrix_star_apply]
      rw [map_sum]
      rfl⟩
  obtain ⟨P, hP⟩ := hfstPos
  obtain ⟨Q, hQ⟩ := hsndPos
  let R : CStarMatrix (Fin n) (Fin n) (C × D) := fun i j ↦ (P i j, Q i j)
  refine ⟨R, ?_⟩
  funext i j
  apply Prod.ext
  · calc
      (((star N * N).map ⇑(prodLinearMap f g)) i j).1 =
          (((star N * N).map ⇑(f.comp fstLM)) i j) := rfl
      _ = (star P * P) i j := congrFun (congrFun hP i) j
      _ = ((star R * R) i j).1 := by
        let fstAH : (C × D) →+ C :=
          { toFun := Prod.fst
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        rw [cstarMatrix_mul_apply, cstarMatrix_mul_apply]
        simp only [cstarMatrix_star_apply]
        change (∑ x, star (P x i) * P x j) =
          fstAH (∑ x, star (R x i) * R x j)
        rw [map_sum]
        rfl
  · calc
      (((star N * N).map ⇑(prodLinearMap f g)) i j).2 =
          (((star N * N).map ⇑(g.comp sndLM)) i j) := rfl
      _ = (star Q * Q) i j := congrFun (congrFun hQ i) j
      _ = ((star R * R) i j).2 := by
        let sndAH : (C × D) →+ D :=
          { toFun := Prod.snd
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        rw [cstarMatrix_mul_apply, cstarMatrix_mul_apply]
        simp only [cstarMatrix_star_apply]
        change (∑ x, star (Q x i) * Q x j) =
          sndAH (∑ x, star (R x i) * R x j)
        rw [map_sum]
        rfl

/-- Split a dependent product over `Fin (n+1)` into its first coordinate and
the remaining dependent product. -/
def directMatrixSumSuccStarAlgEquiv (n : ℕ) (d : Fin (n + 1) → ℕ) :
    DirectMatrixSum d ≃⋆ₐ[ℂ]
      (Matrix (Fin (d 0)) (Fin (d 0)) ℂ ×
        DirectMatrixSum (fun i : Fin n ↦ d i.succ)) where
  toFun x := (x 0, fun i ↦ x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by funext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  right_inv x := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_mul' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl
  map_star' x := by ext <;> rfl

/-- The one-coordinate dependent product is its unique matrix block. -/
def directMatrixSumOneStarAlgEquiv (d : Fin 1 → ℕ) :
    DirectMatrixSum d ≃⋆ₐ[ℂ] Matrix (Fin (d 0)) (Fin (d 0)) ℂ where
  toFun x := x 0
  invFun T := fun i ↦ (Fin.eq_zero i).symm ▸ T
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j ↦ j.elim0) i
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- Apply a star homomorphism in the second coordinate of a product. -/
def prodSecondStarAlgHom
    {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]
    [StarRing A] [StarRing B] [StarRing C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
    (f : B →⋆ₐ[ℂ] C) : (A × B) →⋆ₐ[ℂ] (A × C) where
  toFun x := (x.1, f x.2)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by simp
  commutes' c := Prod.ext rfl (f.commutes c)
  map_star' x := Prod.ext rfl (map_star f x.2)

/-! ## Iterating the binary retract -/

/-- Every nonempty finite direct product of nonzero full matrix blocks is a
UCP retract of one full matrix algebra. -/
theorem exists_matrixUCPRetract_directMatrixSum_succ
    (n : ℕ) (d : Fin (n + 1) → ℕ)
    [hne : ∀ i, Nonempty (Fin (d i))] :
    Nonempty (MatrixUCPRetract (DirectMatrixSum d)) := by
  induction n with
  | zero =>
      let e := directMatrixSumOneStarAlgEquiv d
      let ret : Matrix (Fin (d 0)) (Fin (d 0)) ℂ →ₗ[ℂ] DirectMatrixSum d :=
        e.symm.toAlgEquiv.toLinearEquiv.toLinearMap
      refine ⟨{
        model := Fin (d 0)
        embedding := e.toStarAlgHom
        retract := ret
        retract_completelyPositive :=
          isCompletelyPositive_of_starAlgHom e.symm.toStarAlgHom.toNonUnitalStarAlgHom
        retract_embedding := fun x ↦ e.symm_apply_apply x
        retract_one := by simp [ret] }⟩
  | succ n ih =>
      let dt : Fin (n + 1) → ℕ := fun i ↦ d i.succ
      let hnet : ∀ i, Nonempty (Fin (dt i)) := fun i ↦ hne i.succ
      letI : ∀ i, Nonempty (Fin (dt i)) := hnet
      obtain ⟨Rt⟩ := ih dt
      let Y : FiniteModel := naturalFiniteModel (d 0)
      let Z : FiniteModel :=
        ⟨Rt.model, Rt.fintype, Rt.decidableEq⟩
      letI : Nonempty Y := hne 0
      letI : Nonempty Z := Rt.modelNonempty
      let split := directMatrixSumSuccStarAlgEquiv (n + 1) d
      let middle :
          (Matrix Y Y ℂ × DirectMatrixSum dt) →⋆ₐ[ℂ]
            (Matrix Y Y ℂ × Matrix Z Z ℂ) :=
        prodSecondStarAlgHom Rt.embedding
      let inc : DirectMatrixSum d →⋆ₐ[ℂ] Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ :=
        (binaryBlockDiagStarAlgHom Y Z).comp (middle.comp split.toStarAlgHom)
      let backMiddle : (Matrix Y Y ℂ × Matrix Z Z ℂ) →ₗ[ℂ]
          (Matrix Y Y ℂ × DirectMatrixSum dt) :=
        prodLinearMap LinearMap.id Rt.retract
      let ret : Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ →ₗ[ℂ] DirectMatrixSum d :=
        (split.symm.toAlgEquiv.toLinearEquiv.toLinearMap).comp
          (backMiddle.comp (binaryBlockRetraction Y Z))
      refine ⟨{
        model := Y ⊕ Z
        embedding := inc
        retract := ret
        retract_completelyPositive :=
          (isCompletelyPositive_of_starAlgHom
            split.symm.toStarAlgHom.toNonUnitalStarAlgHom).comp
              ((isCompletelyPositive_prodLinearMap isCompletelyPositive_id
                Rt.retract_completelyPositive).comp
                  (isCompletelyPositive_binaryBlockRetraction Y Z))
        retract_embedding := ?_
        retract_one := ?_ }⟩
      · intro x
        change split.symm
          (backMiddle
            (binaryBlockRetraction Y Z
              (binaryBlockDiagStarAlgHom Y Z (middle (split x))))) = x
        rw [binaryBlockRetraction_blockDiag]
        change split.symm
          ((split x).1, Rt.retract (Rt.embedding (split x).2)) = x
        rw [Rt.retract_embedding]
        exact split.symm_apply_apply x
      · change split.symm
          (backMiddle (binaryBlockRetraction Y Z 1)) = 1
        rw [binaryBlockRetraction_one]
        change split.symm (1, Rt.retract 1) = 1
        rw [Rt.retract_one]
        exact map_one split.symm

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms MatrixUCPRetract.retract_norm_le
#audit_axioms isCompletelyPositive_prodLinearMap
#audit_axioms exists_matrixUCPRetract_directMatrixSum_succ
