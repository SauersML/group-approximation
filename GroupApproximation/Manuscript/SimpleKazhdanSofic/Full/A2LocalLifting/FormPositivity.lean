import GroupApproximation.Analysis.CStarCompletelyPositiveForm
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Meta.AxiomGuard

/-!
# Completely positive operator models are form-positive matrix models (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.54–56 (table row A2): Ozawa's remark that the
full C⋆-algebra of an infinite simple hyperlinear Kazhdan group has no local lifting property.  The
factorization-through-local-lifting step extends local lifts by Arveson's theorem, whose output
lives in `B(ℓ²(Fin |Y|))`, and feeds the result to `Quasidiagonal.AmenableTraceModel`, which wants
matrices over `Y`, completely positive in the form sense.

* `matrixOfEuclidean Y`: the inverse of `Quasidiagonal.euclideanize Y`, i.e. the matrix of an
  operator on `ℓ²(Fin |Y|)`, reindexed to `Y`.
* `isCompletelyPositiveOnMatrices_matrixOfEuclidean`: if `Ψ` is completely positive then
  `matrixOfEuclidean Y ∘ Ψ` is form-positive.  Each form value is a form of `Ψ` at reindexed
  vectors, and `CStarExactness.IsCompletelyPositive.form_nonneg` makes it a real nonnegative
  number.

This is a fork, into lane `A2LocalLifting`, of the never-wired module
`Analysis/MatrixModelFormPositivity.lean` (left untouched).
-/

namespace GroupApproximation
namespace Full
namespace A2LocalLifting

open CStarExactness Quasidiagonal
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u

/-- The matrix of an operator on `ℓ²(Fin |Y|)`, reindexed to `Y`: the inverse of
`Quasidiagonal.euclideanize Y` (row A2, tex l.54–56). -/
def matrixOfEuclidean (Y : FiniteModel) :
    (EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card Y))) →ₗ[ℂ] Matrix Y Y ℂ where
  toFun T := (matrixReindexStarAlgEquiv (enum Y)).symm
    ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm T)
  map_add' S T := by simp
  map_smul' c T := by simp

theorem matrixOfEuclidean_apply (Y : FiniteModel)
    (T : EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card Y))) :
    matrixOfEuclidean Y T = (matrixReindexStarAlgEquiv (enum Y)).symm
      ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm T) := rfl

theorem euclideanize_matrixOfEuclidean (Y : FiniteModel)
    (T : EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card Y))) :
    euclideanize Y (matrixOfEuclidean Y T) = T := by
  rw [euclideanize_apply, matrixOfEuclidean_apply,
    StarAlgEquiv.apply_symm_apply, StarAlgEquiv.apply_symm_apply]

theorem matrixOfEuclidean_euclideanize (Y : FiniteModel) (M : Matrix Y Y ℂ) :
    matrixOfEuclidean Y (euclideanize Y M) = M := by
  rw [euclideanize_apply, matrixOfEuclidean_apply,
    StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply]

theorem matrixOfEuclidean_one (Y : FiniteModel) :
    matrixOfEuclidean Y 1 = 1 := by
  rw [matrixOfEuclidean_apply, map_one, map_one]

/-- A matrix form over `Y` is the operator form of its `euclideanize` at the reindexed
vectors. -/
theorem sum_form_eq_inner_euclideanize (Y : FiniteModel) (M : Matrix Y Y ℂ)
    (u v : Y → ℂ) :
    (∑ x : Y, ∑ y : Y, (starRingEnd ℂ) (u x) * M x y * v y)
      = ⟪(WithLp.toLp 2 fun p : Fin (Fintype.card Y) ↦ u ((enum Y).symm p) :
            EuclideanSpace ℂ (Fin (Fintype.card Y))),
          euclideanize Y M
            (WithLp.toLp 2 fun q : Fin (Fintype.card Y) ↦ v ((enum Y).symm q))⟫_ℂ := by
  rw [euclideanize_apply, inner_toEuclideanCLM_expand]
  symm
  calc (∑ p : Fin (Fintype.card Y), ∑ q : Fin (Fintype.card Y),
        (starRingEnd ℂ) (u ((enum Y).symm p))
          * (M ((enum Y).symm p) ((enum Y).symm q) * v ((enum Y).symm q)))
      = ∑ p : Fin (Fintype.card Y), ∑ y : Y,
          (starRingEnd ℂ) (u ((enum Y).symm p))
            * (M ((enum Y).symm p) y * v y) :=
        Finset.sum_congr rfl fun p _ ↦
          (enum Y).symm.sum_comp fun y : Y ↦
            (starRingEnd ℂ) (u ((enum Y).symm p))
              * (M ((enum Y).symm p) y * v y)
    _ = ∑ x : Y, ∑ y : Y, (starRingEnd ℂ) (u x) * (M x y * v y) :=
        (enum Y).symm.sum_comp fun x : Y ↦
          ∑ y : Y, (starRingEnd ℂ) (u x) * (M x y * v y)
    _ = ∑ x : Y, ∑ y : Y, (starRingEnd ℂ) (u x) * M x y * v y :=
        Finset.sum_congr rfl fun x _ ↦
          Finset.sum_congr rfl fun y _ ↦ (mul_assoc _ _ _).symm

/-- **Completely positive operator models are form-positive matrix models** (row A2,
tex l.54–56). -/
theorem isCompletelyPositiveOnMatrices_matrixOfEuclidean {A : Type u}
    [CStarAlgebra A] (Y : FiniteModel)
    (Ψ : A →ₗ[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card Y))))
    (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositiveOnMatrices Y (fun a : A ↦ matrixOfEuclidean Y (Ψ a)) := by
  intro m a w
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
    obtain ⟨hre, him⟩ := hΨ.form_nonneg a fun i ↦
      (WithLp.toLp 2 fun p : Fin (Fintype.card Y) ↦ w i ((enum Y).symm p) :
        EuclideanSpace ℂ (Fin (Fintype.card Y)))
    have hsum : (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
        (starRingEnd ℂ) (w i x) * matrixOfEuclidean Y (Ψ (star (a i) * a j)) x y
          * w j y)
        = ∑ i : Fin m, ∑ j : Fin m,
            ⟪(WithLp.toLp 2 fun p : Fin (Fintype.card Y) ↦ w i ((enum Y).symm p) :
                EuclideanSpace ℂ (Fin (Fintype.card Y))),
              Ψ (star (a i) * a j)
                (WithLp.toLp 2 fun q : Fin (Fintype.card Y) ↦ w j ((enum Y).symm q))⟫_ℂ := by
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [sum_form_eq_inner_euclideanize Y (matrixOfEuclidean Y (Ψ (star (a i) * a j)))
        (w i) (w j), euclideanize_matrixOfEuclidean]
    rw [hsum]
    exact ⟨him, hre⟩

end

end A2LocalLifting
end Full
end GroupApproximation

open GroupApproximation.Full.A2LocalLifting

#audit_closed_axioms isCompletelyPositiveOnMatrices_matrixOfEuclidean
