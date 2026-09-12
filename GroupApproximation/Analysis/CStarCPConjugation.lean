import GroupApproximation.Analysis.CStarExactness

/-!
# Completely positive inner multipliers

The map `a ↦ c⋆ a c` is completely positive.  This elementary matrix
factorization is the reusable ingredient behind the partition-of-unity
interpolation maps and the antipodal averaging map.
-/

namespace GroupApproximation
namespace CStarExactness

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The linear inner multiplier `a ↦ c⋆ a c`. -/
def conjugationLinearMap (c : A) : A →ₗ[ℂ] A where
  toFun a := star c * a * c
  map_add' a b := by noncomm_ring
  map_smul' z a := by
    rw [RingHom.id_apply]
    rw [mul_smul_comm z (star c) a,
      smul_mul_assoc z (star c * a) c]

@[simp] theorem conjugationLinearMap_apply (c a : A) :
    conjugationLinearMap c a = star c * a * c := rfl

/-- Inner multiplication by `c⋆` and `c` is completely positive. -/
theorem isCompletelyPositive_conjugationLinearMap (c : A) :
    IsCompletelyPositive (conjugationLinearMap c) := by
  intro n M hM
  obtain ⟨N, rfl⟩ := hM
  let P : CStarMatrix (Fin n) (Fin n) A := fun i j ↦ N i j * c
  refine ⟨P, ?_⟩
  ext i j
  rw [CStarMatrix.map_apply, CStarMatrix.mul_apply, CStarMatrix.mul_apply]
  simp only [CStarMatrix.star_apply, conjugationLinearMap_apply, P, star_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  noncomm_ring

end

end CStarExactness
end GroupApproximation
