import GroupApproximation.Analysis.FaithfulTracialState
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Faithful traces on finite matrix amplifications

The normalized diagonal sum amplifies a faithful tracial state on a unital
complex C⋆-algebra to every nonempty finite matrix algebra.  Consequently,
every finite matrix amplification is finite in the operator-algebraic sense:
each isometry is unitary.
-/

open scoped ComplexOrder

namespace GroupApproximation

noncomputable section

namespace FaithfulTracialState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- The normalized diagonal trace induced on a nonempty finite matrix block. -/
def matrixDiagonalTrace (τ : FaithfulTracialState A) (n : Type*)
    [Fintype n] : CStarMatrix n n A →ₗ[ℂ] ℂ where
  toFun M := (Fintype.card n : ℂ)⁻¹ * ∑ i, τ (M i i)
  map_add' M N := by
    simp only [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib, mul_add]
  map_smul' c M := by
    simp only [CStarMatrix.smul_apply, map_smul, RingHom.id_apply]
    rw [← Finset.smul_sum]
    change (Fintype.card n : ℂ)⁻¹ * (c * ∑ i, τ (M i i)) =
      c * ((Fintype.card n : ℂ)⁻¹ * ∑ i, τ (M i i))
    ac_rfl

@[simp]
theorem matrixDiagonalTrace_apply (τ : FaithfulTracialState A) (n : Type*)
    [Fintype n] (M : CStarMatrix n n A) :
    τ.matrixDiagonalTrace n M = (Fintype.card n : ℂ)⁻¹ * ∑ i, τ (M i i) :=
  rfl

/-- A faithful tracial state amplifies to every nonempty finite matrix block. -/
def matrix (τ : FaithfulTracialState A) (n : Type*) [Fintype n] [DecidableEq n]
    (hn : Nonempty n) : FaithfulTracialState (CStarMatrix n n A) := by
  letI := hn
  exact {
  toLinearMap := τ.matrixDiagonalTrace n
  map_one := by
    simp only [matrixDiagonalTrace_apply, CStarMatrix.one_apply_eq, apply_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  map_star_mul_self_nonneg M := by
    simp only [matrixDiagonalTrace_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      map_sum]
    apply mul_nonneg
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact Finset.sum_nonneg fun i _ ↦
        Finset.sum_nonneg fun j _ ↦ τ.map_star_mul_self_nonneg (M j i)
  map_mul_comm M N := by
    simp only [matrixDiagonalTrace_apply, CStarMatrix.mul_apply, map_sum]
    congr 1
    calc
      (∑ i, ∑ j, τ (M i j * N j i)) = ∑ i, ∑ j, τ (N j i * M i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact τ.map_mul_comm _ _
      _ = ∑ j, ∑ i, τ (N j i * M i j) := Finset.sum_comm
  eq_zero_of_map_star_mul_self_eq_zero := by
    intro M hM
    apply CStarMatrix.ext
    intro i j
    have hscale : (Fintype.card n : ℂ)⁻¹ ≠ 0 := by
      exact inv_ne_zero (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))
    have hsum : ∑ k, ∑ l, τ (star (M l k) * M l k) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hscale
      simpa only [matrixDiagonalTrace_apply, CStarMatrix.mul_apply,
        CStarMatrix.star_apply, map_sum] using hM
    have hcolumn : ∑ l, τ (star (M l j) * M l j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦
        Finset.sum_nonneg fun l _ ↦ τ.map_star_mul_self_nonneg (M l k)).mp
          hsum j (Finset.mem_univ j)
    have hentry : τ (star (M i j) * M i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun l _ ↦
        τ.map_star_mul_self_nonneg (M l j)).mp hcolumn i (Finset.mem_univ i)
    exact τ.eq_zero_of_map_star_mul_self_eq_zero hentry }

/-- Every isometry in a finite matrix amplification is unitary. -/
theorem matrix_mul_star_eq_one_of_star_mul_eq_one (τ : FaithfulTracialState A)
    (n : Type*) [Fintype n] [DecidableEq n] (hn : Nonempty n)
    {v : CStarMatrix n n A} (hv : star v * v = 1) : v * star v = 1 :=
  (τ.matrix n hn).mul_star_eq_one_of_star_mul_eq_one hv

end FaithfulTracialState

end

end GroupApproximation
