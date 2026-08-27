import GroupApproximation.Analysis.ShulmanTraceClasses
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Matrix core for tensor synchronization

This small module isolates the finite-matrix calculations used by tensor
synchronization: normalized diagonal amplification of a tracial state and
weighted permutation matrices.  Keeping it independent of the reduced-product
assembly gives the remote checker a narrow foundational target.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationMatrixCore

open scoped ComplexOrder

noncomputable section

universe u v

/-! ## Normalized diagonal traces -/

/-- The normalized diagonal linear functional induced by a tracial state. -/
def matrixDiagonalTrace {A : Type u} [CStarAlgebra A]
    (tau : TracialState A) (I : Type v) [Fintype I] :
    CStarMatrix I I A →ₗ[ℂ] ℂ where
  toFun M := (Fintype.card I : ℂ)⁻¹ * ∑ i, tau (M i i)
  map_add' M N := by
    simp only [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib, mul_add]
  map_smul' c M := by
    simp only [CStarMatrix.smul_apply, map_smul, RingHom.id_apply]
    rw [← Finset.smul_sum]
    change (Fintype.card I : ℂ)⁻¹ * (c * ∑ i, tau (M i i)) =
      c * ((Fintype.card I : ℂ)⁻¹ * ∑ i, tau (M i i))
    ac_rfl

@[simp] theorem matrixDiagonalTrace_apply
    {A : Type u} [CStarAlgebra A] (tau : TracialState A)
    (I : Type v) [Fintype I] (M : CStarMatrix I I A) :
    matrixDiagonalTrace tau I M =
      (Fintype.card I : ℂ)⁻¹ * ∑ i, tau (M i i) :=
  rfl

/-- The normalized diagonal amplification of an arbitrary tracial state. -/
def matrixTracialState {A : Type u} [CStarAlgebra A]
    (tau : TracialState A) (I : Type v) [Fintype I] [DecidableEq I]
    (hI : Nonempty I) : TracialState (CStarMatrix I I A) := by
  letI := hI
  exact {
    toLinearMap := matrixDiagonalTrace tau I
    map_one := by
      simp only [matrixDiagonalTrace_apply, CStarMatrix.one_apply_eq,
        tau.apply_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    map_star_mul_self_nonneg M := by
      simp only [matrixDiagonalTrace_apply, CStarMatrix.mul_apply,
        CStarMatrix.star_apply, map_sum]
      apply mul_nonneg
      · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      · exact Finset.sum_nonneg fun i _ ↦
          Finset.sum_nonneg fun j _ ↦
            tau.map_star_mul_self_nonneg (M j i)
    map_mul_comm M N := by
      simp only [matrixDiagonalTrace_apply, CStarMatrix.mul_apply, map_sum]
      congr 1
      calc
        (∑ i, ∑ j, tau (M i j * N j i)) =
            ∑ i, ∑ j, tau (N j i * M i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact tau.map_mul_comm _ _
        _ = ∑ j, ∑ i, tau (N j i * M i j) := Finset.sum_comm }

@[simp] theorem matrixTracialState_apply
    {A : Type u} [CStarAlgebra A] (tau : TracialState A)
    (I : Type v) [Fintype I] [DecidableEq I] (hI : Nonempty I)
    (M : CStarMatrix I I A) :
    matrixTracialState tau I hI M =
      (Fintype.card I : ℂ)⁻¹ * ∑ i, tau (M i i) :=
  rfl

/-! ## Weighted permutation matrices -/

/-- A permutation matrix whose nonzero entry in every row is `a`. -/
def weightedPermutationMatrix {A : Type u} [CStarAlgebra A]
    {I : Type v} [Fintype I] [DecidableEq I]
    (a : A) (p : Equiv.Perm I) : CStarMatrix I I A :=
  fun i j ↦ if p⁻¹ i = j then a else 0

@[simp] theorem weightedPermutationMatrix_apply
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I] [DecidableEq I]
    (a : A) (p : Equiv.Perm I) (i j : I) :
    weightedPermutationMatrix a p i j = if p⁻¹ i = j then a else 0 :=
  rfl

theorem weightedPermutationMatrix_mul
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I] [DecidableEq I]
    (a b : A) (p q : Equiv.Perm I) :
    weightedPermutationMatrix a p * weightedPermutationMatrix b q =
      weightedPermutationMatrix (a * b) (p * q) := by
  classical
  ext i k
  rw [CStarMatrix.mul_apply, Finset.sum_eq_single (p⁻¹ i)]
  · simp [weightedPermutationMatrix, _root_.mul_inv_rev,
      Equiv.Perm.mul_apply]
  · intro j _ hj
    have hzero : weightedPermutationMatrix a p i j = 0 := by
      rw [weightedPermutationMatrix_apply, if_neg]
      intro hji
      exact hj hji.symm
    rw [hzero, zero_mul]
  · simp

@[simp] theorem weightedPermutationMatrix_one
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    [DecidableEq I] :
    weightedPermutationMatrix (1 : A) (1 : Equiv.Perm I) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [weightedPermutationMatrix]
  · simp [weightedPermutationMatrix, h]

theorem weightedPermutationMatrix_star
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I] [DecidableEq I]
    (a : A) (p : Equiv.Perm I) :
    star (weightedPermutationMatrix a p) =
      weightedPermutationMatrix (star a) p⁻¹ := by
  classical
  ext i j
  by_cases h : p i = j
  · have hinv : p⁻¹ j = i := by
      calc
        p⁻¹ j = p⁻¹ (p i) :=
          congrArg (p⁻¹ : Equiv.Perm I) h.symm
        _ = i := p.symm_apply_apply i
    have htarget : ((p⁻¹ : Equiv.Perm I)⁻¹) i = j := by
      simpa using h
    rw [CStarMatrix.star_apply, weightedPermutationMatrix_apply,
      weightedPermutationMatrix_apply, if_pos hinv, if_pos htarget]
  · have hinv : p⁻¹ j ≠ i := by
      intro hij
      have hji : j = p i := by
        calc
          j = p (p⁻¹ j) := (p.apply_symm_apply j).symm
          _ = p i := congrArg p hij
      exact h hji.symm
    have htarget : ((p⁻¹ : Equiv.Perm I)⁻¹) i ≠ j := by
      simpa using h
    rw [CStarMatrix.star_apply, weightedPermutationMatrix_apply,
      weightedPermutationMatrix_apply, if_neg hinv, if_neg htarget, star_zero]

/-- A unitary coefficient and a permutation give a unitary weighted
permutation matrix. -/
def weightedPermutationUnitary
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    [DecidableEq I] (a : unitary A) (p : Equiv.Perm I) :
    unitary (CStarMatrix I I A) :=
  ⟨weightedPermutationMatrix (a : A) p, by
    constructor
    · rw [weightedPermutationMatrix_star, weightedPermutationMatrix_mul,
        a.property.1, inv_mul_cancel, weightedPermutationMatrix_one]
    · rw [weightedPermutationMatrix_star, weightedPermutationMatrix_mul,
        a.property.2, mul_inv_cancel, weightedPermutationMatrix_one]⟩

@[simp] theorem coe_weightedPermutationUnitary
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    [DecidableEq I] (a : unitary A) (p : Equiv.Perm I) :
    (weightedPermutationUnitary a p : CStarMatrix I I A) =
      weightedPermutationMatrix (a : A) p :=
  rfl

end

end TensorSynchronizationMatrixCore
end OneSidedMFRadical
end Manuscript
end GroupApproximation
