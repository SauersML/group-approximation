import GroupApproximation.Analysis.FiniteMatrixAnisotropicSign
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Sign normalization of anisotropic self-adjoint operators

This file turns the one-sign spectral conclusion into positivity of a signed
operator.  The proof records the quadratic form in an orthonormal eigenbasis,
so it does not require an additional finite-dimensional positivity theorem.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open scoped BigOperators

noncomputable section

/-- The quadratic form of a finite-dimensional self-adjoint operator is the
sum of its eigenvalues weighted by the squared norms of the corresponding
coordinates. -/
theorem inner_map_self_re_eq_sum_eigenvalues_mul_normSq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (hT : T.IsSymmetric) (x : V) :
    (inner ℂ x (T x)).re =
      ∑ i : Fin (Module.finrank ℂ V),
        hT.eigenvalues rfl i *
          Complex.normSq (inner ℂ ((hT.eigenvectorBasis rfl) i) x) := by
  let b := hT.eigenvectorBasis rfl
  have hEigen (i : Fin (Module.finrank ℂ V)) :
      T (b i) = (hT.eigenvalues rfl i : ℂ) • b i := by
    change T ((hT.eigenvectorBasis rfl) i) =
      (hT.eigenvalues rfl i : ℂ) • (hT.eigenvectorBasis rfl) i
    exact hT.apply_eigenvectorBasis rfl i
  have hTx : T x =
      ∑ i : Fin (Module.finrank ℂ V),
        (inner ℂ (b i) x * (hT.eigenvalues rfl i : ℂ)) • b i := by
    calc
      T x = T (∑ i : Fin (Module.finrank ℂ V), inner ℂ (b i) x • b i) := by
        rw [b.sum_repr']
      _ = ∑ i : Fin (Module.finrank ℂ V),
          T (inner ℂ (b i) x • b i) := by rw [map_sum]
      _ = ∑ i : Fin (Module.finrank ℂ V),
          (inner ℂ (b i) x * (hT.eigenvalues rfl i : ℂ)) • b i := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_smul, hEigen, smul_smul]
  rw [hTx, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_smul_right]
  have hconj : inner ℂ x (b i) =
      (starRingEnd ℂ) (inner ℂ (b i) x) := (inner_conj_symm x (b i)).symm
  rw [hconj, starRingEnd_apply, Complex.star_def]
  have hrearrange :
      (inner ℂ (b i) x * (hT.eigenvalues rfl i : ℂ)) *
          (inner ℂ (b i) x).conj =
        (hT.eigenvalues rfl i : ℂ) *
          (inner ℂ (b i) x * (inner ℂ (b i) x).conj) := by
    ring
  rw [hrearrange, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Nonnegative eigenvalues give a nonnegative quadratic form. -/
theorem inner_map_self_re_nonneg_of_eigenvalues_nonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (hT : T.IsSymmetric)
    (heigen : ∀ i : Fin (Module.finrank ℂ V), 0 ≤ hT.eigenvalues rfl i) :
    ∀ x : V, 0 ≤ (inner ℂ x (T x)).re := by
  intro x
  rw [inner_map_self_re_eq_sum_eigenvalues_mul_normSq T hT x]
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (heigen i) (Complex.normSq_nonneg _)

/-- If an invertible self-adjoint operator has anisotropic inverse form, then
multiplication by one of the two real signs makes it symmetric with
nonnegative quadratic form. -/
theorem exists_sign_normalization_isSymmetric_and_form_nonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (S : V ≃ₗ[ℂ] V) (hS : S.toLinearMap.IsSymmetric)
    (haniso : ∀ w : V, w ≠ 0 → inner ℂ w (S.symm w) ≠ 0) :
    ∃ sign : ℝ,
      (sign = 1 ∨ sign = -1) ∧
      (((sign : ℂ) • S.toLinearMap).IsSymmetric ∧
        ∀ x : V, 0 ≤
          (inner ℂ x (((sign : ℂ) • S.toLinearMap) x)).re) := by
  rcases
      eigenvalues_all_positive_or_all_negative_of_inverseForm_anisotropic
        S hS haniso with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · simpa using hS
    · simpa using
        inner_map_self_re_nonneg_of_eigenvalues_nonneg S.toLinearMap hS
          (fun i ↦ (hpos i).le)
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · intro x y
      simpa using congrArg Neg.neg (hS x y)
    · intro x
      have hminus :
          ((((-1 : ℝ) : ℂ) • S.toLinearMap) x) = -(S x) := by
        change (-1 : ℂ) • S x = -(S x)
        exact neg_one_smul ℂ (S x)
      rw [hminus, inner_neg_right, Complex.neg_re,
        inner_map_self_re_eq_sum_eigenvalues_mul_normSq S.toLinearMap hS x,
        ← Finset.sum_neg_distrib]
      exact Finset.sum_nonneg fun i _ ↦
        mul_nonneg (neg_nonneg.mpr (hneg i).le) (Complex.normSq_nonneg _)

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms inner_map_self_re_eq_sum_eigenvalues_mul_normSq
#audit_axioms inner_map_self_re_nonneg_of_eigenvalues_nonneg
#audit_axioms exists_sign_normalization_isSymmetric_and_form_nonneg
