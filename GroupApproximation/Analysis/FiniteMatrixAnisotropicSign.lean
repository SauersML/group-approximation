import GroupApproximation.Analysis.FiniteMatrixTransportedInvolution
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Anisotropic self-adjoint operators have one spectral sign

This file isolates the pure finite-dimensional spectral step in the
Blackadar--Kirchberg normalization argument.  Opposite-sign eigenvalues of
an invertible self-adjoint operator produce an explicit nonzero vector that
is isotropic for the inverse quadratic form.  Hence anisotropy forces all
eigenvalues to have the same sign.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

noncomputable section

/-- An eigenvector of an invertible operator remains an eigenvector of its
inverse, with reciprocal eigenvalue. -/
theorem symm_apply_eq_inv_smul_of_apply_eq_smul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (S : V ≃ₗ[ℂ] V) {u : V} {λ : ℝ} (hλ : λ ≠ 0)
    (hu : S u = (λ : ℂ) • u) :
    S.symm u = ((λ : ℂ)⁻¹ • u := by
  apply S.injective
  rw [S.apply_symm_apply, map_smul, hu, smul_smul]
  rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hλ), one_smul]

/-- Two orthonormal eigenvectors with eigenvalues of opposite sign give a
nonzero isotropic vector for the inverse quadratic form. -/
theorem exists_inverseForm_isotropic_of_opposite_eigenvalues
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (S : V ≃ₗ[ℂ] V) {u v : V} {λ μ : ℝ}
    (huu : inner ℂ u u = 1) (hvv : inner ℂ v v = 1)
    (huv : inner ℂ u v = 0) (hvu : inner ℂ v u = 0)
    (hSu : S u = (λ : ℂ) • u) (hSv : S v = (μ : ℂ) • v)
    (hλ : 0 < λ) (hμ : μ < 0) :
    ∃ w : V, w ≠ 0 ∧ inner ℂ w (S.symm w) = 0 := by
  let r : ℝ := Real.sqrt λ
  let s : ℝ := Real.sqrt (-μ)
  let w : V := (r : ℂ) • u + (s : ℂ) • v
  have hrpos : 0 < r := Real.sqrt_pos.2 hλ
  have hspos : 0 < s := Real.sqrt_pos.2 (neg_pos.mpr hμ)
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hrSq : r ^ 2 = λ := Real.sq_sqrt hλ.le
  have hsSq : s ^ 2 = -μ := Real.sq_sqrt (neg_nonneg.mpr hμ.le)
  have hSinvu : S.symm u = ((λ : ℂ)⁻¹ • u :=
    symm_apply_eq_inv_smul_of_apply_eq_smul S hλ.ne' hSu
  have hSinvv : S.symm v = ((μ : ℂ)⁻¹ • v :=
    symm_apply_eq_inv_smul_of_apply_eq_smul S hμ.ne hSv
  have hwne : w ≠ 0 := by
    intro hwzero
    have hinner := congrArg (fun z : V ↦ inner ℂ u z) hwzero
    have : (r : ℂ) = 0 := by
      simpa [w, inner_add_right, inner_smul_right, huu, huv] using hinner
    exact hrne this
  have hreal : r * (r * λ⁻¹) + s * (s * μ⁻¹) = 0 := by
    calc
      r * (r * λ⁻¹) + s * (s * μ⁻¹) =
          r ^ 2 * λ⁻¹ + s ^ 2 * μ⁻¹ := by ring
      _ = λ * λ⁻¹ + (-μ) * μ⁻¹ := by rw [hrSq, hsSq]
      _ = 0 := by field_simp [hλ.ne', hμ.ne]
  have hcomplex :
      (r : ℂ) * ((r : ℂ) * (λ : ℂ)⁻¹) +
        (s : ℂ) * ((s : ℂ) * (μ : ℂ)⁻¹) = 0 := by
    exact_mod_cast hreal
  refine ⟨w, hwne, ?_⟩
  simp only [w, map_add, map_smul, hSinvu, hSinvv, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, smul_smul,
    starRingEnd_apply, map_ofReal, huu, hvv, huv, hvu, mul_zero,
    add_zero, zero_mul, zero_add, mul_one]
  exact hcomplex

/-- An anisotropic inverse quadratic form rules out opposite signs among
the eigenvalues in the orthonormal eigenbasis of a self-adjoint operator. -/
theorem eigenvalues_pairwise_mul_nonneg_of_inverseForm_anisotropic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (S : V ≃ₗ[ℂ] V) (hS : S.toLinearMap.IsSymmetric)
    (haniso : ∀ w : V, w ≠ 0 → inner ℂ w (S.symm w) ≠ 0) :
    ∀ i j : Fin (Module.finrank ℂ V),
      0 ≤ hS.eigenvalues rfl i * hS.eigenvalues rfl j := by
  intro i j
  by_contra hnonneg
  have hprod : hS.eigenvalues rfl i * hS.eigenvalues rfl j < 0 :=
    lt_of_not_ge hnonneg
  let b := hS.eigenvectorBasis rfl
  let λ := hS.eigenvalues rfl i
  let μ := hS.eigenvalues rfl j
  have hij : i ≠ j := by
    intro hij
    subst j
    exact (not_lt_of_ge (sq_nonneg (hS.eigenvalues rfl i))) hprod
  have huu : inner ℂ (b i) (b i) = 1 := by
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp
  have hvv : inner ℂ (b j) (b j) = 1 := by
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp
  have huv : inner ℂ (b i) (b j) = 0 := by
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [hij]
  have hvu : inner ℂ (b j) (b i) = 0 := by
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [hij]
  have hSi : S (b i) = (λ : ℂ) • b i := by
    simpa [b, λ] using hS.apply_eigenvectorBasis rfl i
  have hSj : S (b j) = (μ : ℂ) • b j := by
    simpa [b, μ] using hS.apply_eigenvectorBasis rfl j
  rcases mul_neg_iff.mp hprod with hposneg | hnegpos
  · obtain ⟨w, hw, hiso⟩ :=
      exists_inverseForm_isotropic_of_opposite_eigenvalues S huu hvv huv hvu
        hSi hSj hposneg.1 hposneg.2
    exact haniso w hw hiso
  · obtain ⟨w, hw, hiso⟩ :=
      exists_inverseForm_isotropic_of_opposite_eigenvalues S hvv huu hvu huv
        hSj hSi hnegpos.2 hnegpos.1
    exact haniso w hw hiso

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms symm_apply_eq_inv_smul_of_apply_eq_smul
#audit_axioms exists_inverseForm_isotropic_of_opposite_eigenvalues
#audit_axioms eigenvalues_pairwise_mul_nonneg_of_inverseForm_anisotropic
