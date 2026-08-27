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
    (S : V ≃ₗ[ℂ] V) {u : V} {lam : ℝ} (hLam : lam ≠ 0)
    (hu : S u = (lam : ℂ) • u) :
    S.symm u = (lam : ℂ)⁻¹ • u := by
  apply S.injective
  rw [S.apply_symm_apply, map_smul, hu, smul_smul]
  rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hLam), one_smul]

/-- Two orthonormal eigenvectors with eigenvalues of opposite sign give a
nonzero isotropic vector for the inverse quadratic form. -/
theorem exists_inverseForm_isotropic_of_opposite_eigenvalues
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (S : V ≃ₗ[ℂ] V) {u v : V} {lam mu : ℝ}
    (huu : inner ℂ u u = 1) (hvv : inner ℂ v v = 1)
    (huv : inner ℂ u v = 0) (hvu : inner ℂ v u = 0)
    (hSu : S u = (lam : ℂ) • u) (hSv : S v = (mu : ℂ) • v)
    (hLam : 0 < lam) (hMu : mu < 0) :
    ∃ w : V, w ≠ 0 ∧ inner ℂ w (S.symm w) = 0 := by
  let r : ℝ := Real.sqrt lam
  let s : ℝ := Real.sqrt (-mu)
  let w : V := (r : ℂ) • u + (s : ℂ) • v
  have hrpos : 0 < r := Real.sqrt_pos.2 hLam
  have hspos : 0 < s := Real.sqrt_pos.2 (neg_pos.mpr hMu)
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hrSq : r ^ 2 = lam := Real.sq_sqrt hLam.le
  have hsSq : s ^ 2 = -mu := Real.sq_sqrt (neg_nonneg.mpr hMu.le)
  have hSinvu : S.symm u = (lam : ℂ)⁻¹ • u :=
    symm_apply_eq_inv_smul_of_apply_eq_smul S hLam.ne' hSu
  have hSinvv : S.symm v = (mu : ℂ)⁻¹ • v :=
    symm_apply_eq_inv_smul_of_apply_eq_smul S hMu.ne hSv
  have hune : u ≠ 0 := by
    intro hu
    have hzeroOne : (0 : ℂ) = 1 := by
      calc
        0 = inner ℂ u u := by simp [hu]
        _ = 1 := huu
    exact zero_ne_one hzeroOne
  have hwne : w ≠ 0 := by
    intro hwzero
    have hinner := congrArg (fun z : V ↦ inner ℂ u z) hwzero
    have hrOrU : (r : ℂ) = 0 ∨ u = 0 := by
      simpa [w, inner_add_right, inner_smul_right, huu, huv] using hinner
    exact hrne (hrOrU.resolve_right hune)
  have hreal : r * (r * lam⁻¹) + s * (s * mu⁻¹) = 0 := by
    calc
      r * (r * lam⁻¹) + s * (s * mu⁻¹) =
          r ^ 2 * lam⁻¹ + s ^ 2 * mu⁻¹ := by ring
      _ = lam * lam⁻¹ + (-mu) * mu⁻¹ := by rw [hrSq, hsSq]
      _ = 0 := by
        field_simp [hLam.ne', hMu.ne]
        norm_num
  have hcomplex :
      (r : ℂ) * ((r : ℂ) * (lam : ℂ)⁻¹) +
        (s : ℂ) * ((s : ℂ) * (mu : ℂ)⁻¹) = 0 := by
    exact_mod_cast hreal
  have hSinvw : S.symm w =
      ((r : ℂ) * (lam : ℂ)⁻¹) • u +
        ((s : ℂ) * (mu : ℂ)⁻¹) • v := by
    dsimp [w]
    change S.symm ((r : ℂ) • u + (s : ℂ) • v) = _
    rw [map_add, map_smul, map_smul, hSinvu, hSinvv, smul_smul, smul_smul]
  have hstarR : star (r : ℂ) = (r : ℂ) := by
    exact Complex.conj_ofReal r
  have hstarS : star (s : ℂ) = (s : ℂ) := by
    exact Complex.conj_ofReal s
  refine ⟨w, hwne, ?_⟩
  rw [hSinvw]
  change inner ℂ ((r : ℂ) • u + (s : ℂ) • v)
      (((r : ℂ) * (lam : ℂ)⁻¹) • u +
        ((s : ℂ) * (mu : ℂ)⁻¹) • v) = 0
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply]
  rw [hstarR, hstarS, huu, hvv, huv, hvu]
  simp only [mul_zero, add_zero, zero_add, mul_one]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcomplex

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
  let lam := hS.eigenvalues rfl i
  let mu := hS.eigenvalues rfl j
  have hij : i ≠ j := by
    intro hij
    subst j
    have hsquare : 0 ≤ hS.eigenvalues rfl i * hS.eigenvalues rfl i :=
      mul_self_nonneg _
    exact (not_lt_of_ge hsquare) hprod
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
    simp [Ne.symm hij]
  have hSi : S (b i) = (lam : ℂ) • b i := by
    change S ((hS.eigenvectorBasis rfl) i) =
      (hS.eigenvalues rfl i : ℂ) • (hS.eigenvectorBasis rfl) i
    exact hS.apply_eigenvectorBasis rfl i
  have hSj : S (b j) = (mu : ℂ) • b j := by
    change S ((hS.eigenvectorBasis rfl) j) =
      (hS.eigenvalues rfl j : ℂ) • (hS.eigenvectorBasis rfl) j
    exact hS.apply_eigenvectorBasis rfl j
  rcases mul_neg_iff.mp hprod with hposneg | hnegpos
  · obtain ⟨w, hw, hiso⟩ :=
      exists_inverseForm_isotropic_of_opposite_eigenvalues S huu hvv huv hvu
        hSi hSj hposneg.1 hposneg.2
    exact haniso w hw hiso
  · obtain ⟨w, hw, hiso⟩ :=
      exists_inverseForm_isotropic_of_opposite_eigenvalues S hvv huu hvu huv
        hSj hSi hnegpos.2 hnegpos.1
    exact haniso w hw hiso

/-- Every spectral value of an invertible self-adjoint operator is nonzero. -/
theorem eigenvalues_ne_zero_of_linearEquiv
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (S : V ≃ₗ[ℂ] V) (hS : S.toLinearMap.IsSymmetric) :
    ∀ i : Fin (Module.finrank ℂ V), hS.eigenvalues rfl i ≠ 0 := by
  intro i hi
  let b := hS.eigenvectorBasis rfl
  have hnorm : inner ℂ (b i) (b i) = 1 := by
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp
  have hSi : S (b i) = (hS.eigenvalues rfl i : ℂ) • b i := by
    change S ((hS.eigenvectorBasis rfl) i) =
      (hS.eigenvalues rfl i : ℂ) • (hS.eigenvectorBasis rfl) i
    exact hS.apply_eigenvectorBasis rfl i
  have hbi : b i = 0 := by
    apply S.injective
    simpa [hi] using hSi
  have hzeroOne : (0 : ℂ) = 1 := by
    calc
      0 = inner ℂ (b i) (b i) := by simp [hbi]
      _ = 1 := hnorm
  exact zero_ne_one hzeroOne

/-- On a nonzero finite-dimensional space, anisotropy of the inverse quadratic
form forces all eigenvalues of an invertible self-adjoint operator to be
strictly positive or all to be strictly negative. -/
theorem eigenvalues_all_positive_or_all_negative_of_inverseForm_anisotropic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (S : V ≃ₗ[ℂ] V) (hS : S.toLinearMap.IsSymmetric)
    (haniso : ∀ w : V, w ≠ 0 → inner ℂ w (S.symm w) ≠ 0) :
    (∀ i : Fin (Module.finrank ℂ V), 0 < hS.eigenvalues rfl i) ∨
      (∀ i : Fin (Module.finrank ℂ V), hS.eigenvalues rfl i < 0) := by
  have hpair :=
    eigenvalues_pairwise_mul_nonneg_of_inverseForm_anisotropic S hS haniso
  have hne := eigenvalues_ne_zero_of_linearEquiv S hS
  have hdim : 0 < Module.finrank ℂ V := Module.finrank_pos
  let i₀ : Fin (Module.finrank ℂ V) := ⟨0, hdim⟩
  rcases lt_or_gt_of_ne (hne i₀) with hi₀neg | hi₀pos
  · right
    intro j
    rcases lt_or_gt_of_ne (hne j) with hjneg | hjpos
    · exact hjneg
    · have := hpair i₀ j
      nlinarith
  · left
    intro j
    rcases lt_or_gt_of_ne (hne j) with hjneg | hjpos
    · have := hpair i₀ j
      nlinarith
    · exact hjpos

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms symm_apply_eq_inv_smul_of_apply_eq_smul
#audit_axioms exists_inverseForm_isotropic_of_opposite_eigenvalues
#audit_axioms eigenvalues_pairwise_mul_nonneg_of_inverseForm_anisotropic
#audit_axioms eigenvalues_ne_zero_of_linearEquiv
#audit_axioms eigenvalues_all_positive_or_all_negative_of_inverseForm_anisotropic
