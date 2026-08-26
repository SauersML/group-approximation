import GroupApproximation.Analysis.FiniteMatrixSignNormalization
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Singular values under pointwise domination

This file supplies the finite-dimensional min--max comparison missing from
Mathlib's current singular-value API.  The proof uses the ordered
orthonormal eigenbases of `A.adjoint ∘ₗ A` and `B.adjoint ∘ₗ B`.
-/

namespace GroupApproximation

open scoped BigOperators

noncomputable section

namespace SingularValueOrder

open BlackadarKirchberg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
private theorem complex_re_inner_self_eq_norm_sq (x : E) :
    (inner ℂ x x).re = ‖x‖ ^ 2 := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) x
  simpa [RCLike.re_to_complex] using h

/-- On the span of eigenvectors with indices at most `k`, the quadratic form
is bounded below by the `k`-th eigenvalue. -/
theorem eigenvalue_mul_normSq_le_inner_of_mem_span_Iic
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (k : Fin (Module.finrank ℂ E)) (x : E)
    (hx : x ∈ Submodule.span ℂ
      ((hS.eigenvectorBasis rfl : Fin (Module.finrank ℂ E) → E) ''
        Set.Iic k)) :
    hS.eigenvalues rfl k * ‖x‖ ^ 2 ≤ (inner ℂ x (S x)).re := by
  let b := hS.eigenvectorBasis rfl
  have hsupp : ↑(b.toBasis.repr x).support ⊆ Set.Iic k :=
    b.toBasis.repr_support_subset_of_mem_span (Set.Iic k) hx
  rw [BlackadarKirchberg.inner_map_self_re_eq_sum_eigenvalues_mul_normSq S hS x]
  rw [← b.sum_sq_norm_inner_right x]
  simp_rw [Complex.normSq_eq_norm_sq]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hik : i ≤ k
  · simpa [b] using mul_le_mul_of_nonneg_right
      (hS.eigenvalues_antitone rfl hik)
      (sq_nonneg ‖inner ℂ (b i) x‖)
  · have hnotmem : i ∉ (b.toBasis.repr x).support := by
      intro himem
      exact hik (hsupp himem)
    have hzero : inner ℂ (b i) x = 0 := by
      have hcoord := Finsupp.notMem_support_iff.mp hnotmem
      rw [b.coe_toBasis_repr_apply, b.repr_apply_apply] at hcoord
      exact hcoord
    simp [b, hzero]

/-- On the span of eigenvectors with indices at least `k`, the quadratic form
is bounded above by the `k`-th eigenvalue. -/
theorem inner_le_eigenvalue_mul_normSq_of_mem_span_Ici
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (k : Fin (Module.finrank ℂ E)) (x : E)
    (hx : x ∈ Submodule.span ℂ
      ((hS.eigenvectorBasis rfl : Fin (Module.finrank ℂ E) → E) ''
        Set.Ici k)) :
    (inner ℂ x (S x)).re ≤ hS.eigenvalues rfl k * ‖x‖ ^ 2 := by
  let b := hS.eigenvectorBasis rfl
  have hsupp : ↑(b.toBasis.repr x).support ⊆ Set.Ici k :=
    b.toBasis.repr_support_subset_of_mem_span (Set.Ici k) hx
  rw [BlackadarKirchberg.inner_map_self_re_eq_sum_eigenvalues_mul_normSq S hS x]
  rw [← b.sum_sq_norm_inner_right x]
  simp_rw [Complex.normSq_eq_norm_sq]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hki : k ≤ i
  · simpa [b] using mul_le_mul_of_nonneg_right
      (hS.eigenvalues_antitone rfl hki)
      (sq_nonneg ‖inner ℂ (b i) x‖)
  · have hnotmem : i ∉ (b.toBasis.repr x).support := by
      intro himem
      exact hki (hsupp himem)
    have hzero : inner ℂ (b i) x = 0 := by
      have hcoord := Finsupp.notMem_support_iff.mp hnotmem
      rw [b.coe_toBasis_repr_apply, b.repr_apply_apply] at hcoord
      exact hcoord
    simp [b, hzero]

/-- The first `k+1` vectors in a basis span a space of dimension `k+1`. -/
omit [FiniteDimensional ℂ E] in
theorem finrank_span_basis_image_Iic
    (b : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E)
    (k : Fin (Module.finrank ℂ E)) :
    Module.finrank ℂ (Submodule.span ℂ (b '' Set.Iic k)) = k.1 + 1 := by
  let f : Set.Iic k → E := fun i ↦ b i.1
  have hf : LinearIndependent ℂ f :=
    b.linearIndependent.comp (fun i : Set.Iic k ↦ i.1) Subtype.val_injective
  have hrange : Set.range f = b '' Set.Iic k := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card hf]
  simp

/-- The basis vectors from `k` onward span a space of dimension `n-k`. -/
omit [FiniteDimensional ℂ E] in
theorem finrank_span_basis_image_Ici
    (b : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E)
    (k : Fin (Module.finrank ℂ E)) :
    Module.finrank ℂ (Submodule.span ℂ (b '' Set.Ici k)) =
      Module.finrank ℂ E - k.1 := by
  let f : Set.Ici k → E := fun i ↦ b i.1
  have hf : LinearIndependent ℂ f :=
    b.linearIndependent.comp (fun i : Set.Ici k ↦ i.1) Subtype.val_injective
  have hrange : Set.range f = b '' Set.Ici k := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← hrange, finrank_span_eq_card hf]
  simp

/-- The leading `S`-spectral subspace and trailing `T`-spectral subspace at
the same index have a nonzero intersection. -/
theorem exists_ne_zero_mem_eigenvector_spans
    (S T : E →ₗ[ℂ] E) (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (k : Fin (Module.finrank ℂ E)) :
    ∃ x : E, x ≠ 0 ∧
      x ∈ Submodule.span ℂ
        ((hS.eigenvectorBasis rfl : Fin (Module.finrank ℂ E) → E) '' Set.Iic k) ∧
      x ∈ Submodule.span ℂ
        ((hT.eigenvectorBasis rfl : Fin (Module.finrank ℂ E) → E) '' Set.Ici k) := by
  let P : Submodule ℂ E := Submodule.span ℂ
    ((hS.eigenvectorBasis rfl : Fin (Module.finrank ℂ E) → E) '' Set.Iic k)
  let Q : Submodule ℂ E := Submodule.span ℂ
    ((hT.eigenvectorBasis rfl : Fin (Module.finrank ℂ E) → E) '' Set.Ici k)
  have hP : Module.finrank ℂ P = k.1 + 1 := by
    exact finrank_span_basis_image_Iic (hS.eigenvectorBasis rfl).toBasis k
  have hQ : Module.finrank ℂ Q = Module.finrank ℂ E - k.1 := by
    exact finrank_span_basis_image_Ici (hT.eigenvectorBasis rfl).toBasis k
  have hsum : Module.finrank ℂ P + Module.finrank ℂ Q =
      Module.finrank ℂ E + 1 := by
    rw [hP, hQ]
    omega
  have hinfpos : 0 < Module.finrank ℂ (P ⊓ Q : Submodule ℂ E) := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq P Q
    have hsup : Module.finrank ℂ (P ⊔ Q : Submodule ℂ E) ≤
        Module.finrank ℂ E := Submodule.finrank_le _
    omega
  have hne : P ⊓ Q ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hinfpos
    omega
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨x, hxne, hxmem.1, hxmem.2⟩

/-- Loewner domination of two self-adjoint operators implies pointwise
domination of their ordered eigenvalue lists.  This is the finite-dimensional
min--max principle in the form needed for singular values. -/
theorem eigenvalues_le_of_quadraticForm_le
    (S T : E →ₗ[ℂ] E) (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hST : ∀ x : E, (inner ℂ x (S x)).re ≤ (inner ℂ x (T x)).re)
    (k : Fin (Module.finrank ℂ E)) :
    hS.eigenvalues rfl k ≤ hT.eigenvalues rfl k := by
  obtain ⟨x, hxne, hxS, hxT⟩ :=
    exists_ne_zero_mem_eigenvector_spans S T hS hT k
  have hnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hxne)
  have hlower := eigenvalue_mul_normSq_le_inner_of_mem_span_Iic S hS k x hxS
  have hupper := inner_le_eigenvalue_mul_normSq_of_mem_span_Ici T hT k x hxT
  nlinarith [hST x]

/-- Pointwise norm domination implies domination of the ordered singular
values. -/
theorem singularValues_le_of_norm_apply_le
    (A B : E →ₗ[ℂ] E) (hAB : ∀ x : E, ‖A x‖ ≤ ‖B x‖)
    (k : Fin (Module.finrank ℂ E)) :
    A.singularValues k ≤ B.singularValues k := by
  let S := A.adjoint ∘ₗ A
  let T := B.adjoint ∘ₗ B
  have hquad : ∀ x : E,
      (inner ℂ x (S x)).re ≤ (inner ℂ x (T x)).re := by
    intro x
    have hsq : ‖A x‖ ^ 2 ≤ ‖B x‖ ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hAB x)
    calc
      (inner ℂ x (S x)).re = ‖A x‖ ^ 2 := by
        change (inner ℂ x (A.adjoint (A x))).re = ‖A x‖ ^ 2
        rw [A.adjoint_inner_right]
        exact complex_re_inner_self_eq_norm_sq (A x)
      _ ≤ ‖B x‖ ^ 2 := hsq
      _ = (inner ℂ x (T x)).re := by
        change ‖B x‖ ^ 2 = (inner ℂ x (B.adjoint (B x))).re
        rw [B.adjoint_inner_right]
        exact (complex_re_inner_self_eq_norm_sq (B x)).symm
  have heigen :
      A.isSymmetric_adjoint_comp_self.eigenvalues rfl k ≤
        B.isSymmetric_adjoint_comp_self.eigenvalues rfl k :=
    eigenvalues_le_of_quadraticForm_le S T
      A.isSymmetric_adjoint_comp_self B.isSymmetric_adjoint_comp_self hquad k
  have hsquare : A.singularValues k ^ 2 ≤ B.singularValues k ^ 2 := by
    rw [A.sq_singularValues_fin rfl k, B.sq_singularValues_fin rfl k]
    exact heigen
  exact (sq_le_sq₀ (A.singularValues_nonneg k) (B.singularValues_nonneg k)).1 hsquare

end SingularValueOrder

end

end GroupApproximation

open GroupApproximation.SingularValueOrder

#audit_axioms eigenvalues_le_of_quadraticForm_le
#audit_axioms singularValues_le_of_norm_apply_le
