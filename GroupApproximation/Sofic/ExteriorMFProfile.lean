import GroupApproximation.Sofic.HyperlinearAmplification
import GroupApproximation.Sofic.NormTraceGap
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Matrix.Order

/-!
# Finite-dimensional exterior amplification estimates

This file proves finite-dimensional exterior-algebra identities and
Hilbert--Schmidt/operator-norm estimates.  The full fermionic Fock lift of a
matrix `A` is the direct sum of all exterior powers of `A`; tensoring it with
its complex conjugate removes the scalar phase.
-/

namespace GroupApproximation

open Matrix Set
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [LinearOrder Y]

/-- The matrix of the `k`th exterior power in the wedge basis induced by the
standard basis of `Y → ℂ`. -/
def exteriorDegreeMatrix (A : Matrix Y Y ℂ) (k : ℕ) :
    Matrix (powersetCard Y k) (powersetCard Y k) ℂ :=
  LinearMap.toMatrix ((Pi.basisFun ℂ Y).exteriorPower k)
    ((Pi.basisFun ℂ Y).exteriorPower k)
    (exteriorPower.map k (Matrix.toLin' A))

/-- Exterior powers preserve products exactly. -/
theorem exteriorDegreeMatrix_mul (A B : Matrix Y Y ℂ) (k : ℕ) :
    exteriorDegreeMatrix (A * B) k =
      exteriorDegreeMatrix A k * exteriorDegreeMatrix B k := by
  classical
  unfold exteriorDegreeMatrix
  rw [Matrix.toLin'_mul, exteriorPower.map_comp]
  exact LinearMap.toMatrix_comp
    ((Pi.basisFun ℂ Y).exteriorPower k)
    ((Pi.basisFun ℂ Y).exteriorPower k)
    ((Pi.basisFun ℂ Y).exteriorPower k) _ _

/-- The exterior power of the identity is the identity. -/
theorem exteriorDegreeMatrix_one (k : ℕ) :
    exteriorDegreeMatrix (1 : Matrix Y Y ℂ) k = 1 := by
  unfold exteriorDegreeMatrix
  rw [Matrix.toLin'_one, exteriorPower.map_id]
  exact LinearMap.toMatrix_id _

/-- Matrix entries of an exterior power are minors of the original matrix.
The transpose in the displayed determinant is immaterial, but this orientation
is the one produced directly by Mathlib's alternating-pairing convention. -/
theorem exteriorDegreeMatrix_apply (A : Matrix Y Y ℂ) (k : ℕ)
    (s t : powersetCard Y k) :
    exteriorDegreeMatrix A k s t =
      (Matrix.of fun i j : Fin k ↦
        A (powersetCard.ofFinEmbEquiv.symm s j)
          (powersetCard.ofFinEmbEquiv.symm t i)).det := by
  rw [exteriorDegreeMatrix, LinearMap.toMatrix_apply,
    exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family,
    exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  ext i j
  simp [Matrix.toLin'_apply, Pi.basisFun_repr, Pi.basisFun_apply]

/-- Exterior powers commute with conjugate transpose in the standard wedge
basis. -/
theorem exteriorDegreeMatrix_conjTranspose (A : Matrix Y Y ℂ) (k : ℕ) :
    exteriorDegreeMatrix Aᴴ k = (exteriorDegreeMatrix A k)ᴴ := by
  ext s t
  rw [exteriorDegreeMatrix_apply, Matrix.conjTranspose_apply,
    exteriorDegreeMatrix_apply]
  rw [← Matrix.det_conjTranspose]
  congr 1

/-- Each exterior degree of a unitary matrix is unitary. -/
theorem exteriorDegreeMatrix_mem_unitaryGroup {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (k : ℕ) :
    exteriorDegreeMatrix A k ∈
      Matrix.unitaryGroup (powersetCard Y k) ℂ := by
  have hAA : A * Aᴴ = 1 := by
    have h := hA
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← exteriorDegreeMatrix_conjTranspose, ← exteriorDegreeMatrix_mul,
    hAA, exteriorDegreeMatrix_one]

/-! ## The full fermionic Fock lift -/

/-- One basis vector for every subset of `Y`, grouped by exterior degree. -/
abbrev FockIndex (Y : Type*) [Fintype Y] :=
  Σ k : Fin (Fintype.card Y + 1), powersetCard Y k

/-- The direct sum of all exterior powers of `A`. -/
def fockMatrix (A : Matrix Y Y ℂ) : Matrix (FockIndex Y) (FockIndex Y) ℂ :=
  fun p q ↦ if h : p.1 = q.1 then
    exteriorDegreeMatrix A p.1 p.2 (h.symm ▸ q.2)
  else 0

@[simp] theorem fockMatrix_apply_same (A : Matrix Y Y ℂ)
    (k : Fin (Fintype.card Y + 1)) (s t : powersetCard Y k) :
    fockMatrix A ⟨k, s⟩ ⟨k, t⟩ = exteriorDegreeMatrix A k s t := by
  simp [fockMatrix]

@[simp] theorem fockMatrix_apply_ne (A : Matrix Y Y ℂ)
    {k l : Fin (Fintype.card Y + 1)} (hkl : k ≠ l)
    (s : powersetCard Y k) (t : powersetCard Y l) :
    fockMatrix A ⟨k, s⟩ ⟨l, t⟩ = 0 := by
  simp [fockMatrix, hkl]

/-- The Fock lift preserves products exactly. -/
theorem fockMatrix_mul (A B : Matrix Y Y ℂ) :
    fockMatrix (A * B) = fockMatrix A * fockMatrix B := by
  classical
  ext ⟨k, s⟩ ⟨l, t⟩
  simp only [Matrix.mul_apply, Fintype.sum_sigma]
  by_cases hkl : k = l
  · subst l
    rw [fockMatrix_apply_same, exteriorDegreeMatrix_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hmk
      simp [fockMatrix, hmk, Ne.symm hmk]
    · exact fun hk ↦ (hk (Finset.mem_univ k)).elim
  · rw [fockMatrix_apply_ne _ hkl]
    symm
    apply Finset.sum_eq_zero
    intro m _
    by_cases hkm : k = m
    · have hml : m ≠ l := fun h ↦ hkl (hkm.trans h)
      simp [fockMatrix, hml]
    · simp [fockMatrix, hkm]

/-- The Fock lift sends the identity to the identity. -/
theorem fockMatrix_one : fockMatrix (1 : Matrix Y Y ℂ) = 1 := by
  classical
  ext ⟨k, s⟩ ⟨l, t⟩
  by_cases hkl : k = l
  · subst l
    rw [fockMatrix_apply_same, exteriorDegreeMatrix_one]
    simp [Matrix.one_apply]
  · rw [fockMatrix_apply_ne _ hkl]
    exact (Matrix.one_apply_ne (fun h ↦ hkl (congrArg Sigma.fst h))).symm

/-- The Fock lift commutes with conjugate transpose. -/
theorem fockMatrix_conjTranspose (A : Matrix Y Y ℂ) :
    fockMatrix Aᴴ = (fockMatrix A)ᴴ := by
  classical
  ext ⟨k, s⟩ ⟨l, t⟩
  by_cases hkl : k = l
  · subst l
    rw [fockMatrix_apply_same, Matrix.conjTranspose_apply,
      fockMatrix_apply_same, exteriorDegreeMatrix_conjTranspose,
      Matrix.conjTranspose_apply]
  · rw [fockMatrix_apply_ne _ hkl, Matrix.conjTranspose_apply,
      fockMatrix_apply_ne _ (Ne.symm hkl)]
    simp

/-- The Fock lift of a unitary matrix is unitary. -/
theorem fockMatrix_mem_unitaryGroup {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    fockMatrix A ∈ Matrix.unitaryGroup (FockIndex Y) ℂ := by
  have hAA : A * Aᴴ = 1 := by
    have h := hA
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← fockMatrix_conjTranspose, ← fockMatrix_mul, hAA, fockMatrix_one]

omit [DecidableEq Y] [LinearOrder Y] in
/-- The Fock space has dimension `2 ^ dim(Y)`. -/
@[simp] theorem card_FockIndex :
    Fintype.card (FockIndex Y) = 2 ^ Fintype.card Y := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_eq_nat_card, powersetCard.card]
  rw [← Fintype.card_eq_nat_card, Fin.sum_univ_eq_sum_range]
  exact Nat.sum_range_choose (Fintype.card Y)

/-- A diagonal entry in exterior degree `k` is the corresponding principal
minor. -/
theorem exteriorDegreeMatrix_apply_self (A : Matrix Y Y ℂ) (k : ℕ)
    (s : powersetCard Y k) :
    exteriorDegreeMatrix A k s s =
      (A.submatrix (Subtype.val : (↥s.val) → Y)
        (Subtype.val : (↥s.val) → Y)).det := by
  rw [exteriorDegreeMatrix_apply]
  let e : Fin k ≃ ↥s.val := (Finset.orderIsoOfFin s.val s.prop).toEquiv
  calc
    (Matrix.of fun i j : Fin k ↦
        A (powersetCard.ofFinEmbEquiv.symm s j)
          (powersetCard.ofFinEmbEquiv.symm s i)).det =
        (Matrix.of fun i j : Fin k ↦
          A (powersetCard.ofFinEmbEquiv.symm s i)
            (powersetCard.ofFinEmbEquiv.symm s j)).det := by
          rw [← Matrix.det_transpose]
          congr 1
    _ = ((A.submatrix (Subtype.val : (↥s.val) → Y)
          (Subtype.val : (↥s.val) → Y)).submatrix e e).det := by
          congr 1
    _ = (A.submatrix (Subtype.val : (↥s.val) → Y)
          (Subtype.val : (↥s.val) → Y)).det :=
          Matrix.det_submatrix_equiv_self e _

/-- The unnormalized Fock character is `det (I + A)`. -/
theorem trace_fockMatrix (A : Matrix Y Y ℂ) :
    Matrix.trace (fockMatrix A) = (1 + A).det := by
  classical
  rw [Matrix.trace, Fintype.sum_sigma]
  change (∑ x, ∑ y, fockMatrix A ⟨x, y⟩ ⟨x, y⟩) = _
  simp only [fockMatrix]
  simp_rw [exteriorDegreeMatrix_apply_self]
  let p : Polynomial ℂ := Matrix.det
    (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)
  have hpdeg : p.natDegree < Fintype.card Y + 1 := by
    apply lt_of_le_of_lt _ (Nat.lt_succ_self _)
    simpa [p, add_comm] using
      (Polynomial.natDegree_det_X_add_C_le A (1 : Matrix Y Y ℂ))
  have hcoeff : ∀ k : ℕ, p.coeff k =
      ∑ s ∈ (Finset.univ : Finset Y).powersetCard k,
        (A.submatrix (Subtype.val : s → Y) (Subtype.val : s → Y)).det := by
    intro k
    simpa [p] using Matrix.coeff_det_one_add_X_smul_eq_sum_minors A k
  have heval : p.eval 1 = (1 + A).det := by
    simp [p, eval_det]
  rw [← heval, Polynomial.eval_eq_sum_range' hpdeg]
  simp only [one_pow, mul_one]
  simp only [dite_true]
  let q : ℕ → ℂ := fun k ↦ ∑ s : powersetCard Y k,
    (A.submatrix (Subtype.val : (↥s.val) → Y)
      (Subtype.val : (↥s.val) → Y)).det
  change (∑ k : Fin (Fintype.card Y + 1), q k) = _
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hcoeff]
  unfold q
  symm
  exact Finset.sum_subtype _ (fun _ ↦ Finset.mem_powersetCard_univ) _

/-! ## The conjugate Fock character -/

/-- The Fock basis as a finite model. -/
abbrev fockModel (Y : FiniteModel) [LinearOrder Y] : FiniteModel :=
  ⟨FockIndex Y, inferInstance, inferInstance⟩

/-- The normalized Fock character. -/
theorem normTrace_fockMatrix (Y : FiniteModel) [LinearOrder Y]
    (A : Matrix Y Y ℂ) :
    normTrace (fockModel Y) (fockMatrix A) =
      (1 + A).det / (2 ^ Fintype.card Y : ℂ) := by
  rw [normTrace, trace_fockMatrix, card_FockIndex]
  norm_cast

/-- The phase-free exterior amplification, `Γ(A) ⊗ overline(Γ(A))`.
This is the matrix realization of `Ad Λ(A)` on the endomorphisms of the full
exterior algebra. -/
def exteriorAdMatrix (A : Matrix Y Y ℂ) :
    Matrix (FockIndex Y × FockIndex Y) (FockIndex Y × FockIndex Y) ℂ :=
  conjDouble (fockMatrix A)

/-- **Exterior character identity.**  The normalized character of the
conjugate full-exterior representation is
`|det ((I + A) / 2)|²`.  Division by `2` is written as scalar multiplication
by `2⁻¹`, removing any ambiguity about matrix division. -/
theorem normTrace_exteriorAdMatrix (Y : FiniteModel) [LinearOrder Y]
    (A : Matrix Y Y ℂ) :
    normTrace (doubleModel (fockModel Y)) (exteriorAdMatrix A) =
      Complex.normSq ((((2 : ℂ)⁻¹) • (1 + A)).det) := by
  rw [exteriorAdMatrix, normTrace_conjDouble, normTrace_fockMatrix]
  congr 2
  rw [Matrix.det_smul]
  rw [div_eq_mul_inv, inv_pow]
  ring

/-- Exterior amplification is exactly multiplicative. -/
theorem exteriorAdMatrix_mul (A B : Matrix Y Y ℂ) :
    exteriorAdMatrix (A * B) = exteriorAdMatrix A * exteriorAdMatrix B := by
  rw [exteriorAdMatrix, exteriorAdMatrix, exteriorAdMatrix,
    fockMatrix_mul, conjDouble_mul]

/-- Exterior amplification preserves unitarity. -/
theorem exteriorAdMatrix_mem_unitaryGroup {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    exteriorAdMatrix A ∈ Matrix.unitaryGroup (FockIndex Y × FockIndex Y) ℂ :=
  conjDouble_mem_unitaryGroup (fockMatrix_mem_unitaryGroup hA)

/-- Exterior amplification commutes with conjugate transpose. -/
theorem exteriorAdMatrix_conjTranspose (A : Matrix Y Y ℂ) :
    exteriorAdMatrix Aᴴ = (exteriorAdMatrix A)ᴴ := by
  rw [exteriorAdMatrix, exteriorAdMatrix, fockMatrix_conjTranspose,
    conjDouble_conjTranspose]

/-! ## Spectral determinant estimates -/

omit [LinearOrder Y] in
/-- Applying the affine polynomial `x ↦ 1 - c x` to a Hermitian matrix
turns its determinant into the product of that polynomial over the real
eigenvalues. -/
theorem det_one_sub_smul_eq_prod_eigenvalues {H : Matrix Y Y ℂ}
    (hH : H.IsHermitian) (c : ℝ) :
    (1 - (c : ℂ) • H).det =
      ∏ i : Y, ((1 - c * hH.eigenvalues i : ℝ) : ℂ) := by
  conv_lhs => rw [hH.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  have hu : (hH.eigenvectorUnitary : Matrix Y Y ℂ) *
      (star hH.eigenvectorUnitary : Matrix Y Y ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hrewrite :
      1 - (c : ℂ) •
          ((hH.eigenvectorUnitary : Matrix Y Y ℂ) *
            Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
              (star hH.eigenvectorUnitary : Matrix Y Y ℂ)) =
        (hH.eigenvectorUnitary : Matrix Y Y ℂ) *
          (1 - (c : ℂ) • Matrix.diagonal
            (RCLike.ofReal ∘ hH.eigenvalues)) *
              (star hH.eigenvectorUnitary : Matrix Y Y ℂ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hrewrite, Matrix.det_mul, Matrix.det_mul, mul_assoc]
  have hdetu : (hH.eigenvectorUnitary : Matrix Y Y ℂ).det *
      (star hH.eigenvectorUnitary : Matrix Y Y ℂ).det = 1 := by
    rw [← Matrix.det_mul, hu, Matrix.det_one]
  calc
    (hH.eigenvectorUnitary : Matrix Y Y ℂ).det *
        (((1 : Matrix Y Y ℂ) - (c : ℂ) • Matrix.diagonal
          (RCLike.ofReal ∘ hH.eigenvalues)).det *
            (star hH.eigenvectorUnitary : Matrix Y Y ℂ).det) =
      ((1 : Matrix Y Y ℂ) - (c : ℂ) • Matrix.diagonal
          (RCLike.ofReal ∘ hH.eigenvalues)).det *
        ((hH.eigenvectorUnitary : Matrix Y Y ℂ).det *
          (star hH.eigenvectorUnitary : Matrix Y Y ℂ).det) := by ring
    _ = ((1 : Matrix Y Y ℂ) - (c : ℂ) • Matrix.diagonal
          (RCLike.ofReal ∘ hH.eigenvalues)).det := by rw [hdetu, mul_one]
    _ = ∏ i : Y, ((1 - c * hH.eigenvalues i : ℝ) : ℂ) := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub,
        Matrix.det_diagonal]
      apply Finset.prod_congr rfl
      intro i hi
      simp [Function.comp_apply]

omit [LinearOrder Y] in
/-- The eigenvalues of `D D*` are bounded above by `‖D‖²`. -/
theorem eigenvalues_mul_conjTranspose_le_sq_opNorm (D : Matrix Y Y ℂ) (i : Y) :
    (Matrix.isHermitian_mul_conjTranspose_self D).eigenvalues i ≤ ‖D‖ ^ 2 := by
  letI : Nonempty Y := ⟨i⟩
  let H : Matrix Y Y ℂ := D * Dᴴ
  let hH : H.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
  have hs := spectrum.norm_le_norm_of_mem (hH.eigenvalues_mem_spectrum_real i)
  have hnorm : ‖H‖ = ‖D‖ ^ 2 := by
    change ‖D * Dᴴ‖ = ‖D‖ ^ 2
    rw [← Matrix.star_eq_conjTranspose, CStarRing.norm_self_mul_star, pow_two]
  have habs : |hH.eigenvalues i| ≤ ‖D‖ ^ 2 := by
    simpa [Real.norm_eq_abs, hnorm] using hs
  exact (le_abs_self _).trans habs

omit [LinearOrder Y] in
/-- The largest eigenvalue of `D D*` is exactly `‖D‖²`. -/
theorem exists_eigenvalue_mul_conjTranspose_eq_sq_opNorm
    (D : Matrix Y Y ℂ) (hY : Nonempty Y) :
    ∃ i : Y, (Matrix.isHermitian_mul_conjTranspose_self D).eigenvalues i =
      ‖D‖ ^ 2 := by
  letI : Nonempty Y := hY
  let H : Matrix Y Y ℂ := D * Dᴴ
  let hH : H.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
  have hpos : H.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose D
  have hnormdiag : ‖H‖ = ‖fun i : Y ↦ (hH.eigenvalues i : ℂ)‖ := by
    calc
      ‖H‖ = ‖Unitary.conjStarAlgAut ℂ (Matrix Y Y ℂ) hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues))‖ :=
        congrArg norm hH.spectral_theorem
      _ = ‖fun i : Y ↦ (hH.eigenvalues i : ℂ)‖ := by
        rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
          CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
          Matrix.l2_opNorm_diagonal]
        rfl
  obtain ⟨i, hi⟩ :=
    (IsGreatest.pi_norm (f := fun i : Y ↦ (hH.eigenvalues i : ℂ))).1
  refine ⟨i, ?_⟩
  change hH.eigenvalues i = ‖D‖ ^ 2
  have hnonneg : 0 ≤ hH.eigenvalues i := hpos.eigenvalues_nonneg i
  have hi' : hH.eigenvalues i = ‖H‖ := by
    rw [hnormdiag, ← hi]
    simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hi']
  change ‖D * Dᴴ‖ = ‖D‖ ^ 2
  rw [← Matrix.star_eq_conjTranspose, CStarRing.norm_self_mul_star, pow_two]

omit [LinearOrder Y] in
/-- Two unitaries are at operator-norm distance at most `2`. -/
theorem opNorm_sub_le_two_of_unitary (hY : Nonempty Y) {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ) :
    ‖A - B‖ ≤ 2 := by
  letI : Nonempty Y := hY
  calc
    ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
    _ = 2 := by rw [CStarRing.norm_of_mem_unitary hA,
      CStarRing.norm_of_mem_unitary hB]; norm_num

omit [LinearOrder Y] in
/-- The positive midpoint Gram matrix is `I - (W-I)(W-I)*/4`. -/
theorem midpoint_mul_conjTranspose {W : Matrix Y Y ℂ}
    (hW : W ∈ Matrix.unitaryGroup Y ℂ) :
    (((2 : ℂ)⁻¹) • (1 + W)) * ((((2 : ℂ)⁻¹) • (1 + W))ᴴ) =
      1 - ((1 / 4 : ℝ) : ℂ) • ((W - 1) * (W - 1)ᴴ) := by
  have hWW : W * Wᴴ = 1 := by
    have h := hW
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one]
  norm_num [map_inv₀, Matrix.smul_mul, Matrix.mul_smul]
  have hL :
      ((1 / 2 : ℂ) • (1 : Matrix Y Y ℂ) + (1 / 2 : ℂ) • W) *
          ((1 / 2 : ℂ) • 1 + (1 / 2 : ℂ) • Wᴴ) =
        (1 / 4 : ℂ) • (1 + W + Wᴴ + W * Wᴴ) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply]
    ring
  have hD : (W - 1) * (Wᴴ - 1) =
      W * Wᴴ - W - Wᴴ + 1 := by noncomm_ring
  rw [hL, hD, hWW]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

omit [LinearOrder Y] in
/-- Squared determinant modulus is the determinant of the Gram matrix. -/
theorem normSq_det_eq_det_mul_conjTranspose (B : Matrix Y Y ℂ) :
    (Complex.normSq B.det : ℂ) = (B * Bᴴ).det := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, ← Complex.mul_conj]
  rfl

omit [LinearOrder Y] in
/-- The exterior determinant character as a real product over the squared
singular displacements of `W-I`. -/
theorem normSq_det_midpoint_eq_prod {W : Matrix Y Y ℂ}
    (hW : W ∈ Matrix.unitaryGroup Y ℂ) :
    Complex.normSq ((((2 : ℂ)⁻¹) • (1 + W)).det) =
      ∏ i : Y, (1 - (Matrix.isHermitian_mul_conjTranspose_self
        (W - 1)).eigenvalues i / 4) := by
  let B : Matrix Y Y ℂ := ((2 : ℂ)⁻¹) • (1 + W)
  let H : Matrix Y Y ℂ := (W - 1) * (W - 1)ᴴ
  let hH : H.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self (W - 1)
  have hc : (Complex.normSq B.det : ℂ) =
      ((∏ i : Y, (1 - hH.eigenvalues i / 4) : ℝ) : ℂ) := by
    rw [normSq_det_eq_det_mul_conjTranspose]
    rw [show B * Bᴴ = 1 - ((1 / 4 : ℝ) : ℂ) • H from
      midpoint_mul_conjTranspose hW]
    rw [det_one_sub_smul_eq_prod_eigenvalues hH (1 / 4)]
    norm_num [div_eq_mul_inv, mul_comm]
  exact_mod_cast hc

omit [LinearOrder Y] in
/-- **Exact defect determinant bound.**  If a unitary is within `ε` of the
identity in operator norm (with `0 ≤ ε ≤ 2`), its exterior character is at
least `1 - d ε²/4`. -/
theorem one_sub_card_mul_sq_div_four_le_normSq_det_midpoint
    {W : Matrix Y Y ℂ}
    (hW : W ∈ Matrix.unitaryGroup Y ℂ)
    {ε : ℝ} (hε2 : ε ≤ 2) (hnorm : ‖W - 1‖ ≤ ε) :
    1 - Fintype.card Y * ε ^ 2 / 4 ≤
      Complex.normSq ((((2 : ℂ)⁻¹) • (1 + W)).det) := by
  have hε0 : 0 ≤ ε := (norm_nonneg (W - 1)).trans hnorm
  rw [normSq_det_midpoint_eq_prod hW]
  let D : Matrix Y Y ℂ := W - 1
  let hH : (D * Dᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
  have hnormsq : ‖D‖ ^ 2 ≤ ε ^ 2 := by
    nlinarith [norm_nonneg D]
  have hμleε : ∀ i : Y, hH.eigenvalues i ≤ ε ^ 2 := by
    intro i
    exact (eigenvalues_mul_conjTranspose_le_sq_opNorm D i).trans hnormsq
  have hbase : 0 ≤ 1 - ε ^ 2 / 4 := by nlinarith
  have hfactor : ∀ i : Y,
      1 - ε ^ 2 / 4 ≤ 1 - hH.eigenvalues i / 4 := by
    intro i
    linarith [hμleε i]
  have hprod : (1 - ε ^ 2 / 4) ^ Fintype.card Y ≤
      ∏ i : Y, (1 - hH.eigenvalues i / 4) := by
    calc
      (1 - ε ^ 2 / 4) ^ Fintype.card Y =
          ∏ _i : Y, (1 - ε ^ 2 / 4) := by simp
      _ ≤ ∏ i : Y, (1 - hH.eigenvalues i / 4) :=
        Finset.prod_le_prod (fun _ _ ↦ hbase) (fun i _ ↦ hfactor i)
  have hbern := one_add_mul_sub_le_pow
    (a := (1 - ε ^ 2 / 4 : ℝ)) (by nlinarith : -1 ≤ 1 - ε ^ 2 / 4)
    (Fintype.card Y)
  have hlinear : 1 - Fintype.card Y * ε ^ 2 / 4 ≤
      (1 - ε ^ 2 / 4) ^ Fintype.card Y := by
    nlinarith
  exact hlinear.trans hprod

omit [LinearOrder Y] in
/-- **Dimension-free separation determinant bound.**  Operator-norm
separation by `δ` forces the exterior character below `1 - δ²/4`, with no
dependence on the matrix dimension. -/
theorem normSq_det_midpoint_le_one_sub_sq_div_four
    (hY : Nonempty Y) {W : Matrix Y Y ℂ}
    (hW : W ∈ Matrix.unitaryGroup Y ℂ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hnorm : δ ≤ ‖W - 1‖) :
    Complex.normSq ((((2 : ℂ)⁻¹) • (1 + W)).det) ≤ 1 - δ ^ 2 / 4 := by
  letI : Nonempty Y := hY
  rw [normSq_det_midpoint_eq_prod hW]
  let D : Matrix Y Y ℂ := W - 1
  let hH : (D * Dᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
  obtain ⟨i, hi⟩ := exists_eigenvalue_mul_conjTranspose_eq_sq_opNorm D hY
  have hD2 : ‖D‖ ≤ 2 :=
    opNorm_sub_le_two_of_unitary hY hW (Submonoid.one_mem _)
  have hμ0 : ∀ j : Y, 0 ≤ hH.eigenvalues j := by
    intro j
    exact Matrix.eigenvalues_self_mul_conjTranspose_nonneg D j
  have hμle4 : ∀ j : Y, hH.eigenvalues j ≤ 4 := by
    intro j
    have hj := eigenvalues_mul_conjTranspose_le_sq_opNorm D j
    nlinarith [norm_nonneg D]
  have hfactor0 : ∀ j : Y, 0 ≤ 1 - hH.eigenvalues j / 4 := by
    intro j
    linarith [hμle4 j]
  have hfactor1 : ∀ j : Y, 1 - hH.eigenvalues j / 4 ≤ 1 := by
    intro j
    linarith [hμ0 j]
  have hi' : hH.eigenvalues i = ‖D‖ ^ 2 := hi
  have hselected : 1 - hH.eigenvalues i / 4 ≤ 1 - δ ^ 2 / 4 := by
    rw [hi']
    nlinarith [norm_nonneg D]
  let R : ℝ := ∏ j ∈ (Finset.univ.erase i), (1 - hH.eigenvalues j / 4)
  have hR0 : 0 ≤ R := by
    apply Finset.prod_nonneg
    intro j hj
    exact hfactor0 j
  have hR1 : R ≤ 1 := by
    calc
      R ≤ ∏ _j ∈ (Finset.univ.erase i), (1 : ℝ) := by
        exact Finset.prod_le_prod (fun j _ ↦ hfactor0 j)
          (fun j _ ↦ hfactor1 j)
      _ = 1 := by simp
  have hq0 : 0 ≤ 1 - δ ^ 2 / 4 := by
    nlinarith [norm_nonneg D]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  change (1 - hH.eigenvalues i / 4) * R ≤ 1 - δ ^ 2 / 4
  nlinarith

/-! ## Exact Hilbert--Schmidt defect and separation constants -/

omit [LinearOrder Y] in
/-- The conjugate transpose of a unitary matrix is unitary. -/
theorem conjTranspose_mem_unitaryGroup {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    Aᴴ ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have h := hA
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  exact h

omit [LinearOrder Y] in
/-- Right multiplication by the adjoint of a unitary identifies relative
displacement from the identity with pairwise operator-norm displacement. -/
theorem opNorm_mul_conjTranspose_sub_one {A B : Matrix Y Y ℂ}
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) :
    ‖A * Bᴴ - 1‖ = ‖A - B‖ := by
  have hBB : B * Bᴴ = 1 := by
    have h := hB
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  rw [show A * Bᴴ - 1 = (A - B) * Bᴴ by rw [Matrix.sub_mul, hBB]]
  exact CStarRing.norm_mul_mem_unitary _ (conjTranspose_mem_unitaryGroup hB)

/-- The exact squared normalized Hilbert--Schmidt distance after exterior
amplification. -/
theorem hsDistSq_exteriorAdMatrix (Y : FiniteModel) [LinearOrder Y]
    {A B : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) :
    hsDistSq (doubleModel (fockModel Y))
        (exteriorAdMatrix A) (exteriorAdMatrix B) =
      2 - 2 * Complex.normSq
        ((((2 : ℂ)⁻¹) • (1 + A * Bᴴ)).det) := by
  have hF : 0 < Fintype.card (fockModel Y) := by
    rw [card_FockIndex]
    positivity
  have hD : 0 < Fintype.card (doubleModel (fockModel Y)) := by
    rw [card_doubleModel]
    exact Nat.mul_pos hF hF
  have hprod : exteriorAdMatrix A * (exteriorAdMatrix B)ᴴ =
      exteriorAdMatrix (A * Bᴴ) := by
    rw [← exteriorAdMatrix_conjTranspose, ← exteriorAdMatrix_mul]
  rw [hsDistSq_of_unitary (doubleModel (fockModel Y))
    (exteriorAdMatrix_mem_unitaryGroup hA)
    (exteriorAdMatrix_mem_unitaryGroup hB) hD, hprod,
    normTrace_exteriorAdMatrix]
  simp

/-- **Exact finite-dimensional defect inequality.**  Exterior amplification
turns operator-norm error `ε` into squared normalized Hilbert--Schmidt error at
most `d ε² / 2`. -/
theorem hsDistSq_exteriorAdMatrix_le (Y : FiniteModel) [LinearOrder Y]
    {A B : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) {ε : ℝ}
    (hε2 : ε ≤ 2) (hnorm : ‖A - B‖ ≤ ε) :
    hsDistSq (doubleModel (fockModel Y))
        (exteriorAdMatrix A) (exteriorAdMatrix B) ≤
      Fintype.card Y * ε ^ 2 / 2 := by
  let W : Matrix Y Y ℂ := A * Bᴴ
  have hW : W ∈ Matrix.unitaryGroup Y ℂ :=
    mul_mem hA (conjTranspose_mem_unitaryGroup hB)
  have hnormW : ‖W - 1‖ ≤ ε := by
    rw [opNorm_mul_conjTranspose_sub_one hB]
    exact hnorm
  have hdet := one_sub_card_mul_sq_div_four_le_normSq_det_midpoint
    hW hε2 hnormW
  rw [hsDistSq_exteriorAdMatrix Y hA hB]
  change 1 - Fintype.card Y * ε ^ 2 / 4 ≤
    Complex.normSq ((((2 : ℂ)⁻¹) • (1 + A * Bᴴ)).det) at hdet
  linarith

/-- **Dimension-free Hilbert--Schmidt separation.**  Operator-norm separation
by `δ` becomes squared normalized Hilbert--Schmidt separation `δ²/2`,
independently of the matrix dimension. -/
theorem sq_div_two_le_hsDistSq_exteriorAdMatrix
    (Y : FiniteModel) [LinearOrder Y] (hY : Nonempty Y)
    {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hnorm : δ ≤ ‖A - B‖) :
    δ ^ 2 / 2 ≤ hsDistSq (doubleModel (fockModel Y))
      (exteriorAdMatrix A) (exteriorAdMatrix B) := by
  letI : Nonempty Y := hY
  let W : Matrix Y Y ℂ := A * Bᴴ
  have hW : W ∈ Matrix.unitaryGroup Y ℂ :=
    mul_mem hA (conjTranspose_mem_unitaryGroup hB)
  have hnormW : δ ≤ ‖W - 1‖ := by
    rw [opNorm_mul_conjTranspose_sub_one hB]
    exact hnorm
  have hdet := normSq_det_midpoint_le_one_sub_sq_div_four hY hW hδ0 hnormW
  rw [hsDistSq_exteriorAdMatrix Y hA hB]
  change Complex.normSq ((((2 : ℂ)⁻¹) • (1 + A * Bᴴ)).det) ≤
    1 - δ ^ 2 / 4 at hdet
  linarith

/-! ## Tensor amplification -/

/-- The `k`-fold tensor power of the phase-free exterior lift. -/
def exteriorTensorMatrix (A : Matrix Y Y ℂ) (k : ℕ) :
    Matrix (Fin k → (FockIndex Y × FockIndex Y))
      (Fin k → (FockIndex Y × FockIndex Y)) ℂ :=
  tensorPow (exteriorAdMatrix A) k

/-- Exterior tensor amplification remains exactly multiplicative. -/
theorem exteriorTensorMatrix_mul (A B : Matrix Y Y ℂ) (k : ℕ) :
    exteriorTensorMatrix (A * B) k =
      exteriorTensorMatrix A k * exteriorTensorMatrix B k := by
  rw [exteriorTensorMatrix, exteriorTensorMatrix, exteriorTensorMatrix,
    exteriorAdMatrix_mul, tensorPow_mul]

/-- Exterior tensor amplification preserves unitarity. -/
theorem exteriorTensorMatrix_mem_unitaryGroup {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (k : ℕ) :
    exteriorTensorMatrix A k ∈ Matrix.unitaryGroup
      (Fin k → (FockIndex Y × FockIndex Y)) ℂ :=
  tensorPow_mem_unitaryGroup (exteriorAdMatrix_mem_unitaryGroup hA) k

/-- Exact tensor-amplified exterior character distance. -/
theorem hsDistSq_exteriorTensorMatrix (Y : FiniteModel) [LinearOrder Y]
    {A B : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) (k : ℕ) :
    hsDistSq (tensorModel (doubleModel (fockModel Y)) k)
        (exteriorTensorMatrix A k) (exteriorTensorMatrix B k) =
      2 - 2 * (Complex.normSq
        ((((2 : ℂ)⁻¹) • (1 + A * Bᴴ)).det)) ^ k := by
  have hF : 0 < Fintype.card (fockModel Y) := by
    rw [card_FockIndex]
    positivity
  have hD : 0 < Fintype.card (doubleModel (fockModel Y)) := by
    rw [card_doubleModel]
    exact Nat.mul_pos hF hF
  have hprod : exteriorAdMatrix A * (exteriorAdMatrix B)ᴴ =
      exteriorAdMatrix (A * Bᴴ) := by
    rw [← exteriorAdMatrix_conjTranspose, ← exteriorAdMatrix_mul]
  rw [exteriorTensorMatrix, exteriorTensorMatrix,
    hsDistSq_tensorPow (doubleModel (fockModel Y))
      (exteriorAdMatrix_mem_unitaryGroup hA)
      (exteriorAdMatrix_mem_unitaryGroup hB) hD k,
    hprod, normTrace_exteriorAdMatrix, ← Complex.ofReal_pow,
    Complex.ofReal_re]

/-- Tensoring `k` exterior lifts costs at most the factor `k` in the exact
finite-dimensional defect bound. -/
theorem hsDistSq_exteriorTensorMatrix_le
    (Y : FiniteModel) [LinearOrder Y]
    {A B : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) {ε : ℝ}
    (hε2 : ε ≤ 2) (hnorm : ‖A - B‖ ≤ ε)
    (k : ℕ) :
    hsDistSq (tensorModel (doubleModel (fockModel Y)) k)
        (exteriorTensorMatrix A k) (exteriorTensorMatrix B k) ≤
      k * (Fintype.card Y * ε ^ 2 / 2) := by
  let q : ℝ := Complex.normSq
    ((((2 : ℂ)⁻¹) • (1 + A * Bᴴ)).det)
  have hbase := hsDistSq_exteriorAdMatrix_le Y hA hB hε2 hnorm
  have hq0 : 0 ≤ q := Complex.normSq_nonneg _
  have hbern := one_add_mul_sub_le_pow (a := q) (by linarith) k
  rw [hsDistSq_exteriorTensorMatrix Y hA hB k]
  rw [hsDistSq_exteriorAdMatrix Y hA hB] at hbase
  change 2 - 2 * q ^ k ≤ _
  change 2 - 2 * q ≤ Fintype.card Y * ε ^ 2 / 2 at hbase
  nlinarith

/-- The same tensor defect bound without an artificial `ε ≤ 2` hypothesis:
the distance between the two unitary inputs is itself at most `2`, so the
previous estimate applies with `min ε 2`. -/
theorem hsDistSq_exteriorTensorMatrix_le_of_nonneg
    (Y : FiniteModel) [LinearOrder Y] (hY : Nonempty Y)
    {A B : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) {ε : ℝ}
    (hnorm : ‖A - B‖ ≤ ε) (k : ℕ) :
    hsDistSq (tensorModel (doubleModel (fockModel Y)) k)
        (exteriorTensorMatrix A k) (exteriorTensorMatrix B k) ≤
      k * (Fintype.card Y * ε ^ 2 / 2) := by
  letI : Nonempty Y := hY
  have hε0 : 0 ≤ ε := (norm_nonneg (A - B)).trans hnorm
  let ε' : ℝ := min ε 2
  have hε'0 : 0 ≤ ε' := le_min hε0 (by norm_num)
  have hε'2 : ε' ≤ 2 := min_le_right _ _
  have hnorm2 : ‖A - B‖ ≤ 2 := opNorm_sub_le_two_of_unitary hY hA hB
  have hnorm' : ‖A - B‖ ≤ ε' := le_min hnorm hnorm2
  have hmain := hsDistSq_exteriorTensorMatrix_le Y hA hB
    hε'2 hnorm' k
  have hsq : ε' ^ 2 ≤ ε ^ 2 := by
    have hle : ε' ≤ ε := min_le_left _ _
    nlinarith
  calc
    _ ≤ k * (Fintype.card Y * ε' ^ 2 / 2) := hmain
    _ ≤ k * (Fintype.card Y * ε ^ 2 / 2) := by gcongr

end

end GroupApproximation
