import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.FiniteDimensionalResidual

/-!
# Rotation blocks and their commutators with block permutation matrices

Source: `non_mf_group_notes.tex`, proof of `thm:exact-mf-residual`, and
Shulman (arXiv:2603.13564), proof of Theorem 10.  The two copies of `G` in
`G *_Γ G` act on `ℂ^Y ⊕ ℂ^Y` by block permutation matrices, and the second
copy is conjugated by a slowly varying rotation

`V = [[C, -S], [S, C]]`, with `C = diag (cos θ)`, `S = diag (sin θ)`.

This file proves the matrix algebra of that construction:

* `rotMatrix_mem_unitaryGroup`: `V` is unitary when `c² + s² = 1` pointwise;
* `norm_rotMatrix_commutator_le`: the commutator of `V` with
  `diag (P_σ, P_τ)` has operator norm at most `2η` whenever `c` and `s` move
  by at most `η` along `σ` and `τ`, and `σ⁻¹`, `τ⁻¹` agree on the support
  of `s`.
-/

namespace GroupApproximation.Full.NN01b

open GroupApproximation Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : FiniteModel)

/-! ## Permutation and real diagonal matrices -/

/-- The permutation matrix of `σ`, sending `e_w` to `e_{σ w}`; it is the
matrix of `permUnitaryHom Y σ`. -/
def pmat (σ : Equiv.Perm Y) : Matrix Y Y ℂ := (σ⁻¹).permMatrix ℂ

theorem coe_permUnitaryHom (σ : Equiv.Perm Y) :
    ((permUnitaryHom Y σ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) = pmat Y σ := rfl

theorem pmat_apply (σ : Equiv.Perm Y) (i j : Y) :
    pmat Y σ i j = if σ⁻¹ i = j then 1 else 0 :=
  permMatrixC_entry Y σ⁻¹ i j

/-- The complex diagonal matrix of a real function. -/
def rdiag (c : Y → ℝ) : Matrix Y Y ℂ := Matrix.diagonal fun w => (c w : ℂ)

theorem rdiag_add (c d : Y → ℝ) :
    rdiag Y c + rdiag Y d = rdiag Y (fun w => c w + d w) := by
  unfold rdiag
  rw [Matrix.diagonal_add]
  exact congrArg Matrix.diagonal (funext fun w => (Complex.ofReal_add (c w) (d w)).symm)

theorem rdiag_sub (c d : Y → ℝ) :
    rdiag Y c - rdiag Y d = rdiag Y (fun w => c w - d w) := by
  unfold rdiag
  rw [Matrix.diagonal_sub]
  exact congrArg Matrix.diagonal (funext fun w => (Complex.ofReal_sub (c w) (d w)).symm)

theorem rdiag_mul (c d : Y → ℝ) :
    rdiag Y c * rdiag Y d = rdiag Y (fun w => c w * d w) := by
  unfold rdiag
  rw [Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun w => (Complex.ofReal_mul (c w) (d w)).symm)

theorem rdiag_one : rdiag Y (fun _ => 1) = 1 := by
  unfold rdiag
  exact (congrArg Matrix.diagonal (funext fun _ => Complex.ofReal_one)).trans
    Matrix.diagonal_one

theorem rdiag_conjTranspose (c : Y → ℝ) : (rdiag Y c)ᴴ = rdiag Y c := by
  unfold rdiag
  rw [Matrix.diagonal_conjTranspose]
  exact congrArg Matrix.diagonal (funext fun w => Complex.conj_ofReal (c w))

/-- Moving a diagonal matrix across a permutation matrix relabels it. -/
theorem pmat_mul_rdiag (σ : Equiv.Perm Y) (c : Y → ℝ) :
    pmat Y σ * rdiag Y c = rdiag Y (fun w => c (σ⁻¹ w)) * pmat Y σ := by
  ext i j
  unfold rdiag
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, pmat_apply]
  by_cases h : σ⁻¹ i = j
  · rw [if_pos h, one_mul, mul_one]
    exact congrArg (fun x : ℝ => (x : ℂ)) (congrArg c h.symm)
  · rw [if_neg h, zero_mul, mul_zero]

/-- A diagonal matrix only sees a permutation on its support. -/
theorem rdiag_mul_pmat_of_agree (s : Y → ℝ) (σ τ : Equiv.Perm Y)
    (h : ∀ w, s w ≠ 0 → σ⁻¹ w = τ⁻¹ w) :
    rdiag Y s * pmat Y σ = rdiag Y s * pmat Y τ := by
  ext i j
  unfold rdiag
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, pmat_apply, pmat_apply]
  by_cases hs : s i = 0
  · rw [hs, Complex.ofReal_zero, zero_mul, zero_mul]
  · rw [h i hs]

theorem comm_rdiag_pmat (c : Y → ℝ) (σ : Equiv.Perm Y) :
    rdiag Y c * pmat Y σ - pmat Y σ * rdiag Y c =
      rdiag Y (fun w => c w - c (σ⁻¹ w)) * pmat Y σ := by
  rw [pmat_mul_rdiag, ← sub_mul, rdiag_sub]

theorem norm_rdiag_mul_pmat_le (d : Y → ℝ) (σ : Equiv.Perm Y) {η : ℝ} (hη : 0 ≤ η)
    (hd : ∀ w, |d w| ≤ η) : ‖rdiag Y d * pmat Y σ‖ ≤ η := by
  have hdiag : ‖rdiag Y d‖ ≤ η := by
    unfold rdiag
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hη]
    intro w
    exact (Complex.norm_real (d w)).trans_le ((Real.norm_eq_abs (d w)).trans_le (hd w))
  have hperm : ‖pmat Y σ‖ ≤ 1 := Matrix.permMatrix_l2_opNorm_le (𝕜 := ℂ) σ⁻¹
  calc ‖rdiag Y d * pmat Y σ‖ ≤ ‖rdiag Y d‖ * ‖pmat Y σ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ η * 1 := mul_le_mul hdiag hperm (norm_nonneg _) hη
    _ = η := mul_one η

/-! ## The swap and rotation matrices on `Y ⊕ Y` -/

/-- The block swap `[[0, 1], [1, 0]]`. -/
def swapMatrix : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ :=
  Matrix.fromBlocks (0 : Matrix Y Y ℂ) (1 : Matrix Y Y ℂ) (1 : Matrix Y Y ℂ)
    (0 : Matrix Y Y ℂ)

theorem swapMatrix_mem_unitaryGroup :
    swapMatrix Y ∈ Matrix.unitaryGroup (blockSumModel Y Y) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold swapMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
    Matrix.fromBlocks_multiply]
  have h1 : (0 : Matrix Y Y ℂ) * 0 + 1 * 1 = 1 := by rw [mul_zero, zero_add, mul_one]
  have h2 : (0 : Matrix Y Y ℂ) * 1 + 1 * 0 = 0 := by rw [zero_mul, mul_zero, add_zero]
  have h3 : (1 : Matrix Y Y ℂ) * 0 + 0 * 1 = 0 := by rw [mul_zero, zero_mul, add_zero]
  have h4 : (1 : Matrix Y Y ℂ) * 1 + 0 * 0 = 1 := by rw [mul_one, mul_zero, add_zero]
  rw [h1, h2, h3, h4]
  exact Matrix.fromBlocks_one

theorem swapMatrix_mul_blockDiag (A B : Matrix Y Y ℂ) :
    swapMatrix Y * blockDiagMatrix Y Y A B = blockDiagMatrix Y Y B A * swapMatrix Y := by
  unfold swapMatrix blockDiagMatrix
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

/-- The rotation `[[C, -S], [S, C]]` with `C = rdiag c` and `S = rdiag s`. -/
def rotMatrix (c s : Y → ℝ) : Matrix (blockSumModel Y Y) (blockSumModel Y Y) ℂ :=
  Matrix.fromBlocks (rdiag Y c) (-rdiag Y s) (rdiag Y s) (rdiag Y c)

theorem rotMatrix_eq_add (c s : Y → ℝ) :
    rotMatrix Y c s = blockDiagMatrix Y Y (rdiag Y c) (rdiag Y c) +
      blockDiagMatrix Y Y (-rdiag Y s) (rdiag Y s) * swapMatrix Y := by
  unfold rotMatrix blockDiagMatrix swapMatrix
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  congr 1 <;> simp

theorem rotMatrix_conjTranspose (c s : Y → ℝ) :
    (rotMatrix Y c s)ᴴ = Matrix.fromBlocks (rdiag Y c) (rdiag Y s) (-rdiag Y s) (rdiag Y c) := by
  unfold rotMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg, rdiag_conjTranspose,
    rdiag_conjTranspose]

theorem rotMatrix_mem_unitaryGroup (c s : Y → ℝ) (hcs : ∀ w, c w * c w + s w * s w = 1) :
    rotMatrix Y c s ∈ Matrix.unitaryGroup (blockSumModel Y Y) ℂ := by
  have hCC : rdiag Y c * rdiag Y c + rdiag Y s * rdiag Y s = 1 := by
    rw [rdiag_mul, rdiag_mul, rdiag_add]
    exact (congrArg (rdiag Y) (funext hcs)).trans (rdiag_one Y)
  have hSC : rdiag Y s * rdiag Y c = rdiag Y c * rdiag Y s := by
    rw [rdiag_mul, rdiag_mul]
    exact congrArg (rdiag Y) (funext fun w => mul_comm (s w) (c w))
  have h12 : rdiag Y c * -rdiag Y s + rdiag Y s * rdiag Y c = 0 := by
    rw [mul_neg, hSC, neg_add_cancel]
  have h21 : -rdiag Y s * rdiag Y c + rdiag Y c * rdiag Y s = 0 := by
    rw [neg_mul, hSC, neg_add_cancel]
  have h22 : -rdiag Y s * -rdiag Y s + rdiag Y c * rdiag Y c = 1 := by
    rw [neg_mul_neg, add_comm, hCC]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, rotMatrix_conjTranspose]
  unfold rotMatrix
  rw [Matrix.fromBlocks_multiply, hCC, h12, h21, h22]
  exact Matrix.fromBlocks_one

/-! ## The commutator estimate -/

/-- Commutator of `X + W J` with `P`, when `J P = P' J`. -/
theorem comm_split {R : Type*} [Ring R] (X W J P P' : R) (hJ : J * P = P' * J) :
    (X + W * J) * P - P * (X + W * J) = (X * P - P * X) + (W * P' - P * W) * J := by
  rw [add_mul, mul_add, mul_assoc W J P, hJ, ← mul_assoc W P' J, ← mul_assoc P W J, sub_mul]
  abel

/-- **Commutator estimate.**  If `c` and `s` move by at most `η` along `σ⁻¹`
and `τ⁻¹`, and `σ⁻¹`, `τ⁻¹` agree on the support of `s`, then the rotation
`V` almost commutes with `diag (P_σ, P_τ)`: `‖V P - P V‖ ≤ 2η`
(`thm:exact-mf-residual`, `non_mf_group_notes.tex`). -/
theorem norm_rotMatrix_commutator_le (c s : Y → ℝ) (σ τ : Equiv.Perm Y) {η : ℝ}
    (hη : 0 ≤ η) (hcσ : ∀ w, |c w - c (σ⁻¹ w)| ≤ η) (hcτ : ∀ w, |c w - c (τ⁻¹ w)| ≤ η)
    (hsσ : ∀ w, |s w - s (σ⁻¹ w)| ≤ η) (hsτ : ∀ w, |s w - s (τ⁻¹ w)| ≤ η)
    (hsupp : ∀ w, s w ≠ 0 → σ⁻¹ w = τ⁻¹ w) :
    ‖rotMatrix Y c s * blockDiagMatrix Y Y (pmat Y σ) (pmat Y τ) -
      blockDiagMatrix Y Y (pmat Y σ) (pmat Y τ) * rotMatrix Y c s‖ ≤ 2 * η := by
  have h11 := comm_rdiag_pmat Y c σ
  have h22 := comm_rdiag_pmat Y c τ
  have hQ : -rdiag Y s * pmat Y τ - pmat Y σ * -rdiag Y s =
      rdiag Y (fun w => s (σ⁻¹ w) - s w) * pmat Y σ := by
    rw [neg_mul, mul_neg, neg_sub_neg, pmat_mul_rdiag,
      rdiag_mul_pmat_of_agree Y s τ σ (fun w hw => (hsupp w hw).symm), ← sub_mul, rdiag_sub]
  have hR : rdiag Y s * pmat Y σ - pmat Y τ * rdiag Y s =
      rdiag Y (fun w => s w - s (τ⁻¹ w)) * pmat Y τ := by
    rw [rdiag_mul_pmat_of_agree Y s σ τ hsupp, pmat_mul_rdiag, ← sub_mul, rdiag_sub]
  rw [rotMatrix_eq_add,
    comm_split _ _ _ _ _ (swapMatrix_mul_blockDiag Y (pmat Y σ) (pmat Y τ)),
    blockDiagMatrix_mul, blockDiagMatrix_mul, blockDiagMatrix_mul, blockDiagMatrix_mul,
    blockDiagMatrix_sub, blockDiagMatrix_sub, h11, h22, hQ, hR]
  refine (norm_add_le _ _).trans ?_
  rw [CStarRing.norm_mul_mem_unitary _ (swapMatrix_mem_unitaryGroup Y), l2_opNorm_blockDiag,
    l2_opNorm_blockDiag, two_mul]
  exact add_le_add
    (max_le (norm_rdiag_mul_pmat_le Y _ σ hη hcσ) (norm_rdiag_mul_pmat_le Y _ τ hη hcτ))
    (max_le
      (norm_rdiag_mul_pmat_le Y _ σ hη fun w => (abs_sub_comm _ _).trans_le (hsσ w))
      (norm_rdiag_mul_pmat_le Y _ τ hη hsτ))

end

end GroupApproximation.Full.NN01b
