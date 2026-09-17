import GroupApproximation.Sofic.OperatorMF
import GroupApproximation.Sofic.FiniteDimensionalResidual
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.CStarAlgebra.Matrix
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal phase unitaries

Manuscript `non_mf_group_notes.tex`, `thm:notes-abelian-boundary` (tex lines 2078--2160),
torsion-free half of the proof (tex lines 2098--2150). The proof puts phase unitaries on
`ℓ²(F_n)`:
`D_n(a) δ_y = e^{i θ(a) f_n(y)} δ_y` and `Λ_n(g) δ_y = δ_{q_n(g) y}`.

This file does the matrix algebra for these operators over an arbitrary finite model `Y`:

* `diagUnitary Y v` — the diagonal unitary `δ_y ↦ e^{i v(y)} δ_y`;
* `diagUnitary_add` — phases add;
* `opLength_diag_inv_mul_le` — operator-norm distance is at most the sup distance of the
  phases (`|e^{is} - e^{it}| ≤ |s - t|`);
* `two_le_opLength_diag` — a phase `π` at some point gives length at least `2`;
* `perm_conj_diagUnitary` — conjugating by a permutation unitary translates the phase.
-/

namespace GroupApproximation.Full.NN06

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : FiniteModel)

/-- The diagonal matrix `diag(e^{i v(y)})`. -/
def circleDiag (v : Y → ℝ) : Matrix Y Y ℂ :=
  Matrix.diagonal fun y => ((Circle.exp (v y) : Circle) : ℂ)

theorem circle_mul_star (w : Circle) : (w : ℂ) * star (w : ℂ) = 1 := by
  show (w : ℂ) * (starRingEnd ℂ) (w : ℂ) = 1
  rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]

theorem circleDiag_mem (v : Y → ℝ) : circleDiag Y v ∈ Matrix.unitaryGroup Y ℂ := by
  have hentry : ∀ y : Y,
      ((Circle.exp (v y) : Circle) : ℂ) * star ((Circle.exp (v y) : Circle) : ℂ) = 1 :=
    fun y => circle_mul_star _
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  show Matrix.diagonal (fun y => ((Circle.exp (v y) : Circle) : ℂ)) *
      (Matrix.diagonal (fun y => ((Circle.exp (v y) : Circle) : ℂ)))ᴴ = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  exact (congrArg Matrix.diagonal (funext hentry)).trans Matrix.diagonal_one

/-- The diagonal unitary `δ_y ↦ e^{i v(y)} δ_y` (tex line 2126, `D_n(a)`). -/
def diagUnitary (v : Y → ℝ) : Matrix.unitaryGroup Y ℂ :=
  ⟨circleDiag Y v, circleDiag_mem Y v⟩

theorem diagUnitary_add (v w : Y → ℝ) :
    diagUnitary Y (v + w) = diagUnitary Y v * diagUnitary Y w := by
  refine Subtype.ext ?_
  show Matrix.diagonal (fun y => ((Circle.exp ((v + w) y) : Circle) : ℂ)) =
    Matrix.diagonal (fun y => ((Circle.exp (v y) : Circle) : ℂ)) *
      Matrix.diagonal (fun y => ((Circle.exp (w y) : Circle) : ℂ))
  rw [Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun y => ?_)
  show ((Circle.exp (v y + w y) : Circle) : ℂ) =
    ((Circle.exp (v y) : Circle) : ℂ) * ((Circle.exp (w y) : Circle) : ℂ)
  rw [Circle.exp_add, Circle.coe_mul]

/-- `|e^{is} - e^{it}| ≤ |s - t|`. -/
theorem norm_circleExp_sub_le (s t : ℝ) :
    ‖((Circle.exp s : Circle) : ℂ) - ((Circle.exp t : Circle) : ℂ)‖ ≤ |s - t| := by
  have hst : t + (s - t) = s := by ring
  have hsplit : ((Circle.exp s : Circle) : ℂ) - ((Circle.exp t : Circle) : ℂ) =
      ((Circle.exp t : Circle) : ℂ) * (((Circle.exp (s - t) : Circle) : ℂ) - 1) := by
    rw [mul_sub, mul_one, ← Circle.coe_mul, ← Circle.exp_add, hst]
  rw [hsplit, norm_mul, Circle.norm_coe, one_mul, Circle.coe_exp, mul_comm,
    ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- Operator-norm distance between two diagonal unitaries is at most the sup distance of
their phases. -/
theorem opLength_diag_inv_mul_le {v w : Y → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y, |w y - v y| ≤ r) :
    opLength Y ((diagUnitary Y v)⁻¹ * diagUnitary Y w) ≤ r := by
  rw [opLength_inv_mul]
  show ‖Matrix.diagonal (fun y => ((Circle.exp (w y) : Circle) : ℂ)) -
      Matrix.diagonal (fun y => ((Circle.exp (v y) : Circle) : ℂ))‖ ≤ r
  rw [Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hr]
  intro y
  exact (norm_circleExp_sub_le (w y) (v y)).trans (h y)

/-- A phase `π` at one point forces operator-norm length at least `2`. -/
theorem two_le_opLength_diag {v : Y → ℝ} (y₀ : Y) (h : v y₀ = Real.pi) :
    2 ≤ opLength Y (diagUnitary Y v) := by
  show 2 ≤ ‖Matrix.diagonal (fun y => ((Circle.exp (v y) : Circle) : ℂ)) -
    Matrix.diagonal (fun _ => (1 : ℂ))‖
  rw [Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
  refine le_trans ?_
    (norm_le_pi_norm (fun y => ((Circle.exp (v y) : Circle) : ℂ) - 1) y₀)
  show 2 ≤ ‖((Circle.exp (v y₀) : Circle) : ℂ) - 1‖
  have hval : ((Circle.exp (v y₀) : Circle) : ℂ) - 1 = -2 := by
    rw [h, Circle.coe_exp, Complex.exp_pi_mul_I]
    ring
  exact le_of_eq (by rw [hval, norm_neg, Complex.norm_two])

/-- Conjugating a diagonal unitary by a permutation unitary translates its phase:
`Λ(σ) D(v) Λ(σ)* = D(v ∘ σ⁻¹)` (tex lines 2129--2133). -/
theorem perm_conj_diagUnitary (σ : Equiv.Perm Y) (v : Y → ℝ) :
    permUnitaryHom Y σ * diagUnitary Y v * (permUnitaryHom Y σ)⁻¹ =
      diagUnitary Y (fun y => v (σ⁻¹ y)) := by
  rw [← map_inv (permUnitaryHom Y) σ]
  refine Subtype.ext ?_
  show (σ⁻¹).permMatrix ℂ * Matrix.diagonal (fun y => ((Circle.exp (v y) : Circle) : ℂ)) *
      (σ⁻¹⁻¹).permMatrix ℂ =
    Matrix.diagonal (fun y => ((Circle.exp (v (σ⁻¹ y)) : Circle) : ℂ))
  rw [inv_inv, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul,
    Matrix.submatrix_submatrix]
  exact Matrix.submatrix_diagonal_equiv _ σ⁻¹

end

#audit_axioms circleDiag_mem
#audit_axioms diagUnitary_add
#audit_axioms norm_circleExp_sub_le
#audit_axioms opLength_diag_inv_mul_le
#audit_axioms two_le_opLength_diag
#audit_axioms perm_conj_diagUnitary

end GroupApproximation.Full.NN06
