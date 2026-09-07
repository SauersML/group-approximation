import GroupApproximation.Manuscript.OneSidedMFRadical.HilbertSchmidtAdMatrix

/-!
# Operators on the Hilbert--Schmidt space, acting on matrices

`non_mf_groups_exist.tex`, the rewritten proof of Theorem `thm:transport`,
works throughout with operators on the Hilbert space
`(M_{d_n}(ℂ), ‖·‖₂)` applied to matrices: the projections `P_n`, the maps
`Ad(V_n(ℓ))`, and the displayed estimates

> `limsup_n ‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ ≤ ε`,
> `‖P_n x_n − x_n‖₂ → 0`,
> `‖Ad(V_n(ℓ))x_n − x_n‖₂ ≤ 2‖x_n − P_nx_n‖₂ + ‖Ad(V_n(ℓ))P_n − P_n‖ ‖x_n‖₂`.

`Manuscript/OneSidedMFRadical/HilbertSchmidtAdMatrix.lean` fixed the printed
choice of matrix units, so such an operator *is* a matrix of size `d_n²`.
This file is the action: `applyOp M a` is the matrix `M` acts on `a` as, the
printed `M x`.  What it supplies:

* `applyOp_one`, `applyOp_mul`, `applyOp_sub`, `applyOp_smul`, `applyOp_sum`
  — the action is unital, multiplicative and linear, all of it `mulVec`
  algebra with no `WithLp` bookkeeping;
* `applyOp_adMatrix` — the printed `Ad(V) x = V x V*`;
* `hsNorm_applyOp_le` — the printed `‖M x‖₂ ≤ ‖M‖ ‖x‖₂`, the one estimate
  that has to cross into `EuclideanSpace`, and the only place the
  normalization factor `(card Y)^{1/2}` appears.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace HilbertSchmidtOperatorAction

open Filter Matrix Topology
open HilbertSchmidtAdMatrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : FiniteModel)

/-! ## The action -/

/-- The vectorization of a matrix, as a plain function on the square index. -/
def vecFun (a : Matrix Y Y ℂ) : Y × Y → ℂ := fun p ↦ a p.1 p.2

/-- **The printed `M x`.**  An operator on the Hilbert--Schmidt space, given
by its matrix in the matrix-unit basis, applied to a matrix. -/
def applyOp (M : Matrix (Y × Y) (Y × Y) ℂ) (a : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  Matrix.of fun i j ↦ (M *ᵥ vecFun Y a) (i, j)

@[simp] theorem applyOp_apply (M : Matrix (Y × Y) (Y × Y) ℂ)
    (a : Matrix Y Y ℂ) (i j : Y) :
    applyOp Y M a i j = (M *ᵥ vecFun Y a) (i, j) := rfl

@[simp] theorem vecFun_applyOp (M : Matrix (Y × Y) (Y × Y) ℂ)
    (a : Matrix Y Y ℂ) : vecFun Y (applyOp Y M a) = M *ᵥ vecFun Y a := rfl

theorem applyOp_one (a : Matrix Y Y ℂ) : applyOp Y 1 a = a := by
  ext i j
  rw [applyOp_apply, Matrix.one_mulVec]
  rfl

theorem applyOp_mul (M N : Matrix (Y × Y) (Y × Y) ℂ) (a : Matrix Y Y ℂ) :
    applyOp Y (M * N) a = applyOp Y M (applyOp Y N a) := by
  ext i j
  rw [applyOp_apply, applyOp_apply, vecFun_applyOp,
    Matrix.mulVec_mulVec (vecFun Y a) M N]

theorem applyOp_sub (M N : Matrix (Y × Y) (Y × Y) ℂ) (a : Matrix Y Y ℂ) :
    applyOp Y (M - N) a = applyOp Y M a - applyOp Y N a := by
  ext i j
  rw [applyOp_apply, Matrix.sub_mulVec, Matrix.sub_apply, Pi.sub_apply,
    applyOp_apply, applyOp_apply]

theorem applyOp_smul (c : ℂ) (M : Matrix (Y × Y) (Y × Y) ℂ)
    (a : Matrix Y Y ℂ) : applyOp Y (c • M) a = c • applyOp Y M a := by
  ext i j
  rw [applyOp_apply, Matrix.smul_mulVec, Matrix.smul_apply, Pi.smul_apply,
    applyOp_apply]

theorem applyOp_add (M N : Matrix (Y × Y) (Y × Y) ℂ) (a : Matrix Y Y ℂ) :
    applyOp Y (M + N) a = applyOp Y M a + applyOp Y N a := by
  ext i j
  rw [applyOp_apply, Matrix.add_mulVec, Matrix.add_apply, Pi.add_apply,
    applyOp_apply, applyOp_apply]

theorem applyOp_zero (a : Matrix Y Y ℂ) :
    applyOp Y (0 : Matrix (Y × Y) (Y × Y) ℂ) a = 0 := by
  ext i j
  rw [applyOp_apply, Matrix.zero_mulVec]
  simp

theorem applyOp_sum {ι : Type*} (F : Finset ι)
    (M : ι → Matrix (Y × Y) (Y × Y) ℂ) (a : Matrix Y Y ℂ) :
    applyOp Y (∑ s ∈ F, M s) a = ∑ s ∈ F, applyOp Y (M s) a := by
  classical
  refine Finset.induction_on F ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, applyOp_zero]
  · intro b s hb ih
    rw [Finset.sum_insert hb, Finset.sum_insert hb, applyOp_add, ih]

/-- **The printed `Ad(V) x = V x V*`.** -/
theorem applyOp_adMatrix (V : Matrix Y Y ℂ) (a : Matrix Y Y ℂ) :
    applyOp Y (adMatrix Y V) a = V * a * Vᴴ := by
  have h := unvec_adMatrix_mulVec Y V (WithLp.toLp 2 (vecFun Y a))
  have hu : unvec Y (WithLp.toLp 2 (vecFun Y a)) = a := rfl
  rw [hu] at h
  exact h

/-! ## The printed operator-norm estimate `‖M x‖₂ ≤ ‖M‖ ‖x‖₂` -/

/-- The vectorization as an element of the Euclidean space. -/
def vecE (a : Matrix Y Y ℂ) : EuclideanSpace ℂ (Y × Y) :=
  WithLp.toLp 2 (vecFun Y a)

@[simp] theorem unvec_vecE (a : Matrix Y Y ℂ) : unvec Y (vecE Y a) = a := rfl

theorem toEuclideanCLM_vecE (M : Matrix (Y × Y) (Y × Y) ℂ)
    (a : Matrix Y Y ℂ) :
    Matrix.toEuclideanCLM (n := Y × Y) (𝕜 := ℂ) M (vecE Y a)
      = vecE Y (applyOp Y M a) := rfl

theorem norm_vecE (hY : 0 < Fintype.card Y) (a : Matrix Y Y ℂ) :
    ‖vecE Y a‖ = Real.sqrt (Fintype.card Y) * hsNorm Y a := by
  have h1 : ‖vecE Y a‖ ^ 2 = (Fintype.card Y : ℝ) * hsNormSq Y a := by
    have h := norm_sq_eq_card_mul_hsNormSq Y hY (vecE Y a)
    rwa [unvec_vecE] at h
  have h2 : (Real.sqrt (Fintype.card Y) * hsNorm Y a) ^ 2
      = (Fintype.card Y : ℝ) * hsNormSq Y a := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card Y : ℝ)),
      TracialUltraproduct.sq_hsNorm]
  have hnn : (0 : ℝ) ≤ Real.sqrt (Fintype.card Y) * hsNorm Y a :=
    mul_nonneg (Real.sqrt_nonneg _) (hsNorm_nonneg Y a)
  nlinarith [h1, h2, norm_nonneg (vecE Y a), hnn]

theorem vecE_add (a b : Matrix Y Y ℂ) :
    vecE Y (a + b) = vecE Y a + vecE Y b := rfl

theorem vecE_smul (c : ℂ) (a : Matrix Y Y ℂ) :
    vecE Y (c • a) = c • vecE Y a := rfl

/-- **The triangle inequality for the printed `‖·‖₂`.**  The vectorization is
an isometry onto a Euclidean space up to the factor `(card Y)^{1/2}`, so the
normalized Hilbert--Schmidt norm inherits it with no constant. -/
theorem hsNorm_add_le (hY : 0 < Fintype.card Y) (a b : Matrix Y Y ℂ) :
    hsNorm Y (a + b) ≤ hsNorm Y a + hsNorm Y b := by
  have hc : (0 : ℝ) < Real.sqrt (Fintype.card Y) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hY)
  have h := norm_add_le (vecE Y a) (vecE Y b)
  rw [← vecE_add, norm_vecE Y hY (a + b), norm_vecE Y hY a,
    norm_vecE Y hY b] at h
  have h2 : Real.sqrt (Fintype.card Y) * hsNorm Y (a + b)
      ≤ Real.sqrt (Fintype.card Y) * (hsNorm Y a + hsNorm Y b) := by
    calc Real.sqrt (Fintype.card Y) * hsNorm Y (a + b)
        ≤ Real.sqrt (Fintype.card Y) * hsNorm Y a
          + Real.sqrt (Fintype.card Y) * hsNorm Y b := h
      _ = Real.sqrt (Fintype.card Y) * (hsNorm Y a + hsNorm Y b) := by ring
  exact le_of_mul_le_mul_left h2 hc

theorem hsNorm_smul (hY : 0 < Fintype.card Y) (c : ℂ) (a : Matrix Y Y ℂ) :
    hsNorm Y (c • a) = ‖c‖ * hsNorm Y a := by
  have hc : (0 : ℝ) < Real.sqrt (Fintype.card Y) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hY)
  have h : ‖vecE Y (c • a)‖ = ‖c‖ * ‖vecE Y a‖ := by
    rw [vecE_smul, norm_smul]
  rw [norm_vecE Y hY (c • a), norm_vecE Y hY a] at h
  have h2 : Real.sqrt (Fintype.card Y) * hsNorm Y (c • a)
      = Real.sqrt (Fintype.card Y) * (‖c‖ * hsNorm Y a) := by
    rw [h]; ring
  exact mul_left_cancel₀ (ne_of_gt hc) h2

theorem hsNorm_sum_le (hY : 0 < Fintype.card Y) {ι : Type*} (F : Finset ι)
    (f : ι → Matrix Y Y ℂ) :
    hsNorm Y (∑ s ∈ F, f s) ≤ ∑ s ∈ F, hsNorm Y (f s) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact le_of_eq (TracialUltraproduct.hsNorm_zero Y)
  · intro b s hb ih
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    refine (hsNorm_add_le Y hY _ _).trans ?_
    linarith [ih]

/-- **The printed `‖M x‖₂ ≤ ‖M‖ ‖x‖₂`.**  The `L2Operator` norm of the matrix
of an operator on the Hilbert--Schmidt space bounds its action in `‖·‖₂`; the
normalization factor cancels between the two sides. -/
theorem hsNorm_applyOp_le (hY : 0 < Fintype.card Y)
    (M : Matrix (Y × Y) (Y × Y) ℂ) (a : Matrix Y Y ℂ) :
    hsNorm Y (applyOp Y M a) ≤ ‖M‖ * hsNorm Y a := by
  have hc : (0 : ℝ) < Real.sqrt (Fintype.card Y) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hY)
  have hle := (Matrix.toEuclideanCLM (n := Y × Y) (𝕜 := ℂ) M).le_opNorm
    (vecE Y a)
  rw [Matrix.l2_opNorm_toEuclideanCLM, toEuclideanCLM_vecE,
    norm_vecE Y hY (applyOp Y M a), norm_vecE Y hY a] at hle
  have h3 : Real.sqrt (Fintype.card Y) * hsNorm Y (applyOp Y M a)
      ≤ Real.sqrt (Fintype.card Y) * (‖M‖ * hsNorm Y a) := by
    calc Real.sqrt (Fintype.card Y) * hsNorm Y (applyOp Y M a)
        ≤ ‖M‖ * (Real.sqrt (Fintype.card Y) * hsNorm Y a) := hle
      _ = Real.sqrt (Fintype.card Y) * (‖M‖ * hsNorm Y a) := by ring
  exact le_of_mul_le_mul_left h3 hc

end

end HilbertSchmidtOperatorAction
end OneSidedMFRadical
end Manuscript
end GroupApproximation
