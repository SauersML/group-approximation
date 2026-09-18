import GroupApproximation.SteinbergFP.Doubling
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Morita isomorphisms from a binary Leavitt family

A binary Leavitt family `s₀, s₁, t₀, t₁` of `S` gives the ring isomorphism
`ψ : S ≃+* M₂(S)`, `ψ(r)_{st} = t_s r s_t`, with inverse `B ↦ Σ_{a,b} s_a B_{ab} t_b`
(`moritaTwo`).  Iterating, `M_{2^j}(S) ≃+* S` for every `j` (`morita`).

The scalar matrices `s_b · 1`, `t_b · 1` form a binary Leavitt family of `M_ι(S)`
(`matrixLeavitt`).  This is part 2 of the research node
`leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`, with `k = 2^j`.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

variable {S : Type*} [Ring S] (L : LeavittFamily S)

theorem psi_one : L.psi 1 = 1 := by
  ext s t
  simp only [LeavittFamily.psi, Matrix.of_apply, mul_one, L.tv_mul_sv, Matrix.one_apply]

theorem psi_zero : L.psi 0 = 0 := by
  ext s t
  simp [LeavittFamily.psi]

/-- `ψ` as a ring homomorphism. -/
def psiHom : S →+* Matrix (Fin 2) (Fin 2) S where
  toFun := L.psi
  map_one' := psi_one L
  map_mul' a b := (L.psi_mul a b).symm
  map_zero' := psi_zero L
  map_add' := L.psi_add

/-- `θ(B) = Σ_{a,b} s_a B_{ab} t_b`. -/
def theta (B : Matrix (Fin 2) (Fin 2) S) : S :=
  ∑ a : Fin 2, ∑ b : Fin 2, L.sv a * B a b * L.tv b

theorem theta_psi (r : S) : theta L (L.psi r) = r := by
  simp only [theta, LeavittFamily.psi, Matrix.of_apply, Fin.sum_univ_two, LeavittFamily.sv,
    LeavittFamily.tv, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc _ = (L.s0 * L.t0 + L.s1 * L.t1) * r * (L.s0 * L.t0 + L.s1 * L.t1) := by noncomm_ring
    _ = r := by rw [L.sum_range, one_mul, mul_one]

theorem psi_theta (B : Matrix (Fin 2) (Fin 2) S) : L.psi (theta L B) = B := by
  ext s t
  simp only [LeavittFamily.psi, theta, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  have key : ∀ a b : Fin 2, L.tv s * (L.sv a * B a b * L.tv b) * L.sv t =
      (L.tv s * L.sv a) * B a b * (L.tv b * L.sv t) := fun a b ↦ by noncomm_ring
  simp only [key, L.tv_mul_sv]
  fin_cases s <;> fin_cases t <;> simp

/-- **`M₂(S) ≃+* S`.** -/
def moritaTwo : Matrix (Fin 2) (Fin 2) S ≃+* S :=
  (RingEquiv.ofBijective (psiHom L)
    ⟨fun a b h ↦ by
      rw [← theta_psi L a, ← theta_psi L b]
      exact congrArg (theta L) h,
    fun B ↦ ⟨theta L B, psi_theta L B⟩⟩).symm

/-- `Fin (2^(j+1)) ≃ Fin (2^j) × Fin 2`. -/
def finPowSuccEquiv (j : ℕ) : Fin (2 ^ (j + 1)) ≃ Fin (2 ^ j) × Fin 2 :=
  (finCongr (pow_succ 2 j)).trans finProdFinEquiv.symm

/-- **`M_{2^j}(S) ≃+* S`.** -/
def morita : (j : ℕ) → Matrix (Fin (2 ^ j)) (Fin (2 ^ j)) S ≃+* S
  | 0 => (Matrix.reindexRingEquiv S (finCongr (pow_zero 2))).trans Matrix.uniqueRingEquiv
  | j + 1 => (Matrix.reindexRingEquiv S (finPowSuccEquiv j)).trans
      ((Matrix.compRingEquiv (Fin (2 ^ j)) (Fin 2) S).symm.trans
        ((moritaTwo L).mapMatrix.trans (morita j)))

section Scalar

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The scalar binary Leavitt family of `M_ι(S)`. -/
def matrixLeavitt : LeavittFamily (Matrix ι ι S) where
  s0 := Matrix.diagonal fun _ ↦ L.s0
  s1 := Matrix.diagonal fun _ ↦ L.s1
  t0 := Matrix.diagonal fun _ ↦ L.t0
  t1 := Matrix.diagonal fun _ ↦ L.t1
  t0_s0 := by rw [Matrix.diagonal_mul_diagonal, L.t0_s0, Matrix.diagonal_one]
  t0_s1 := by rw [Matrix.diagonal_mul_diagonal, L.t0_s1, Matrix.diagonal_zero]
  t1_s0 := by rw [Matrix.diagonal_mul_diagonal, L.t1_s0, Matrix.diagonal_zero]
  t1_s1 := by rw [Matrix.diagonal_mul_diagonal, L.t1_s1, Matrix.diagonal_one]
  sum_range := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add,
      L.sum_range, Matrix.diagonal_one]

theorem matrixLeavitt_tv (s : Fin 2) :
    (matrixLeavitt L ι).tv s = Matrix.diagonal fun _ ↦ L.tv s := by
  fin_cases s <;> rfl

end Scalar

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.morita
#audit_axioms GroupApproximation.SteinbergFP.matrixLeavitt
