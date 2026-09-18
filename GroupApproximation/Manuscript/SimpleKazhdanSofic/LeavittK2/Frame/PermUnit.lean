import Mathlib.Data.Matrix.PEquiv
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Group.Pi.Lemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Permutation units and the action of `GL_n(A)` on column vectors

Lane `sk-leavitt-07` (carto `sk-leavitt`), groundwork for the ordered frame complex `X_n(A)`
of Khanh (arXiv:2609.08428v1), proof of Theorem 5.1 (tex l.424–446).

The group `GL_n(A)` is `(Matrix (Fin n) (Fin n) A)ˣ`.  It acts on `Fin n → A` through the
Mathlib module structure `Matrix.instModule...` (`A • v = A *ᵥ v`, `Matrix.smul_eq_mulVec`)
and `Units.instMulAction`, so `g • v = (g : Matrix _ _ A) *ᵥ v` holds by `rfl`.

* `framePermUnit σ`: the permutation matrix `σ.toPEquiv.toMatrix` as a unit, with
  `framePermUnit σ • a = a ∘ σ`.  In particular it sends `e_j` to `e_{σ⁻¹ j}`.
  It is an anti-homomorphism: `framePermUnit (σ * τ) = framePermUnit τ * framePermUnit σ`.
* `smul_single_eq_self_iff`: `g` fixes `e_j` iff the `j`-th column of `g` is `e_j`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {A : Type*} [Ring A] {n : ℕ}

theorem frame_smul_def (g : (Matrix (Fin n) (Fin n) A)ˣ) (v : Fin n → A) :
    g • v = (g : Matrix (Fin n) (Fin n) A) *ᵥ v := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frame_smul_def

/-- The permutation matrix of `σ`, as a unit of the matrix ring. -/
def framePermUnit (σ : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) A)ˣ where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    have h := (PEquiv.toMatrix_trans (α := A) σ.toPEquiv σ.symm.toPEquiv).symm
    rw [← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl] at h
    exact h
  inv_val := by
    have h := (PEquiv.toMatrix_trans (α := A) σ.symm.toPEquiv σ.toPEquiv).symm
    rw [← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl] at h
    exact h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.framePermUnit

theorem framePermUnit_val (σ : Equiv.Perm (Fin n)) :
    ((framePermUnit σ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) =
      σ.toPEquiv.toMatrix := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.framePermUnit_val

theorem framePermUnit_one :
    (framePermUnit (1 : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) A)ˣ) = 1 := by
  apply Units.ext
  show (1 : Equiv.Perm (Fin n)).toPEquiv.toMatrix = (1 : Matrix (Fin n) (Fin n) A)
  rw [Equiv.Perm.one_def, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.framePermUnit_one

/-- Permutation units form an anti-homomorphism (`σ * τ` means "first `τ`, then `σ`"). -/
theorem framePermUnit_mul (σ τ : Equiv.Perm (Fin n)) :
    (framePermUnit (σ * τ) : (Matrix (Fin n) (Fin n) A)ˣ) =
      framePermUnit τ * framePermUnit σ := by
  apply Units.ext
  rw [Units.val_mul]
  show (σ * τ).toPEquiv.toMatrix =
    (τ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) * σ.toPEquiv.toMatrix
  rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.Perm.mul_def]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.framePermUnit_mul

theorem framePermUnit_mul_self_of_mul_self {σ : Equiv.Perm (Fin n)} (hσ : σ * σ = 1) :
    (framePermUnit σ : (Matrix (Fin n) (Fin n) A)ˣ) * framePermUnit σ = 1 := by
  rw [← framePermUnit_mul, hσ, framePermUnit_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.framePermUnit_mul_self_of_mul_self

theorem framePermUnit_smul (σ : Equiv.Perm (Fin n)) (a : Fin n → A) :
    (framePermUnit σ : (Matrix (Fin n) (Fin n) A)ˣ) • a = a ∘ σ := by
  show (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) A) *ᵥ a = a ∘ σ
  exact PEquiv.toMatrix_toPEquiv_mulVec σ a

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.framePermUnit_smul

/-- `framePermUnit σ` sends the standard basis vector `e_j` to `e_{σ⁻¹ j}`. -/
theorem framePermUnit_smul_single (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    (framePermUnit σ : (Matrix (Fin n) (Fin n) A)ˣ) • (Pi.single j 1 : Fin n → A) =
      Pi.single (σ.symm j) 1 := by
  rw [framePermUnit_smul, Pi.single_comp_equiv]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.framePermUnit_smul_single

/-- A unit fixes `e_j` iff its `j`-th column is `e_j`. -/
theorem smul_single_eq_self_iff (g : (Matrix (Fin n) (Fin n) A)ˣ) (j : Fin n) :
    g • (Pi.single j 1 : Fin n → A) = Pi.single j 1 ↔
      ∀ i, (g : Matrix (Fin n) (Fin n) A) i j = (Pi.single j 1 : Fin n → A) i := by
  constructor
  · intro h i
    have h' : (g : Matrix (Fin n) (Fin n) A) *ᵥ Pi.single j 1 = Pi.single j 1 := h
    rw [Matrix.mulVec_single_one] at h'
    exact congrFun h' i
  · intro h
    show (g : Matrix (Fin n) (Fin n) A) *ᵥ Pi.single j 1 = Pi.single j 1
    rw [Matrix.mulVec_single_one]
    exact funext h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.smul_single_eq_self_iff

theorem frame_single_castSucc {m : ℕ} (j i : Fin m) :
    (Pi.single (Fin.castSucc j) 1 : Fin (m + 1) → A) (Fin.castSucc i) =
      (Pi.single j 1 : Fin m → A) i := by
  by_cases h : i = j
  · rw [h, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne ((Fin.castSucc_injective m).ne h)]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frame_single_castSucc

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
