import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Logic.Equiv.Fin.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The affine representation of a split extension (bh-met-26)

Let `κ : B → K^d` turn products into sums (`κ (a * b) = κ a + κ b`, `κ 1 = 0`) and intertwine
`φ` with a linear representation `ρ : Q →* GL_d(K)`:
`κ (φ q b) = ρ q *ᵥ κ b`.  Then
`x ↦ [[ρ x.right, κ x.left], [0, 1]]` is a group homomorphism `B ⋊[φ] Q →* GL_{d+1}(K)`,
and it is injective when both `κ` and `ρ` are.  This is the standard affine trick.  It is
generic: no commutativity or exponent hypotheses are used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open Matrix

section Affine

variable {B Q : Type*} [Group B] [Group Q] {φ : Q →* MulAut B} {K : Type*} [Field K] {d : ℕ}

/-- The affine block matrix `[[ρ x.right, κ x.left], [0, 1]]`. -/
def eAffineMatrix (κ : B → (Fin d → K)) (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (x : B ⋊[φ] Q) : Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) K :=
  fromBlocks (ρ x.right : Matrix (Fin d) (Fin d) K) (replicateCol (Fin 1) (κ x.left)) 0 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eAffineMatrix

theorem eAffineMatrix_mul (κ : B → (Fin d → K)) (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hadd : ∀ a b : B, κ (a * b) = κ a + κ b)
    (hκ : ∀ (q : Q) (b : B), κ (φ q b) = (ρ q : Matrix (Fin d) (Fin d) K) *ᵥ κ b)
    (x y : B ⋊[φ] Q) :
    eAffineMatrix κ ρ (x * y) = eAffineMatrix κ ρ x * eAffineMatrix κ ρ y := by
  have hA : (ρ (x * y).right : Matrix (Fin d) (Fin d) K) =
      (ρ x.right : Matrix (Fin d) (Fin d) K) * (ρ y.right : Matrix (Fin d) (Fin d) K) := by
    rw [SemidirectProduct.mul_right, map_mul, Units.val_mul]
  have hB : replicateCol (Fin 1) (κ (x * y).left) =
      (ρ x.right : Matrix (Fin d) (Fin d) K) * replicateCol (Fin 1) (κ y.left) +
        replicateCol (Fin 1) (κ x.left) := by
    rw [SemidirectProduct.mul_left, hadd, hκ, replicateCol_add, replicateCol_mulVec, add_comm]
  unfold eAffineMatrix
  rw [fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA, Matrix.mul_zero, add_zero]
  · rw [hB, Matrix.mul_one]
  · rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  · rw [Matrix.zero_mul, Matrix.mul_one, zero_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eAffineMatrix_mul

theorem eAffineMatrix_one (κ : B → (Fin d → K)) (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hzero : κ 1 = 0) : eAffineMatrix κ ρ (1 : B ⋊[φ] Q) = 1 := by
  unfold eAffineMatrix
  rw [SemidirectProduct.one_right, SemidirectProduct.one_left, map_one, Units.val_one, hzero,
    replicateCol_zero, fromBlocks_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eAffineMatrix_one

/-- The affine representation as a monoid homomorphism into block matrices. -/
def eAffineHom (κ : B → (Fin d → K)) (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hzero : κ 1 = 0) (hadd : ∀ a b : B, κ (a * b) = κ a + κ b)
    (hκ : ∀ (q : Q) (b : B), κ (φ q b) = (ρ q : Matrix (Fin d) (Fin d) K) *ᵥ κ b) :
    (B ⋊[φ] Q) →* Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) K where
  toFun := eAffineMatrix κ ρ
  map_one' := eAffineMatrix_one κ ρ hzero
  map_mul' := eAffineMatrix_mul κ ρ hadd hκ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eAffineHom

theorem eAffineHom_injective (κ : B → (Fin d → K)) (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hzero : κ 1 = 0) (hadd : ∀ a b : B, κ (a * b) = κ a + κ b)
    (hκ : ∀ (q : Q) (b : B), κ (φ q b) = (ρ q : Matrix (Fin d) (Fin d) K) *ᵥ κ b)
    (hκi : Function.Injective κ) (hρi : Function.Injective ρ) :
    Function.Injective (eAffineHom κ ρ hzero hadd hκ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : fromBlocks (ρ x.right : Matrix (Fin d) (Fin d) K)
      (replicateCol (Fin 1) (κ x.left)) 0 1 =
        fromBlocks (1 : Matrix (Fin d) (Fin d) K) 0 0 (1 : Matrix (Fin 1) (Fin 1) K) :=
    hx.trans fromBlocks_one.symm
  obtain ⟨hA, hB, -, -⟩ := fromBlocks_inj.mp hx'
  have hr : x.right = 1 := hρi (by rw [map_one]; exact Units.ext hA)
  have hl : x.left = 1 := hκi (by
    rw [hzero]
    exact replicateCol_injective (hB.trans replicateCol_zero.symm))
  exact SemidirectProduct.ext hl hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eAffineHom_injective

/-- The affine representation into `GL_{d+1}(K)`. -/
noncomputable def eAffineGL (κ : B → (Fin d → K)) (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hzero : κ 1 = 0) (hadd : ∀ a b : B, κ (a * b) = κ a + κ b)
    (hκ : ∀ (q : Q) (b : B), κ (φ q b) = (ρ q : Matrix (Fin d) (Fin d) K) *ᵥ κ b) :
    (B ⋊[φ] Q) →* GeneralLinearGroup (Fin (d + 1)) K :=
  ((reindexRingEquiv K (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).toMonoidHom.comp
    (eAffineHom κ ρ hzero hadd hκ)).toHomUnits

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eAffineGL

theorem eAffineGL_injective (κ : B → (Fin d → K)) (ρ : Q →* GeneralLinearGroup (Fin d) K)
    (hzero : κ 1 = 0) (hadd : ∀ a b : B, κ (a * b) = κ a + κ b)
    (hκ : ∀ (q : Q) (b : B), κ (φ q b) = (ρ q : Matrix (Fin d) (Fin d) K) *ᵥ κ b)
    (hκi : Function.Injective κ) (hρi : Function.Injective ρ) :
    Function.Injective (eAffineGL κ ρ hzero hadd hκ) := by
  intro x y hxy
  have h1 : reindexRingEquiv K (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))
      (eAffineHom κ ρ hzero hadd hκ x) =
        reindexRingEquiv K (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))
          (eAffineHom κ ρ hzero hadd hκ y) :=
    congrArg Units.val hxy
  exact eAffineHom_injective κ ρ hzero hadd hκ hκi hρi
    ((reindexRingEquiv K (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))).injective h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eAffineGL_injective

end Affine

end GroupApproximation.BooneHigman.Metabelian.Coprimary
