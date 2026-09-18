import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Logic.Equiv.Fin.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Unipotent translations: from additive to conjugation representations (bh-met-79)

Let `ι : M →+ K^d` be injective and intertwine an action `act` of `Q` on `M` with a linear
representation `ρ : Q →* GL_d(K)`, i.e. `ι (act q m) = ρ q *ᵥ ι m`.  Then the unipotent
translations `m ↦ [[1, ι m], [0, 1]]` form an injective group homomorphism
`Multiplicative M →* GL_{d+1}(K)`.  Conjugating by `[[ρ q, 0], [0, 1]]` realises `act q`.
This is the standard translation trick.  It uses no commutativity or exponent hypotheses, and
it does not need `ρ` to be injective.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open Matrix

section Trans

variable {M Q K : Type*} [AddCommGroup M] [Group Q] [Field K] {d : ℕ}

/-- The unipotent translation matrix `[[1, v], [0, 1]]`. -/
def eHighCoprimaryTrans (v : Fin d → K) : Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) K :=
  fromBlocks 1 (replicateCol (Fin 1) v) 0 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryTrans

theorem eHighCoprimaryTrans_zero : eHighCoprimaryTrans (0 : Fin d → K) = 1 := by
  unfold eHighCoprimaryTrans
  rw [replicateCol_zero, fromBlocks_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryTrans_zero

theorem eHighCoprimaryTrans_add (v w : Fin d → K) :
    eHighCoprimaryTrans (v + w) = eHighCoprimaryTrans v * eHighCoprimaryTrans w := by
  unfold eHighCoprimaryTrans
  rw [fromBlocks_multiply, fromBlocks_inj]
  refine ⟨by simp, ?_, by simp, by simp⟩
  rw [Matrix.one_mul, Matrix.mul_one, replicateCol_add, add_comm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryTrans_add

/-- The block-diagonal matrix `[[A, 0], [0, 1]]`. -/
def eHighCoprimaryDiag (A : Matrix (Fin d) (Fin d) K) :
    Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) K :=
  fromBlocks A 0 0 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryDiag

theorem eHighCoprimaryDiag_one : eHighCoprimaryDiag (1 : Matrix (Fin d) (Fin d) K) = 1 := by
  unfold eHighCoprimaryDiag
  exact fromBlocks_one

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryDiag_one

theorem eHighCoprimaryDiag_mul (A B : Matrix (Fin d) (Fin d) K) :
    eHighCoprimaryDiag (A * B) = eHighCoprimaryDiag A * eHighCoprimaryDiag B := by
  unfold eHighCoprimaryDiag
  rw [fromBlocks_multiply, fromBlocks_inj]
  exact ⟨by simp, by simp, by simp, by simp⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryDiag_mul

theorem eHighCoprimaryTrans_mul_diag (A : Matrix (Fin d) (Fin d) K) (v : Fin d → K) :
    eHighCoprimaryTrans (A *ᵥ v) * eHighCoprimaryDiag A =
      eHighCoprimaryDiag A * eHighCoprimaryTrans v := by
  unfold eHighCoprimaryTrans eHighCoprimaryDiag
  rw [fromBlocks_multiply, fromBlocks_multiply, replicateCol_mulVec, fromBlocks_inj]
  exact ⟨by simp, by simp, by simp, by simp⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryTrans_mul_diag

/-- The translation representation `m ↦ [[1, ι m], [0, 1]]` as a monoid homomorphism. -/
def eHighCoprimaryTransHom (ι : M →+ (Fin d → K)) :
    Multiplicative M →* Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) K where
  toFun x := eHighCoprimaryTrans (ι (Multiplicative.toAdd x))
  map_one' := by
    show eHighCoprimaryTrans (ι (Multiplicative.toAdd (1 : Multiplicative M))) = 1
    rw [toAdd_one, map_zero, eHighCoprimaryTrans_zero]
  map_mul' x y := by
    show eHighCoprimaryTrans (ι (Multiplicative.toAdd (x * y))) =
      eHighCoprimaryTrans (ι (Multiplicative.toAdd x)) *
        eHighCoprimaryTrans (ι (Multiplicative.toAdd y))
    rw [toAdd_mul, map_add, eHighCoprimaryTrans_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryTransHom

/-- The block-diagonal representation `q ↦ [[ρ q, 0], [0, 1]]` as a monoid homomorphism. -/
def eHighCoprimaryDiagHom (ρ : Q →* GeneralLinearGroup (Fin d) K) :
    Q →* Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) K where
  toFun q := eHighCoprimaryDiag (ρ q : Matrix (Fin d) (Fin d) K)
  map_one' := by
    show eHighCoprimaryDiag (ρ 1 : Matrix (Fin d) (Fin d) K) = 1
    rw [map_one, Units.val_one, eHighCoprimaryDiag_one]
  map_mul' q r := by
    show eHighCoprimaryDiag (ρ (q * r) : Matrix (Fin d) (Fin d) K) =
      eHighCoprimaryDiag (ρ q : Matrix (Fin d) (Fin d) K) *
        eHighCoprimaryDiag (ρ r : Matrix (Fin d) (Fin d) K)
    rw [map_mul, Units.val_mul, eHighCoprimaryDiag_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryDiagHom

variable (K d) in
/-- The reindexing ring isomorphism from `Fin d ⊕ Fin 1` to `Fin (d + 1)` indices. -/
noncomputable def eHighCoprimaryReindex :
    Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) K ≃+* Matrix (Fin (d + 1)) (Fin (d + 1)) K :=
  reindexRingEquiv K (finSumFinEquiv : Fin d ⊕ Fin 1 ≃ Fin (d + 1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryReindex

/-- **Translation trick.**  An injective additive representation `ι` intertwining `act` with
`ρ` gives an injective `κ' : Multiplicative M →* GL_{d+1}(K)` and `ρ' : Q →* GL_{d+1}(K)`
such that conjugation by `ρ' q` realises `act q`. -/
theorem eHighCoprimary_exists_gl_of_additive (act : Q → M → M) (ι : M →+ (Fin d → K))
    (ρ : Q →* GeneralLinearGroup (Fin d) K) (hι : Function.Injective ι)
    (hequiv : ∀ (q : Q) (m : M), ι (act q m) = (ρ q : Matrix (Fin d) (Fin d) K) *ᵥ ι m) :
    ∃ (κ' : Multiplicative M →* GeneralLinearGroup (Fin (d + 1)) K)
      (ρ' : Q →* GeneralLinearGroup (Fin (d + 1)) K), Function.Injective κ' ∧
        ∀ (q : Q) (m : M), κ' (Multiplicative.ofAdd (act q m)) =
          ρ' q * κ' (Multiplicative.ofAdd m) * (ρ' q)⁻¹ := by
  refine ⟨((eHighCoprimaryReindex K d).toMonoidHom.comp
      (eHighCoprimaryTransHom ι)).toHomUnits,
    ((eHighCoprimaryReindex K d).toMonoidHom.comp
      (eHighCoprimaryDiagHom ρ)).toHomUnits, ?_, ?_⟩
  · refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
    have h1 : eHighCoprimaryReindex K d
        (eHighCoprimaryTransHom ι x) =
          eHighCoprimaryReindex K d 1 := by
      rw [map_one]
      exact congrArg Units.val hx
    have h2 : fromBlocks (1 : Matrix (Fin d) (Fin d) K)
        (replicateCol (Fin 1) (ι (Multiplicative.toAdd x))) 0 1 =
          fromBlocks (1 : Matrix (Fin d) (Fin d) K) 0 0 (1 : Matrix (Fin 1) (Fin 1) K) :=
      ((eHighCoprimaryReindex K d).injective h1).trans
        fromBlocks_one.symm
    obtain ⟨-, hB, -, -⟩ := fromBlocks_inj.mp h2
    have h3 : Multiplicative.toAdd x = 0 := hι (by
      rw [map_zero]
      exact replicateCol_injective (hB.trans replicateCol_zero.symm))
    exact Multiplicative.toAdd.injective (by rw [h3, toAdd_one])
  · intro q m
    have h : eHighCoprimaryTransHom ι (Multiplicative.ofAdd (act q m)) *
        eHighCoprimaryDiagHom ρ q =
          eHighCoprimaryDiagHom ρ q * eHighCoprimaryTransHom ι (Multiplicative.ofAdd m) := by
      show eHighCoprimaryTrans (ι (act q m)) *
          eHighCoprimaryDiag (ρ q : Matrix (Fin d) (Fin d) K) =
        eHighCoprimaryDiag (ρ q : Matrix (Fin d) (Fin d) K) * eHighCoprimaryTrans (ι m)
      rw [hequiv]
      exact eHighCoprimaryTrans_mul_diag _ _
    refine eq_mul_inv_of_mul_eq (Units.ext ?_)
    show eHighCoprimaryReindex K d (eHighCoprimaryTransHom ι (Multiplicative.ofAdd (act q m))) *
        eHighCoprimaryReindex K d (eHighCoprimaryDiagHom ρ q) =
      eHighCoprimaryReindex K d (eHighCoprimaryDiagHom ρ q) *
        eHighCoprimaryReindex K d (eHighCoprimaryTransHom ι (Multiplicative.ofAdd m))
    rw [← map_mul, ← map_mul, h]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimary_exists_gl_of_additive

end Trans

end GroupApproximation.BooneHigman.Metabelian.Coprimary
