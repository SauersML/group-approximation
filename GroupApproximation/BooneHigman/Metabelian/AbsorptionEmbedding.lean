import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Absorption, part 1: the homomorphism `g ↦ diag(g, g⁻ᵀ, 1)`

Lane `bh-met-16`.  Over a commutative ring `R` and for `2M ≤ N` we build the homomorphism

  `absorptionUnits M N h : GL_M(R) →* GL_N(R)`,  `g ↦ diag(g, (g⁻¹)ᵀ, 1_{N-2M})`

(the blocks are placed along `Fin N ≃ (Fin M ⊕ Fin M) ⊕ Fin (N - 2M)`), and prove that it is
injective (`absorptionUnits_injective`) and lands in `SL_N(R)` (`absorptionUnits_det`).
Multiplicativity of the middle block is `((gh)⁻¹)ᵀ = (g⁻¹)ᵀ (h⁻¹)ᵀ`, which is where
commutativity of `R` enters (through `Matrix.transpose_mul`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

section Blocks

variable {R : Type*} [CommRing R]
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- Block-diagonal matrices multiply blockwise. -/
theorem fromBlocks_diag_mul (A A' : Matrix m m R) (D D' : Matrix n n R) :
    Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks A' 0 0 D' =
      Matrix.fromBlocks (A * A') 0 0 (D * D') := by
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.fromBlocks_diag_mul

/-- The block-diagonal unit `diag(u, v)`. -/
noncomputable def blockUnits (u : (Matrix m m R)ˣ) (v : (Matrix n n R)ˣ) :
    (Matrix (m ⊕ n) (m ⊕ n) R)ˣ where
  val := Matrix.fromBlocks (u : Matrix m m R) 0 0 (v : Matrix n n R)
  inv := Matrix.fromBlocks ((u⁻¹ : (Matrix m m R)ˣ) : Matrix m m R) 0 0
    ((v⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)
  val_inv := by
    rw [fromBlocks_diag_mul, Units.mul_inv, Units.mul_inv, Matrix.fromBlocks_one]
  inv_val := by
    rw [fromBlocks_diag_mul, Units.inv_mul, Units.inv_mul, Matrix.fromBlocks_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.blockUnits

theorem blockUnits_mul (u u' : (Matrix m m R)ˣ) (v v' : (Matrix n n R)ˣ) :
    blockUnits (u * u') (v * v') = blockUnits u v * blockUnits u' v' := by
  apply Units.ext
  change Matrix.fromBlocks ((u * u' : (Matrix m m R)ˣ) : Matrix m m R) 0 0
      ((v * v' : (Matrix n n R)ˣ) : Matrix n n R) =
    Matrix.fromBlocks (u : Matrix m m R) 0 0 (v : Matrix n n R) *
      Matrix.fromBlocks (u' : Matrix m m R) 0 0 (v' : Matrix n n R)
  rw [fromBlocks_diag_mul, Units.val_mul, Units.val_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.blockUnits_mul

theorem blockUnits_mul_one (u u' : (Matrix m m R)ˣ) :
    blockUnits (u * u') (1 : (Matrix n n R)ˣ) =
      blockUnits u (1 : (Matrix n n R)ˣ) * blockUnits u' (1 : (Matrix n n R)ˣ) := by
  rw [← blockUnits_mul, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.blockUnits_mul_one

theorem blockUnits_one :
    blockUnits (1 : (Matrix m m R)ˣ) (1 : (Matrix n n R)ˣ) = 1 := by
  apply Units.ext
  change Matrix.fromBlocks ((1 : (Matrix m m R)ˣ) : Matrix m m R) 0 0
      ((1 : (Matrix n n R)ˣ) : Matrix n n R) = (1 : Matrix (m ⊕ n) (m ⊕ n) R)
  simp only [Units.val_one, Matrix.fromBlocks_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.blockUnits_one

/-- The upper-left block of `diag(u, v)` determines `u`. -/
theorem blockUnits_left_eq {u u' : (Matrix m m R)ˣ} {v v' : (Matrix n n R)ˣ}
    (h : blockUnits u v = blockUnits u' v') : u = u' := by
  have hv :=
    congrArg (fun z : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ ↦ (z : Matrix (m ⊕ n) (m ⊕ n) R)) h
  change Matrix.fromBlocks (u : Matrix m m R) 0 0 (v : Matrix n n R) =
    Matrix.fromBlocks (u' : Matrix m m R) 0 0 (v' : Matrix n n R) at hv
  exact Units.ext (Matrix.fromBlocks_inj.mp hv).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.blockUnits_left_eq

theorem blockUnits_det (u : (Matrix m m R)ˣ) (v : (Matrix n n R)ˣ) :
    Matrix.det
        ((blockUnits u v : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ) : Matrix (m ⊕ n) (m ⊕ n) R) =
      Matrix.det (u : Matrix m m R) * Matrix.det (v : Matrix n n R) := by
  change Matrix.det (Matrix.fromBlocks (u : Matrix m m R) 0 0 (v : Matrix n n R)) = _
  exact Matrix.det_fromBlocks_zero₂₁ _ _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.blockUnits_det

/-- The inverse-transpose homomorphism `g ↦ (g⁻¹)ᵀ` on `GL_m(R)`. -/
noncomputable def invTransposeHom : (Matrix m m R)ˣ →* (Matrix m m R)ˣ where
  toFun g :=
    { val := Matrix.transpose ((g⁻¹ : (Matrix m m R)ˣ) : Matrix m m R)
      inv := Matrix.transpose (g : Matrix m m R)
      val_inv := by
        rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      inv_val := by
        rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one] }
  map_one' := by
    apply Units.ext
    change Matrix.transpose (((1 : (Matrix m m R)ˣ)⁻¹ : (Matrix m m R)ˣ) : Matrix m m R) =
      ((1 : (Matrix m m R)ˣ) : Matrix m m R)
    rw [inv_one, Units.val_one, Matrix.transpose_one]
  map_mul' g h := by
    apply Units.ext
    change Matrix.transpose (((g * h)⁻¹ : (Matrix m m R)ˣ) : Matrix m m R) =
      Matrix.transpose ((g⁻¹ : (Matrix m m R)ˣ) : Matrix m m R) *
        Matrix.transpose ((h⁻¹ : (Matrix m m R)ˣ) : Matrix m m R)
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.invTransposeHom

theorem invTransposeHom_val (g : (Matrix m m R)ˣ) :
    ((invTransposeHom g : (Matrix m m R)ˣ) : Matrix m m R) =
      Matrix.transpose ((g⁻¹ : (Matrix m m R)ˣ) : Matrix m m R) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.invTransposeHom_val

end Blocks

section FinBlocks

variable {R : Type*} [CommRing R]

/-- `(Fin M ⊕ Fin M) ⊕ Fin (N - 2M) ≃ Fin N` for `2M ≤ N`. -/
def absorptionIndexEquiv (M N : ℕ) (h : 2 * M ≤ N) :
    (Fin M ⊕ Fin M) ⊕ Fin (N - 2 * M) ≃ Fin N :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin (N - 2 * M)))).trans
    (finSumFinEquiv.trans (finCongr (show M + M + (N - 2 * M) = N by omega)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.absorptionIndexEquiv

/-- **The absorbing homomorphism** `g ↦ diag(g, (g⁻¹)ᵀ, 1_{N-2M})`. -/
noncomputable def absorptionUnits (M N : ℕ) (h : 2 * M ≤ N) :
    (Matrix (Fin M) (Fin M) R)ˣ →* (Matrix (Fin N) (Fin N) R)ˣ where
  toFun g := elementaryReindexUnitEquiv (R := R) (absorptionIndexEquiv M N h)
    (blockUnits (blockUnits g (invTransposeHom g))
      (1 : (Matrix (Fin (N - 2 * M)) (Fin (N - 2 * M)) R)ˣ))
  map_one' := by
    show elementaryReindexUnitEquiv (R := R) (absorptionIndexEquiv M N h)
        (blockUnits (blockUnits (1 : (Matrix (Fin M) (Fin M) R)ˣ)
            (invTransposeHom (1 : (Matrix (Fin M) (Fin M) R)ˣ)))
          (1 : (Matrix (Fin (N - 2 * M)) (Fin (N - 2 * M)) R)ˣ)) = 1
    rw [map_one, blockUnits_one, blockUnits_one, map_one]
  map_mul' g g' := by
    show elementaryReindexUnitEquiv (R := R) (absorptionIndexEquiv M N h)
        (blockUnits (blockUnits (g * g') (invTransposeHom (g * g')))
          (1 : (Matrix (Fin (N - 2 * M)) (Fin (N - 2 * M)) R)ˣ)) =
      elementaryReindexUnitEquiv (R := R) (absorptionIndexEquiv M N h)
          (blockUnits (blockUnits g (invTransposeHom g))
            (1 : (Matrix (Fin (N - 2 * M)) (Fin (N - 2 * M)) R)ˣ)) *
        elementaryReindexUnitEquiv (R := R) (absorptionIndexEquiv M N h)
          (blockUnits (blockUnits g' (invTransposeHom g'))
            (1 : (Matrix (Fin (N - 2 * M)) (Fin (N - 2 * M)) R)ˣ))
    rw [map_mul (invTransposeHom (R := R) (m := Fin M)) g g', blockUnits_mul, blockUnits_mul_one, map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.absorptionUnits

theorem absorptionUnits_injective (M N : ℕ) (h : 2 * M ≤ N) :
    Function.Injective (absorptionUnits (R := R) M N h) := by
  intro g g' hg
  have h1 : blockUnits (blockUnits g (invTransposeHom g))
        (1 : (Matrix (Fin (N - 2 * M)) (Fin (N - 2 * M)) R)ˣ) =
      blockUnits (blockUnits g' (invTransposeHom g'))
        (1 : (Matrix (Fin (N - 2 * M)) (Fin (N - 2 * M)) R)ˣ) :=
    (elementaryReindexUnitEquiv (R := R) (absorptionIndexEquiv M N h)).injective hg
  exact blockUnits_left_eq (blockUnits_left_eq h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.absorptionUnits_injective

/-- `diag(g, (g⁻¹)ᵀ, 1)` has determinant `det g · det g⁻¹ = 1`. -/
theorem absorptionUnits_det (M N : ℕ) (h : 2 * M ≤ N) (g : (Matrix (Fin M) (Fin M) R)ˣ) :
    Matrix.det ((absorptionUnits (R := R) M N h g : (Matrix (Fin N) (Fin N) R)ˣ) :
      Matrix (Fin N) (Fin N) R) = 1 := by
  change Matrix.det (Matrix.reindex (absorptionIndexEquiv M N h) (absorptionIndexEquiv M N h)
      ((blockUnits (blockUnits g (invTransposeHom g))
        (1 : (Matrix (Fin (N - 2 * M)) (Fin (N - 2 * M)) R)ˣ) :
          (Matrix ((Fin M ⊕ Fin M) ⊕ Fin (N - 2 * M)) ((Fin M ⊕ Fin M) ⊕ Fin (N - 2 * M)) R)ˣ) :
        Matrix ((Fin M ⊕ Fin M) ⊕ Fin (N - 2 * M)) ((Fin M ⊕ Fin M) ⊕ Fin (N - 2 * M)) R)) = 1
  rw [Matrix.det_reindex_self, blockUnits_det, blockUnits_det, invTransposeHom_val,
    Matrix.det_transpose, ← Matrix.det_mul, Units.mul_inv]
  simp only [Units.val_one, Matrix.det_one, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.absorptionUnits_det

end FinBlocks

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
