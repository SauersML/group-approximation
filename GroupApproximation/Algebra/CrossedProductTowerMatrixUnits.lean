import GroupApproximation.Algebra.LocallyMatricial
import GroupApproximation.Pestov91.CrossedProduct

/-!
# Tower matrix units in `A ⋊ ℤ`

`non_mf_groups_exist.tex`, lem:transient-matrices, the last step of the proof: on each cell the
characteristic arrows between the levels of a tower form a copy of `M_h(k)`.

The levels are elements `p a i` of the coefficient ring (block `a`, level `i`), with exponents
`n a i`, such that
* level `i` is the translate of level `j` by `n a i - n a j` (`hcov`);
* levels are idempotent (`hidem`), distinct levels of one block are orthogonal (`hne`), and levels
  of distinct blocks are orthogonal (`hblock`).

The arrow from level `j` to level `i` is
`towerUnit p n a i j = single (ofAdd (n a i - n a j)) (p a i)`, which is
`C (p a i) * u ^ (n a i - n a j)` (`towerUnit_eq_C_mul_unit_zpow`).

* `towerUnit_mul_towerUnit`: the product of two arrows in normal form.
* `isMatrixUnitFamily_towerUnit`: the arrows form a matrix unit family.
* `towerUnit_self`, `towerUnit_self_ne_zero`: the diagonal arrows are the levels.
-/

namespace GroupApproximation
namespace Pestov91
namespace CrossedProduct

open SkewMonoidAlgebra (single)
open Multiplicative (ofAdd)

variable {A : Type*} [Ring A] {m : ℕ} {h : Fin m → ℕ}

/-- The arrow from level `j` to level `i` of block `a`, `C (p a i) * u ^ (n a i - n a j)`. -/
noncomputable def towerUnit (p : ∀ a : Fin m, Fin (h a) → A) (n : ∀ a : Fin m, Fin (h a) → ℤ)
    (a : Fin m) (i j : Fin (h a)) : SkewMonoidAlgebra A (Multiplicative ℤ) :=
  single (ofAdd (n a i - n a j)) (p a i)

variable {p : ∀ a : Fin m, Fin (h a) → A} {n : ∀ a : Fin m, Fin (h a) → ℤ}

theorem towerUnit_self_ne_zero {a : Fin m} {i : Fin (h a)} (hp : p a i ≠ 0) :
    towerUnit p n a i i ≠ 0 :=
  fun h0 => hp (SkewMonoidAlgebra.single_eq_zero.1 h0)

variable [MulSemiringAction (Multiplicative ℤ) A]

theorem towerUnit_eq_C_mul_unit_zpow (a : Fin m) (i j : Fin (h a)) :
    towerUnit p n a i j =
      C (p a i) * ((unit ^ (n a i - n a j) : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
        SkewMonoidAlgebra A (Multiplicative ℤ)) := by
  rw [val_unit_zpow, C_mul_single, mul_one, towerUnit]

theorem towerUnit_self (a : Fin m) (i : Fin (h a)) : towerUnit p n a i i = C (p a i) := by
  rw [towerUnit, sub_self, ofAdd_zero, C_apply]

/-- The product of two arrows, in normal form. -/
theorem towerUnit_mul_towerUnit (a b : Fin m) (i j : Fin (h a)) (i' j' : Fin (h b)) :
    towerUnit p n a i j * towerUnit p n b i' j' =
      single (ofAdd (n a i - n a j + (n b i' - n b j')))
        (p a i * ofAdd (n a i - n a j) • p b i') := by
  rw [towerUnit, towerUnit, SkewMonoidAlgebra.single_mul_single, ← ofAdd_add]

theorem towerUnit_mul_towerUnit_same
    (hcov : ∀ a (i j : Fin (h a)), ofAdd (n a i - n a j) • p a j = p a i)
    (hidem : ∀ a (i : Fin (h a)), p a i * p a i = p a i) (a : Fin m) (i j l : Fin (h a)) :
    towerUnit p n a i j * towerUnit p n a j l = towerUnit p n a i l := by
  rw [towerUnit_mul_towerUnit, hcov, hidem, sub_add_sub_cancel, towerUnit]

theorem towerUnit_mul_towerUnit_of_ne
    (hcov : ∀ a (i j : Fin (h a)), ofAdd (n a i - n a j) • p a j = p a i)
    (hne : ∀ a (i j : Fin (h a)), i ≠ j → p a i * p a j = 0) (a : Fin m) (i j j' l : Fin (h a))
    (hj : j ≠ j') :
    towerUnit p n a i j * towerUnit p n a j' l = 0 := by
  rw [towerUnit_mul_towerUnit, ← hcov a i j, ← smul_mul', hne a j j' hj, smul_zero,
    SkewMonoidAlgebra.single_zero]

theorem towerUnit_mul_towerUnit_of_block_ne
    (hcov : ∀ a (i j : Fin (h a)), ofAdd (n a i - n a j) • p a j = p a i)
    (hblock : ∀ a b, a ≠ b → ∀ (i : Fin (h a)) (j : Fin (h b)), p a i * p b j = 0)
    {a b : Fin m} (hab : a ≠ b) (i j : Fin (h a)) (i' j' : Fin (h b)) :
    towerUnit p n a i j * towerUnit p n b i' j' = 0 := by
  rw [towerUnit_mul_towerUnit, ← hcov a i j, ← smul_mul', hblock a b hab j i', smul_zero,
    SkewMonoidAlgebra.single_zero]

/-- The arrows between the levels of towers of translated orthogonal idempotents form a matrix
unit family. -/
theorem isMatrixUnitFamily_towerUnit
    (hcov : ∀ a (i j : Fin (h a)), ofAdd (n a i - n a j) • p a j = p a i)
    (hidem : ∀ a (i : Fin (h a)), p a i * p a i = p a i)
    (hne : ∀ a (i j : Fin (h a)), i ≠ j → p a i * p a j = 0)
    (hblock : ∀ a b, a ≠ b → ∀ (i : Fin (h a)) (j : Fin (h b)), p a i * p b j = 0) :
    ChainCore.IsMatrixUnitFamily (towerUnit p n) :=
  ⟨towerUnit_mul_towerUnit_same hcov hidem, towerUnit_mul_towerUnit_of_ne hcov hne,
    fun _ _ hab => towerUnit_mul_towerUnit_of_block_ne hcov hblock hab⟩

end CrossedProduct
end Pestov91
end GroupApproximation
