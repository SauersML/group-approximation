import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Elementary two-by-two C-star matrices

The Ueda corner model only needs diagonal matrices, matrix units, and their
elementary multiplication rules.  This file packages those operations for
`CStarMatrix (Fin 2) (Fin 2) A` so the later HNN proof can remain at the
level of star-algebra homomorphisms.
-/

namespace GroupApproximation

open Matrix
open scoped CStarAlgebra Matrix

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- A two-by-two diagonal C-star matrix. -/
def cStarDiagonalTwo (x y : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal ![x, y])

@[simp] theorem cStarDiagonalTwo_apply_zero_zero (x y : A) :
    cStarDiagonalTwo x y 0 0 = x := by
  simp [cStarDiagonalTwo]

@[simp] theorem cStarDiagonalTwo_apply_zero_one (x y : A) :
    cStarDiagonalTwo x y 0 1 = 0 := by
  simp [cStarDiagonalTwo]

@[simp] theorem cStarDiagonalTwo_apply_one_zero (x y : A) :
    cStarDiagonalTwo x y 1 0 = 0 := by
  simp [cStarDiagonalTwo]

@[simp] theorem cStarDiagonalTwo_apply_one_one (x y : A) :
    cStarDiagonalTwo x y 1 1 = y := by
  simp [cStarDiagonalTwo]

/-- Diagonal placement is a unital star-algebra homomorphism from a product. -/
def cStarDiagonalTwoHom :
    A × A →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) A where
  toFun p := cStarDiagonalTwo p.1 p.2
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := by
    change Matrix.diagonal ![p.1 * q.1, p.2 * q.2] =
      Matrix.diagonal ![p.1, p.2] * Matrix.diagonal ![q.1, q.2]
    symm
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> rfl
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cStarDiagonalTwo, CStarMatrix.algebraMap_apply]
  map_star' p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cStarDiagonalTwo, CStarMatrix.star_apply]

@[simp] theorem cStarDiagonalTwoHom_apply (p : A × A) :
    cStarDiagonalTwoHom p = cStarDiagonalTwo p.1 p.2 :=
  rfl

/-- The two-by-two matrix with `a` in entry `(i,j)` and zero elsewhere. -/
def cStarMatrixUnitTwo (i j : Fin 2) (a : A) :
    CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

@[simp] theorem cStarMatrixUnitTwo_apply (i j k l : Fin 2) (a : A) :
    cStarMatrixUnitTwo i j a k l = if i = k ∧ j = l then a else 0 := by
  exact Matrix.single_apply i j a k l

/-- Multiplication of two matrix units. -/
theorem cStarMatrixUnitTwo_mul (i j k l : Fin 2) (a b : A) :
    cStarMatrixUnitTwo i j a * cStarMatrixUnitTwo k l b =
      if j = k then cStarMatrixUnitTwo i l (a * b) else 0 := by
  by_cases h : j = k
  · subst k
    rw [if_pos rfl]
    change Matrix.single i j a * Matrix.single j l b =
      Matrix.single i l (a * b)
    exact Matrix.single_mul_single_same a i j l b
  · rw [if_neg h]
    change Matrix.single i j a * Matrix.single k l b = 0
    exact Matrix.single_mul_single_of_ne a i j k h b

/-- The star of a matrix unit. -/
@[simp] theorem star_cStarMatrixUnitTwo (i j : Fin 2) (a : A) :
    star (cStarMatrixUnitTwo i j a) = cStarMatrixUnitTwo j i (star a) := by
  ext p q
  rw [CStarMatrix.star_apply]
  by_cases hi : i = q <;> by_cases hj : j = p <;>
    simp [cStarMatrixUnitTwo, Matrix.single, hi, hj]

/-- The two diagonal unit matrix units add to the identity. -/
theorem cStarMatrixUnitTwo_add :
    cStarMatrixUnitTwo 0 0 (1 : A) + cStarMatrixUnitTwo 1 1 (1 : A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cStarMatrixUnitTwo]

/-- Diagonal matrices act on the left of a matrix unit entrywise. -/
theorem cStarDiagonalTwo_mul_unit (x y a : A) (i j : Fin 2) :
    cStarDiagonalTwo x y * cStarMatrixUnitTwo i j a =
      cStarMatrixUnitTwo i j (![x, y] i * a) := by
  ext p q
  change (Matrix.diagonal ![x, y] * Matrix.single i j a) p q =
    Matrix.single i j (![x, y] i * a) p q
  rw [Matrix.diagonal_mul]
  by_cases h : i = p ∧ j = q
  · rcases h with ⟨rfl, rfl⟩
    simp [Matrix.single]
  · simp [Matrix.single, h]

/-- Diagonal matrices act on the right of a matrix unit entrywise. -/
theorem cStarMatrixUnitTwo_mul_diagonal (a x y : A) (i j : Fin 2) :
    cStarMatrixUnitTwo i j a * cStarDiagonalTwo x y =
      cStarMatrixUnitTwo i j (a * ![x, y] j) := by
  ext p q
  change (Matrix.single i j a * Matrix.diagonal ![x, y]) p q =
    Matrix.single i j (a * ![x, y] j) p q
  rw [Matrix.mul_diagonal]
  by_cases h : i = p ∧ j = q
  · rcases h with ⟨rfl, rfl⟩
    simp [Matrix.single]
  · simp [Matrix.single, h]

end

end GroupApproximation
