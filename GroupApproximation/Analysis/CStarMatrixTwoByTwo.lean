import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Elementary two-by-two C-star matrix maps

This file records the small entrywise constructions used by the HNN corner
argument.  They are stated for genuine `CStarMatrix` algebras, not raw ring
matrices with an assumed C-star norm.
-/

namespace GroupApproximation

open scoped CStarAlgebra

noncomputable section

universe u v

/-- Entrywise application of a unital star-algebra homomorphism to a square
C-star matrix. -/
def cStarMatrixMap {A : Type u} {B : Type v}
    [CStarAlgebra A] [CStarAlgebra B]
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : A →⋆ₐ[ℂ] B) :
    CStarMatrix I I A →⋆ₐ[ℂ] CStarMatrix I I B where
  toFun := CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom
  map_one' := by
    change (1 : Matrix I I A).map f = (1 : Matrix I I B)
    exact Matrix.map_one f (map_zero f) (map_one f)
  map_mul' x y := map_mul (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom) x y
  map_zero' := map_zero (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom)
  map_add' x y := map_add (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom) x y
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom
        (z • (1 : CStarMatrix I I A)) =
      z • (1 : CStarMatrix I I B)
    rw [map_smul]
    congr 1
    change (1 : Matrix I I A).map f = (1 : Matrix I I B)
    exact Matrix.map_one f (map_zero f) (map_one f)
  map_star' x := map_star (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom) x

@[simp] theorem cStarMatrixMap_apply
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : A →⋆ₐ[ℂ] B) (M : CStarMatrix I I A) (i j : I) :
    cStarMatrixMap f M i j = f (M i j) :=
  by
    change (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom M) i j = _
    rfl

theorem cStarMatrixMap_injective
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f) :
    Function.Injective (cStarMatrixMap (I := I) f) := by
  intro M N hMN
  ext i j
  apply hf
  have hij := congrArg (fun P : CStarMatrix I I B ↦ P i j) hMN
  simpa only [cStarMatrixMap_apply] using hij

/-- The diagonal matrix with prescribed `(0,0)` and `(1,1)` entries. -/
def cStarDiagonal2 {A : Type u} [CStarAlgebra A] (a b : A) :
    CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal ![a, b])

@[simp] theorem cStarDiagonal2_apply_zero_zero
    {A : Type u} [CStarAlgebra A] (a b : A) :
    cStarDiagonal2 a b 0 0 = a := by
  simp [cStarDiagonal2]

@[simp] theorem cStarDiagonal2_apply_zero_one
    {A : Type u} [CStarAlgebra A] (a b : A) :
    cStarDiagonal2 a b 0 1 = 0 := by
  simp [cStarDiagonal2]

@[simp] theorem cStarDiagonal2_apply_one_zero
    {A : Type u} [CStarAlgebra A] (a b : A) :
    cStarDiagonal2 a b 1 0 = 0 := by
  simp [cStarDiagonal2]

@[simp] theorem cStarDiagonal2_apply_one_one
    {A : Type u} [CStarAlgebra A] (a b : A) :
    cStarDiagonal2 a b 1 1 = b := by
  simp [cStarDiagonal2]

/-- A two-by-two matrix unit with coefficient `1`. -/
def cStarMatrixUnit2 {A : Type u} [CStarAlgebra A] (i j : Fin 2) :
    CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (Matrix.single i j 1)

@[simp] theorem cStarMatrixUnit2_star
    {A : Type u} [CStarAlgebra A] (i j : Fin 2) :
    star (cStarMatrixUnit2 (A := A) i j) = cStarMatrixUnit2 j i := by
  ext p q
  fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;>
    simp [cStarMatrixUnit2, CStarMatrix.star_apply, Matrix.single_apply]

@[simp] theorem cStarMatrixUnit2_mul
    {A : Type u} [CStarAlgebra A] (i j k l : Fin 2) :
    cStarMatrixUnit2 (A := A) i j * cStarMatrixUnit2 k l =
      if j = k then cStarMatrixUnit2 i l else 0 := by
  ext p q
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    fin_cases p <;> fin_cases q <;>
      simp [cStarMatrixUnit2, CStarMatrix.mul_apply, Matrix.single_apply]

@[simp] theorem cStarMatrixMap_diagonal2
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (a b : A) :
    cStarMatrixMap f (cStarDiagonal2 a b) =
      cStarDiagonal2 (f a) (f b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp] theorem cStarMatrixMap_unit2
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (i j : Fin 2) :
    cStarMatrixMap f (cStarMatrixUnit2 i j) = cStarMatrixUnit2 i j := by
  ext p q
  fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;>
    simp [cStarMatrixUnit2, Matrix.single_apply]

end

end GroupApproximation
