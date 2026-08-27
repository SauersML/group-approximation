import Mathlib.Algebra.Star.Unitary
import GroupApproximation.Analysis.CStarMatrixTwoByTwo

/-!
# The flip unitary of a two-by-two C-star matrix algebra

The permutation matrix `f = e₀₁ + e₁₀` of `M₂(A)` is a self-adjoint unitary
which exchanges the two diagonal entries:

    f* = f ,   f² = 1 ,   f diag(x,y) f = diag(y,x) ,

so `f` commutes with every scalar diagonal `diag(x,x)`.

This is the commutation Shulman's Theorem 10 rests on: there the two
representations of the amalgamated algebra are `ρ₂(c) = diag(c,c)` and
`ρ₁ = f* ρ₂ f`, and the displayed identities are what makes those two agree.
Only the four algebraic facts are proved here; nothing about that theorem is
asserted.

Every proof is entrywise, in the idiom of `CStarMatrixTwoByTwo`: the index
case split, then one `simp` over the two matrix constructors.  The name `flip`
shadows the core combinator inside this namespace, which is deliberate --
nothing here needs the combinator.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped CStarAlgebra

noncomputable section

universe u

/-- The flip `e₀₁ + e₁₀` of `M₂(A)`. -/
def flip (A : Type u) [CStarAlgebra A] : CStarMatrix (Fin 2) (Fin 2) A :=
  cStarMatrixUnit2 0 1 + cStarMatrixUnit2 1 0

@[simp] theorem flip_apply_zero_zero (A : Type u) [CStarAlgebra A] :
    flip A 0 0 = 0 := by
  simp [flip, cStarMatrixUnit2, Matrix.single_apply]

@[simp] theorem flip_apply_zero_one (A : Type u) [CStarAlgebra A] :
    flip A 0 1 = 1 := by
  simp [flip, cStarMatrixUnit2, Matrix.single_apply]

@[simp] theorem flip_apply_one_zero (A : Type u) [CStarAlgebra A] :
    flip A 1 0 = 1 := by
  simp [flip, cStarMatrixUnit2, Matrix.single_apply]

@[simp] theorem flip_apply_one_one (A : Type u) [CStarAlgebra A] :
    flip A 1 1 = 0 := by
  simp [flip, cStarMatrixUnit2, Matrix.single_apply]

/-- The flip is self-adjoint. -/
theorem star_flip (A : Type u) [CStarAlgebra A] : star (flip A) = flip A := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [flip, cStarMatrixUnit2, CStarMatrix.star_apply, Matrix.single_apply]

/-- The flip is an involution. -/
theorem flip_mul_flip (A : Type u) [CStarAlgebra A] : flip A * flip A = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [flip, cStarMatrixUnit2, CStarMatrix.mul_apply, CStarMatrix.one_apply,
      Matrix.single_apply]

theorem flip_mem_unitary (A : Type u) [CStarAlgebra A] :
    flip A ∈ unitary (CStarMatrix (Fin 2) (Fin 2) A) := by
  constructor
  · rw [star_flip]
    exact flip_mul_flip A
  · rw [star_flip]
    exact flip_mul_flip A

/-- The flip, as a unitary of `M₂(A)`. -/
def flipUnitary (A : Type u) [CStarAlgebra A] :
    unitary (CStarMatrix (Fin 2) (Fin 2) A) :=
  ⟨flip A, flip_mem_unitary A⟩

@[simp] theorem coe_flipUnitary (A : Type u) [CStarAlgebra A] :
    ((flipUnitary A : unitary (CStarMatrix (Fin 2) (Fin 2) A)) :
      CStarMatrix (Fin 2) (Fin 2) A) = flip A :=
  rfl

/-- Conjugating a diagonal by the flip exchanges its two entries. -/
theorem flip_mul_diagonal2_mul_flip {A : Type u} [CStarAlgebra A] (x y : A) :
    flip A * cStarDiagonal2 x y * flip A = cStarDiagonal2 y x := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [flip, cStarMatrixUnit2, cStarDiagonal2, CStarMatrix.mul_apply,
      Matrix.single_apply]

/-- The flip commutes with every scalar diagonal. -/
theorem flip_commute_diagonal2 {A : Type u} [CStarAlgebra A] (x : A) :
    Commute (flip A) (cStarDiagonal2 x x) := by
  have h : flip A * cStarDiagonal2 x x = cStarDiagonal2 x x * flip A := by
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [flip, cStarMatrixUnit2, cStarDiagonal2, CStarMatrix.mul_apply,
        Matrix.single_apply]
  exact h

end

end ShulmanFill
end GroupApproximation
