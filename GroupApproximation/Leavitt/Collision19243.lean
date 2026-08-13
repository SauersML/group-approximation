import GroupApproximation.Leavitt.Leavitt

/-!
# The parent-block identity behind atlas collision word 19243

The first interior atlas collision is an exact two-by-two identity.  It does
not see that the involution in the first block comes from a proper child of
the parent cylinder: every involution in every characteristic-two ring
satisfies the same word.
-/

namespace GroupApproximation

variable {R : Type*} [Ring R] [CharP R 2]

/-- Collision word `19243` closes for an arbitrary involution `K` in the
parent block.  Thus this word alone cannot recover the proper prefix
refinement or a Leavitt cross coefficient. -/
theorem collision19243_parentBlock_identity (K : R) (hK : K * K = 1) :
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) *
        !![K, 0; 0, 1] *
        !![1, 0; 1, 1] *
        !![K, 0; 0, 1] *
        !![0, 1; 1, 1] *
        !![K, 0; 0, 1] *
        !![1, 1; 0, 1] *
        !![K, 0; 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, hK,
      CharTwo.add_self_eq_zero, add_comm, add_left_comm]

end GroupApproximation
