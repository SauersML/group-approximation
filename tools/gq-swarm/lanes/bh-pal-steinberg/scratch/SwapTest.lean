import GroupApproximation.SteinbergFP.Doubling
import GroupApproximation.SteinbergFP.Diagonal
import Mathlib.LinearAlgebra.Matrix.Notation

namespace GroupApproximation.SteinbergFP
open SteinbergGroup
variable {S : Type*} [Ring S] (L : LeavittFamily S)

example : !![1 - L.t0 * L.s0, -(L.t0 * L.s1), -L.t0;
         -(L.t1 * L.s0), 1 - L.t1 * L.s1, -L.t1;
         L.s0, L.s1, 1] * !![L.t0, 0, 0; L.t1, 0, 0; 0, L.s0, L.s1] =
      !![0, -1, 0; 0, 0, -1; 1, L.s0, L.s1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1, L.sum_range]
  all_goals trace_state
  all_goals sorry

example : !![(0 : S), -1, 0; 0, 0, -1; 1, L.s0, L.s1] * !![1, -L.s0, -L.s1; 0, 1, 0; 0, 0, 1] =
      !![0, -1, 0; 0, 0, -1; 1, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals trace_state
  all_goals sorry

example : stMatrix (Fin 3) S (x 0 2 (by decide) (1 : S) * x 2 0 (by decide) (-1) * x 0 2 (by decide) 1 *
    (x 1 0 (by decide) (1 : S) * x 0 1 (by decide) (-1) * x 1 0 (by decide) 1)) =
      !![0, -1, 0; 0, 0, -1; 1, 0, 0] := by
  simp only [map_mul, stMatrix_x]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]
  all_goals trace_state
  all_goals sorry

end GroupApproximation.SteinbergFP
