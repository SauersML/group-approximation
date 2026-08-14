import GroupApproximation.Sofic.LiteralP13HodgeResidual31Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual31Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual31Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual31Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_1 :
    ∑ c : Fin 293, (residualNumerator 3 1 c).natAbs = 6215318798 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_3_1_0, residual_part_sum_3_1_1, residual_part_sum_3_1_2, residual_part_sum_3_1_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
