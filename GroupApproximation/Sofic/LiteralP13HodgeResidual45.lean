import GroupApproximation.Sofic.LiteralP13HodgeResidual45Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual45Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual45Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual45Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_5 :
    ∑ c : Fin 293, (residualNumerator 4 5 c).natAbs = 6642855556 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_4_5_0, residual_part_sum_4_5_1, residual_part_sum_4_5_2, residual_part_sum_4_5_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
