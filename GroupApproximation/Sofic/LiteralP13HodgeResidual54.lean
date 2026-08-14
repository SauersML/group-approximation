import GroupApproximation.Sofic.LiteralP13HodgeResidual54Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual54Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual54Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual54Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_4 :
    ∑ c : Fin 293, (residualNumerator 5 4 c).natAbs = 6642855556 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_5_4_0, residual_part_sum_5_4_1, residual_part_sum_5_4_2, residual_part_sum_5_4_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
