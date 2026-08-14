import GroupApproximation.Sofic.P13ExactStagedResidual40Part0
import GroupApproximation.Sofic.P13ExactStagedResidual40Part1
import GroupApproximation.Sofic.P13ExactStagedResidual40Part2
import GroupApproximation.Sofic.P13ExactStagedResidual40Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_0 :
    ∑ c : Fin 293, (residualNumerator 4 0 c).natAbs = 8836491131 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_4_0_0, residual_part_sum_4_0_1, residual_part_sum_4_0_2, residual_part_sum_4_0_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
