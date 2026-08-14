import GroupApproximation.Sofic.P13ExactStagedResidual04Part0
import GroupApproximation.Sofic.P13ExactStagedResidual04Part1
import GroupApproximation.Sofic.P13ExactStagedResidual04Part2
import GroupApproximation.Sofic.P13ExactStagedResidual04Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_4 :
    ∑ c : Fin 293, (residualNumerator 0 4 c).natAbs = 8836491131 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_0_4_0, residual_part_sum_0_4_1, residual_part_sum_0_4_2, residual_part_sum_0_4_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
