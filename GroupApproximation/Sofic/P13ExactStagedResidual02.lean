import GroupApproximation.Sofic.P13ExactStagedResidual02Part0
import GroupApproximation.Sofic.P13ExactStagedResidual02Part1
import GroupApproximation.Sofic.P13ExactStagedResidual02Part2
import GroupApproximation.Sofic.P13ExactStagedResidual02Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_2 :
    ∑ c : Fin 293, (residualNumerator 0 2 c).natAbs = 9079445487 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_0_2_0, residual_part_sum_0_2_1, residual_part_sum_0_2_2, residual_part_sum_0_2_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
