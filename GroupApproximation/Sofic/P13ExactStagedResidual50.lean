import GroupApproximation.Sofic.P13ExactStagedResidual50Part0
import GroupApproximation.Sofic.P13ExactStagedResidual50Part1
import GroupApproximation.Sofic.P13ExactStagedResidual50Part2
import GroupApproximation.Sofic.P13ExactStagedResidual50Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_0 :
    ∑ c : Fin 293, (residualNumerator 5 0 c).natAbs = 8235929367 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_5_0_0, residual_part_sum_5_0_1, residual_part_sum_5_0_2, residual_part_sum_5_0_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
