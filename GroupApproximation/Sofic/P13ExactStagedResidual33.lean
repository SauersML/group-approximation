import GroupApproximation.Sofic.P13ExactStagedResidual33Part0
import GroupApproximation.Sofic.P13ExactStagedResidual33Part1
import GroupApproximation.Sofic.P13ExactStagedResidual33Part2
import GroupApproximation.Sofic.P13ExactStagedResidual33Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_3 :
    ∑ c : Fin 293, (residualNumerator 3 3 c).natAbs = 11621832714147 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_3_3_0, residual_part_sum_3_3_1, residual_part_sum_3_3_2, residual_part_sum_3_3_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
