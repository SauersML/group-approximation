import GroupApproximation.Sofic.P13ExactStagedResidual32Part0
import GroupApproximation.Sofic.P13ExactStagedResidual32Part1
import GroupApproximation.Sofic.P13ExactStagedResidual32Part2
import GroupApproximation.Sofic.P13ExactStagedResidual32Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_2 :
    ∑ c : Fin 293, (residualNumerator 3 2 c).natAbs = 8331331951 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_3_2_0, residual_part_sum_3_2_1, residual_part_sum_3_2_2, residual_part_sum_3_2_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
