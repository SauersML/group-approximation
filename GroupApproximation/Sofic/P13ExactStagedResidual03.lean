import GroupApproximation.Sofic.P13ExactStagedResidual03Part0
import GroupApproximation.Sofic.P13ExactStagedResidual03Part1
import GroupApproximation.Sofic.P13ExactStagedResidual03Part2
import GroupApproximation.Sofic.P13ExactStagedResidual03Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_3 :
    ∑ c : Fin 293, (residualNumerator 0 3 c).natAbs = 9283845417 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_0_3_0, residual_part_sum_0_3_1, residual_part_sum_0_3_2, residual_part_sum_0_3_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
