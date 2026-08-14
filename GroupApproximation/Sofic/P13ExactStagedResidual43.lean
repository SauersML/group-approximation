import GroupApproximation.Sofic.P13ExactStagedResidual43Part0
import GroupApproximation.Sofic.P13ExactStagedResidual43Part1
import GroupApproximation.Sofic.P13ExactStagedResidual43Part2
import GroupApproximation.Sofic.P13ExactStagedResidual43Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_3 :
    ∑ c : Fin 293, (residualNumerator 4 3 c).natAbs = 6257693699 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_4_3_0, residual_part_sum_4_3_1, residual_part_sum_4_3_2, residual_part_sum_4_3_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
