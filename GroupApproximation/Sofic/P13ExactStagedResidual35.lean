import GroupApproximation.Sofic.P13ExactStagedResidual35Part0
import GroupApproximation.Sofic.P13ExactStagedResidual35Part1
import GroupApproximation.Sofic.P13ExactStagedResidual35Part2
import GroupApproximation.Sofic.P13ExactStagedResidual35Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_5 :
    ∑ c : Fin 293, (residualNumerator 3 5 c).natAbs = 6828814009 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_3_5_0, residual_part_sum_3_5_1, residual_part_sum_3_5_2, residual_part_sum_3_5_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
