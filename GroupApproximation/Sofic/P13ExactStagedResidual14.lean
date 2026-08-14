import GroupApproximation.Sofic.P13ExactStagedResidual14Part0
import GroupApproximation.Sofic.P13ExactStagedResidual14Part1
import GroupApproximation.Sofic.P13ExactStagedResidual14Part2
import GroupApproximation.Sofic.P13ExactStagedResidual14Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_4 :
    ∑ c : Fin 293, (residualNumerator 1 4 c).natAbs = 6701810124 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_1_4_0, residual_part_sum_1_4_1, residual_part_sum_1_4_2, residual_part_sum_1_4_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
