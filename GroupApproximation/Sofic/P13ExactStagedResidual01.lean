import GroupApproximation.Sofic.P13ExactStagedResidual01Part0
import GroupApproximation.Sofic.P13ExactStagedResidual01Part1
import GroupApproximation.Sofic.P13ExactStagedResidual01Part2
import GroupApproximation.Sofic.P13ExactStagedResidual01Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_1 :
    ∑ c : Fin 293, (residualNumerator 0 1 c).natAbs = 9037219251 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_0_1_0, residual_part_sum_0_1_1, residual_part_sum_0_1_2, residual_part_sum_0_1_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
