import GroupApproximation.Sofic.P13ExactStagedResidual21Part0
import GroupApproximation.Sofic.P13ExactStagedResidual21Part1
import GroupApproximation.Sofic.P13ExactStagedResidual21Part2
import GroupApproximation.Sofic.P13ExactStagedResidual21Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_1 :
    ∑ c : Fin 293, (residualNumerator 2 1 c).natAbs = 7915229999 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_2_1_0, residual_part_sum_2_1_1, residual_part_sum_2_1_2, residual_part_sum_2_1_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
