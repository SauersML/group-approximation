import GroupApproximation.Sofic.P13ExactStagedResidual11Part0
import GroupApproximation.Sofic.P13ExactStagedResidual11Part1
import GroupApproximation.Sofic.P13ExactStagedResidual11Part2
import GroupApproximation.Sofic.P13ExactStagedResidual11Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_1 :
    ∑ c : Fin 293, (residualNumerator 1 1 c).natAbs = 11622602362466 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_1_1_0, residual_part_sum_1_1_1, residual_part_sum_1_1_2, residual_part_sum_1_1_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
