import GroupApproximation.Sofic.P13ExactStagedResidual51Part0
import GroupApproximation.Sofic.P13ExactStagedResidual51Part1
import GroupApproximation.Sofic.P13ExactStagedResidual51Part2
import GroupApproximation.Sofic.P13ExactStagedResidual51Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_1 :
    ∑ c : Fin 293, (residualNumerator 5 1 c).natAbs = 6652740039 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_5_1_0, residual_part_sum_5_1_1, residual_part_sum_5_1_2, residual_part_sum_5_1_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
