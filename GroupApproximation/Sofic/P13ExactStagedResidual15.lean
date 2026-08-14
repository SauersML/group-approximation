import GroupApproximation.Sofic.P13ExactStagedResidual15Part0
import GroupApproximation.Sofic.P13ExactStagedResidual15Part1
import GroupApproximation.Sofic.P13ExactStagedResidual15Part2
import GroupApproximation.Sofic.P13ExactStagedResidual15Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_5 :
    ∑ c : Fin 293, (residualNumerator 1 5 c).natAbs = 6652740039 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_1_5_0, residual_part_sum_1_5_1, residual_part_sum_1_5_2, residual_part_sum_1_5_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
