import GroupApproximation.Sofic.P13ExactStagedResidual52Part0
import GroupApproximation.Sofic.P13ExactStagedResidual52Part1
import GroupApproximation.Sofic.P13ExactStagedResidual52Part2
import GroupApproximation.Sofic.P13ExactStagedResidual52Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_2 :
    ∑ c : Fin 293, (residualNumerator 5 2 c).natAbs = 7921451991 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_5_2_0, residual_part_sum_5_2_1, residual_part_sum_5_2_2, residual_part_sum_5_2_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
