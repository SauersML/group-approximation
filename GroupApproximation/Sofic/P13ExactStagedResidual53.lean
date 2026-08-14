import GroupApproximation.Sofic.P13ExactStagedResidual53Part0
import GroupApproximation.Sofic.P13ExactStagedResidual53Part1
import GroupApproximation.Sofic.P13ExactStagedResidual53Part2
import GroupApproximation.Sofic.P13ExactStagedResidual53Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_3 :
    ∑ c : Fin 293, (residualNumerator 5 3 c).natAbs = 6828814009 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_5_3_0, residual_part_sum_5_3_1, residual_part_sum_5_3_2, residual_part_sum_5_3_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
