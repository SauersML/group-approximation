import GroupApproximation.Sofic.P13ExactStagedResidual55Part0
import GroupApproximation.Sofic.P13ExactStagedResidual55Part1
import GroupApproximation.Sofic.P13ExactStagedResidual55Part2
import GroupApproximation.Sofic.P13ExactStagedResidual55Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_5 :
    ∑ c : Fin 293, (residualNumerator 5 5 c).natAbs = 11622680190256 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_5_5_0, residual_part_sum_5_5_1, residual_part_sum_5_5_2, residual_part_sum_5_5_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
