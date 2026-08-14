import GroupApproximation.Sofic.P13ExactStagedResidual24Part0
import GroupApproximation.Sofic.P13ExactStagedResidual24Part1
import GroupApproximation.Sofic.P13ExactStagedResidual24Part2
import GroupApproximation.Sofic.P13ExactStagedResidual24Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_4 :
    ∑ c : Fin 293, (residualNumerator 2 4 c).natAbs = 7779090332 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_2_4_0, residual_part_sum_2_4_1, residual_part_sum_2_4_2, residual_part_sum_2_4_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
