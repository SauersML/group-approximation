import GroupApproximation.Sofic.P13ExactStagedResidual22Part0
import GroupApproximation.Sofic.P13ExactStagedResidual22Part1
import GroupApproximation.Sofic.P13ExactStagedResidual22Part2
import GroupApproximation.Sofic.P13ExactStagedResidual22Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_2 :
    ∑ c : Fin 293, (residualNumerator 2 2 c).natAbs = 11624840006764 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_2_2_0, residual_part_sum_2_2_1, residual_part_sum_2_2_2, residual_part_sum_2_2_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
