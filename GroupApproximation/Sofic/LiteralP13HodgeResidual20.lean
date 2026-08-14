import GroupApproximation.Sofic.LiteralP13HodgeResidual20Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual20Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual20Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual20Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_0 :
    ∑ c : Fin 293, (residualNumerator 2 0 c).natAbs = 9079445487 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_2_0_0, residual_part_sum_2_0_1, residual_part_sum_2_0_2, residual_part_sum_2_0_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
