import GroupApproximation.Sofic.LiteralP13HodgeResidual30Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual30Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual30Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual30Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_0 :
    ∑ c : Fin 293, (residualNumerator 3 0 c).natAbs = 9283845417 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_3_0_0, residual_part_sum_3_0_1, residual_part_sum_3_0_2, residual_part_sum_3_0_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
