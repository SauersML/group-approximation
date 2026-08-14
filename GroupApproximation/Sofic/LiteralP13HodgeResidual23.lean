import GroupApproximation.Sofic.LiteralP13HodgeResidual23Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual23Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual23Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual23Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_3 :
    ∑ c : Fin 293, (residualNumerator 2 3 c).natAbs = 8331331951 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_2_3_0, residual_part_sum_2_3_1, residual_part_sum_2_3_2, residual_part_sum_2_3_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
