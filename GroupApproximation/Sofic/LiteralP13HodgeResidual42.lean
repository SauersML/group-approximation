import GroupApproximation.Sofic.LiteralP13HodgeResidual42Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual42Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual42Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual42Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_2 :
    ∑ c : Fin 293, (residualNumerator 4 2 c).natAbs = 7779090332 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_4_2_0, residual_part_sum_4_2_1, residual_part_sum_4_2_2, residual_part_sum_4_2_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
