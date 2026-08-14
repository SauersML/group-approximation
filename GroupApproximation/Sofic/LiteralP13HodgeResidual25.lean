import GroupApproximation.Sofic.LiteralP13HodgeResidual25Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual25Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual25Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual25Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_5 :
    ∑ c : Fin 293, (residualNumerator 2 5 c).natAbs = 7921451991 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_2_5_0, residual_part_sum_2_5_1, residual_part_sum_2_5_2, residual_part_sum_2_5_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
