import GroupApproximation.Sofic.LiteralP13HodgeResidual44Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual44Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual44Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual44Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_4 :
    ∑ c : Fin 293, (residualNumerator 4 4 c).natAbs = 11622780615189 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_4_4_0, residual_part_sum_4_4_1, residual_part_sum_4_4_2, residual_part_sum_4_4_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
