import GroupApproximation.Sofic.LiteralP13HodgeResidual13Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual13Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual13Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual13Part3

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_3 :
    ∑ c : Fin 293, (residualNumerator 1 3 c).natAbs = 6215318798 := by
  rw [sum_natAbs_eq_parts]
  rw [Fin.sum_univ_four]
  simp only [add_assoc]
  rw [residual_part_sum_1_3_0, residual_part_sum_1_3_1, residual_part_sum_1_3_2, residual_part_sum_1_3_3]
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
