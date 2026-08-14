import GroupApproximation.Sofic.LiteralP13HodgeResidual40Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual40Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual40Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual40Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_0 :
    ∑ c : Fin 293, (residualNumerator 4 0 c).natAbs = 8836491131 := by
  refine (sum_natAbs_eq_of_part_sums 4 0
    residual_part_sum_4_0_0 residual_part_sum_4_0_1
    residual_part_sum_4_0_2 residual_part_sum_4_0_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
