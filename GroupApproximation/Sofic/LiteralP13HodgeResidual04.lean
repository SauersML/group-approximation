import GroupApproximation.Sofic.LiteralP13HodgeResidual04Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual04Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual04Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual04Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_4 :
    ∑ c : Fin 293, (residualNumerator 0 4 c).natAbs = 8836491131 := by
  refine (sum_natAbs_eq_of_part_sums 0 4
    residual_part_sum_0_4_0 residual_part_sum_0_4_1
    residual_part_sum_0_4_2 residual_part_sum_0_4_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
