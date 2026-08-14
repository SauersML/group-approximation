import GroupApproximation.Sofic.LiteralP13HodgeResidual41Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual41Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual41Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual41Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_1 :
    ∑ c : Fin 293, (residualNumerator 4 1 c).natAbs = 6701810124 := by
  refine (sum_natAbs_eq_of_part_sums 4 1
    residual_part_sum_4_1_0 residual_part_sum_4_1_1
    residual_part_sum_4_1_2 residual_part_sum_4_1_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
