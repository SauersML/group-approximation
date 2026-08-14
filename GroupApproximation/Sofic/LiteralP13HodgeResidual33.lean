import GroupApproximation.Sofic.LiteralP13HodgeResidual33Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual33Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual33Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual33Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_3 :
    ∑ c : Fin 293, (residualNumerator 3 3 c).natAbs = 11621832714147 := by
  refine (sum_natAbs_eq_of_part_sums 3 3
    residual_part_sum_3_3_0 residual_part_sum_3_3_1
    residual_part_sum_3_3_2 residual_part_sum_3_3_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
