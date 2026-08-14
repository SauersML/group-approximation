import GroupApproximation.Sofic.LiteralP13HodgeResidual54Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual54Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual54Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual54Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_4 :
    ∑ c : Fin 293, (residualNumerator 5 4 c).natAbs = 6642855556 := by
  refine (sum_natAbs_eq_of_part_sums 5 4
    residual_part_sum_5_4_0 residual_part_sum_5_4_1
    residual_part_sum_5_4_2 residual_part_sum_5_4_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
