import GroupApproximation.Sofic.LiteralP13HodgeResidual50Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual50Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual50Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual50Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_0 :
    ∑ c : Fin 293, (residualNumerator 5 0 c).natAbs = 8235929367 := by
  refine (sum_natAbs_eq_of_part_sums 5 0
    residual_part_sum_5_0_0 residual_part_sum_5_0_1
    residual_part_sum_5_0_2 residual_part_sum_5_0_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
