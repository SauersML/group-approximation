import GroupApproximation.Sofic.LiteralP13HodgeResidual05Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual05Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual05Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual05Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_5 :
    ∑ c : Fin 293, (residualNumerator 0 5 c).natAbs = 8235929367 := by
  refine (sum_natAbs_eq_of_part_sums 0 5
    residual_part_sum_0_5_0 residual_part_sum_0_5_1
    residual_part_sum_0_5_2 residual_part_sum_0_5_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
