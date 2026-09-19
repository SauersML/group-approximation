import GroupApproximation.Sofic.LiteralP13HodgeResidual11Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual11Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual11Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual11Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_1 :
    ∑ c : Fin 293, (residualNumerator 1 1 c).natAbs = 11622602362466 := by
  refine (sum_natAbs_eq_of_part_sums 1 1
    residual_part_sum_1_1_0 residual_part_sum_1_1_1
    residual_part_sum_1_1_2 residual_part_sum_1_1_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
