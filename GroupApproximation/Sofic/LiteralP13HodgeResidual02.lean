import GroupApproximation.Sofic.LiteralP13HodgeResidual02Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual02Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual02Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual02Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_2 :
    ∑ c : Fin 293, (residualNumerator 0 2 c).natAbs = 9079445487 := by
  refine (sum_natAbs_eq_of_part_sums 0 2
    residual_part_sum_0_2_0 residual_part_sum_0_2_1
    residual_part_sum_0_2_2 residual_part_sum_0_2_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
