import GroupApproximation.Sofic.LiteralP13HodgeResidual01Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual01Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual01Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual01Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_1 :
    ∑ c : Fin 293, (residualNumerator 0 1 c).natAbs = 9037219251 := by
  refine (sum_natAbs_eq_of_part_sums 0 1
    residual_part_sum_0_1_0 residual_part_sum_0_1_1
    residual_part_sum_0_1_2 residual_part_sum_0_1_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
