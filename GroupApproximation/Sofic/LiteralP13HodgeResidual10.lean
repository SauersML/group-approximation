import GroupApproximation.Sofic.LiteralP13HodgeResidual10Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual10Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual10Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual10Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_0 :
    ∑ c : Fin 293, (residualNumerator 1 0 c).natAbs = 9037219251 := by
  refine (sum_natAbs_eq_of_part_sums 1 0
    residual_part_sum_1_0_0 residual_part_sum_1_0_1
    residual_part_sum_1_0_2 residual_part_sum_1_0_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
