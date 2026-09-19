import GroupApproximation.Sofic.LiteralP13HodgeResidual14Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual14Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual14Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual14Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_4 :
    ∑ c : Fin 293, (residualNumerator 1 4 c).natAbs = 6701810124 := by
  refine (sum_natAbs_eq_of_part_sums 1 4
    residual_part_sum_1_4_0 residual_part_sum_1_4_1
    residual_part_sum_1_4_2 residual_part_sum_1_4_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
