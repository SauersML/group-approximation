import GroupApproximation.Sofic.LiteralP13HodgeResidual00Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual00Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual00Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual00Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_0 :
    ∑ c : Fin 293, (residualNumerator 0 0 c).natAbs = 11626413589061 := by
  refine (sum_natAbs_eq_of_part_sums 0 0
    residual_part_sum_0_0_0 residual_part_sum_0_0_1
    residual_part_sum_0_0_2 residual_part_sum_0_0_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
