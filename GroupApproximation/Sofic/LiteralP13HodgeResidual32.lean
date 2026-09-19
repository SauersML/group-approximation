import GroupApproximation.Sofic.LiteralP13HodgeResidual32Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual32Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual32Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual32Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_2 :
    ∑ c : Fin 293, (residualNumerator 3 2 c).natAbs = 8331331951 := by
  refine (sum_natAbs_eq_of_part_sums 3 2
    residual_part_sum_3_2_0 residual_part_sum_3_2_1
    residual_part_sum_3_2_2 residual_part_sum_3_2_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
