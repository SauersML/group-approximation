import GroupApproximation.Sofic.LiteralP13HodgeResidual03Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual03Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual03Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual03Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_0_3 :
    ∑ c : Fin 293, (residualNumerator 0 3 c).natAbs = 9283845417 := by
  refine (sum_natAbs_eq_of_part_sums 0 3
    residual_part_sum_0_3_0 residual_part_sum_0_3_1
    residual_part_sum_0_3_2 residual_part_sum_0_3_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
