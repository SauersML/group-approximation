import GroupApproximation.Sofic.LiteralP13HodgeResidual15Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual15Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual15Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual15Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_5 :
    ∑ c : Fin 293, (residualNumerator 1 5 c).natAbs = 6652740039 := by
  refine (sum_natAbs_eq_of_part_sums 1 5
    residual_part_sum_1_5_0 residual_part_sum_1_5_1
    residual_part_sum_1_5_2 residual_part_sum_1_5_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
