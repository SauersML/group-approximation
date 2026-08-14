import GroupApproximation.Sofic.LiteralP13HodgeResidual51Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual51Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual51Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual51Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_1 :
    ∑ c : Fin 293, (residualNumerator 5 1 c).natAbs = 6652740039 := by
  refine (sum_natAbs_eq_of_part_sums 5 1
    residual_part_sum_5_1_0 residual_part_sum_5_1_1
    residual_part_sum_5_1_2 residual_part_sum_5_1_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
