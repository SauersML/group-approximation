import GroupApproximation.Sofic.LiteralP13HodgeResidual43Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual43Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual43Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual43Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_3 :
    ∑ c : Fin 293, (residualNumerator 4 3 c).natAbs = 6257693699 := by
  refine (sum_natAbs_eq_of_part_sums 4 3
    residual_part_sum_4_3_0 residual_part_sum_4_3_1
    residual_part_sum_4_3_2 residual_part_sum_4_3_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
