import GroupApproximation.Sofic.LiteralP13HodgeResidual34Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual34Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual34Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual34Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_4 :
    ∑ c : Fin 293, (residualNumerator 3 4 c).natAbs = 6257693699 := by
  refine (sum_natAbs_eq_of_part_sums 3 4
    residual_part_sum_3_4_0 residual_part_sum_3_4_1
    residual_part_sum_3_4_2 residual_part_sum_3_4_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
