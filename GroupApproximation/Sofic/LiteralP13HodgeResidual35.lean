import GroupApproximation.Sofic.LiteralP13HodgeResidual35Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual35Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual35Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual35Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_5 :
    ∑ c : Fin 293, (residualNumerator 3 5 c).natAbs = 6828814009 := by
  refine (sum_natAbs_eq_of_part_sums 3 5
    residual_part_sum_3_5_0 residual_part_sum_3_5_1
    residual_part_sum_3_5_2 residual_part_sum_3_5_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
