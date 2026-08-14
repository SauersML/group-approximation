import GroupApproximation.Sofic.LiteralP13HodgeResidual53Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual53Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual53Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual53Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_3 :
    ∑ c : Fin 293, (residualNumerator 5 3 c).natAbs = 6828814009 := by
  refine (sum_natAbs_eq_of_part_sums 5 3
    residual_part_sum_5_3_0 residual_part_sum_5_3_1
    residual_part_sum_5_3_2 residual_part_sum_5_3_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
