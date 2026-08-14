import GroupApproximation.Sofic.LiteralP13HodgeResidual52Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual52Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual52Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual52Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_2 :
    ∑ c : Fin 293, (residualNumerator 5 2 c).natAbs = 7921451991 := by
  refine (sum_natAbs_eq_of_part_sums 5 2
    residual_part_sum_5_2_0 residual_part_sum_5_2_1
    residual_part_sum_5_2_2 residual_part_sum_5_2_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
