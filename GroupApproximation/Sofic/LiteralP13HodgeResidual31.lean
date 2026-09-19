import GroupApproximation.Sofic.LiteralP13HodgeResidual31Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual31Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual31Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual31Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_1 :
    ∑ c : Fin 293, (residualNumerator 3 1 c).natAbs = 6215318798 := by
  refine (sum_natAbs_eq_of_part_sums 3 1
    residual_part_sum_3_1_0 residual_part_sum_3_1_1
    residual_part_sum_3_1_2 residual_part_sum_3_1_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
