import GroupApproximation.Sofic.LiteralP13HodgeResidual13Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual13Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual13Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual13Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_3 :
    ∑ c : Fin 293, (residualNumerator 1 3 c).natAbs = 6215318798 := by
  refine (sum_natAbs_eq_of_part_sums 1 3
    residual_part_sum_1_3_0 residual_part_sum_1_3_1
    residual_part_sum_1_3_2 residual_part_sum_1_3_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
