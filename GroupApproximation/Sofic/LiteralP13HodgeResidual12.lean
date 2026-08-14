import GroupApproximation.Sofic.LiteralP13HodgeResidual12Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual12Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual12Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual12Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_2 :
    ∑ c : Fin 293, (residualNumerator 1 2 c).natAbs = 7915229999 := by
  refine (sum_natAbs_eq_of_part_sums 1 2
    residual_part_sum_1_2_0 residual_part_sum_1_2_1
    residual_part_sum_1_2_2 residual_part_sum_1_2_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
