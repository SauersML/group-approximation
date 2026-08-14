import GroupApproximation.Sofic.LiteralP13HodgeResidual55Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual55Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual55Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual55Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_5 :
    ∑ c : Fin 293, (residualNumerator 5 5 c).natAbs = 11622680190256 := by
  refine (sum_natAbs_eq_of_part_sums 5 5
    residual_part_sum_5_5_0 residual_part_sum_5_5_1
    residual_part_sum_5_5_2 residual_part_sum_5_5_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
