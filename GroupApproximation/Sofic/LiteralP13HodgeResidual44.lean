import GroupApproximation.Sofic.LiteralP13HodgeResidual44Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual44Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual44Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual44Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_4 :
    ∑ c : Fin 293, (residualNumerator 4 4 c).natAbs = 11622780615189 := by
  refine (sum_natAbs_eq_of_part_sums 4 4
    residual_part_sum_4_4_0 residual_part_sum_4_4_1
    residual_part_sum_4_4_2 residual_part_sum_4_4_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
