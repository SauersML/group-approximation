import GroupApproximation.Sofic.LiteralP13HodgeResidual24Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual24Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual24Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual24Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_4 :
    ∑ c : Fin 293, (residualNumerator 2 4 c).natAbs = 7779090332 := by
  refine (sum_natAbs_eq_of_part_sums 2 4
    residual_part_sum_2_4_0 residual_part_sum_2_4_1
    residual_part_sum_2_4_2 residual_part_sum_2_4_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
