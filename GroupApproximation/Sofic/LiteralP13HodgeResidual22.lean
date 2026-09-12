import GroupApproximation.Sofic.LiteralP13HodgeResidual22Part0
import GroupApproximation.Sofic.LiteralP13HodgeResidual22Part1
import GroupApproximation.Sofic.LiteralP13HodgeResidual22Part2
import GroupApproximation.Sofic.LiteralP13HodgeResidual22Part3
import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_2 :
    ∑ c : Fin 293, (residualNumerator 2 2 c).natAbs = 11624840006764 := by
  refine (sum_natAbs_eq_of_part_sums 2 2
    residual_part_sum_2_2_0 residual_part_sum_2_2_1
    residual_part_sum_2_2_2 residual_part_sum_2_2_3).trans ?_
  norm_num

end LiteralP13HodgeCertificate
end GroupApproximation
