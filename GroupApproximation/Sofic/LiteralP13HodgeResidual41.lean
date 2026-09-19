import GroupApproximation.Sofic.LiteralP13HodgeResidual14
import GroupApproximation.Sofic.LiteralP13HodgeTranspose

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_1 :
    ∑ c : Fin 293, (residualNumerator 4 1 c).natAbs = 6701810124 := by
  rw [sum_residual_natAbs_transpose_of_ne 1 4 (by decide)]
  exact residual_block_natAbs_1_4

end LiteralP13HodgeCertificate
end GroupApproximation
