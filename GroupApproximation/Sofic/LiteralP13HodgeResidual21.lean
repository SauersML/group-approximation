import GroupApproximation.Sofic.LiteralP13HodgeResidual12
import GroupApproximation.Sofic.LiteralP13HodgeTranspose

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_1 :
    ∑ c : Fin 293, (residualNumerator 2 1 c).natAbs = 7915229999 := by
  rw [sum_residual_natAbs_transpose_of_ne 1 2 (by decide)]
  exact residual_block_natAbs_1_2

end LiteralP13HodgeCertificate
end GroupApproximation
