import GroupApproximation.Sofic.LiteralP13HodgeResidual35
import GroupApproximation.Sofic.LiteralP13HodgeTranspose

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_3 :
    ∑ c : Fin 293, (residualNumerator 5 3 c).natAbs = 6828814009 := by
  rw [sum_residual_natAbs_transpose_of_ne 3 5 (by decide)]
  exact residual_block_natAbs_3_5

end LiteralP13HodgeCertificate
end GroupApproximation
