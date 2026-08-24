import GroupApproximation.Sofic.LiteralP13HodgeResidual04

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_0 :
    ∑ c : Fin 293, (residualNumerator 4 0 c).natAbs = 8836491131 := by
  rw [sum_residual_natAbs_transpose_of_ne 0 4 (by decide)]
  exact residual_block_natAbs_0_4

end LiteralP13HodgeCertificate
end GroupApproximation
