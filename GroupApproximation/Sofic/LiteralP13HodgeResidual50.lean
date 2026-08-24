import GroupApproximation.Sofic.LiteralP13HodgeResidual05

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_0 :
    ∑ c : Fin 293, (residualNumerator 5 0 c).natAbs = 8235929367 := by
  rw [sum_residual_natAbs_transpose_of_ne 0 5 (by decide)]
  exact residual_block_natAbs_0_5

end LiteralP13HodgeCertificate
end GroupApproximation
