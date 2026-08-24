import GroupApproximation.Sofic.LiteralP13HodgeResidual03

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_0 :
    ∑ c : Fin 293, (residualNumerator 3 0 c).natAbs = 9283845417 := by
  rw [sum_residual_natAbs_transpose_of_ne 0 3 (by decide)]
  exact residual_block_natAbs_0_3

end LiteralP13HodgeCertificate
end GroupApproximation
