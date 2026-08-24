import GroupApproximation.Sofic.LiteralP13HodgeResidual01

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_1_0 :
    ∑ c : Fin 293, (residualNumerator 1 0 c).natAbs = 9037219251 := by
  rw [sum_residual_natAbs_transpose_of_ne 0 1 (by decide)]
  exact residual_block_natAbs_0_1

end LiteralP13HodgeCertificate
end GroupApproximation
