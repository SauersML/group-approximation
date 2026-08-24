import GroupApproximation.Sofic.LiteralP13HodgeResidual02

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_2_0 :
    ∑ c : Fin 293, (residualNumerator 2 0 c).natAbs = 9079445487 := by
  rw [sum_residual_natAbs_transpose_of_ne 0 2 (by decide)]
  exact residual_block_natAbs_0_2

end LiteralP13HodgeCertificate
end GroupApproximation

