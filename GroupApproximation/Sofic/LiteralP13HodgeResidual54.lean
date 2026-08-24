import GroupApproximation.Sofic.LiteralP13HodgeResidual45

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_4 :
    ∑ c : Fin 293, (residualNumerator 5 4 c).natAbs = 6642855556 := by
  rw [sum_residual_natAbs_transpose_of_ne 4 5 (by decide)]
  exact residual_block_natAbs_4_5

end LiteralP13HodgeCertificate
end GroupApproximation
