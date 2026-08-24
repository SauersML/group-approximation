import GroupApproximation.Sofic.LiteralP13HodgeResidual15

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_1 :
    ∑ c : Fin 293, (residualNumerator 5 1 c).natAbs = 6652740039 := by
  rw [sum_residual_natAbs_transpose_of_ne 1 5 (by decide)]
  exact residual_block_natAbs_1_5

end LiteralP13HodgeCertificate
end GroupApproximation

