import GroupApproximation.Sofic.LiteralP13HodgeResidual34

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_3 :
    ∑ c : Fin 293, (residualNumerator 4 3 c).natAbs = 6257693699 := by
  rw [sum_residual_natAbs_transpose_of_ne 3 4 (by decide)]
  exact residual_block_natAbs_3_4

end LiteralP13HodgeCertificate
end GroupApproximation

