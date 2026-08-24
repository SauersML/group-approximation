import GroupApproximation.Sofic.LiteralP13HodgeResidual23

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_2 :
    ∑ c : Fin 293, (residualNumerator 3 2 c).natAbs = 8331331951 := by
  rw [sum_residual_natAbs_transpose_of_ne 2 3 (by decide)]
  exact residual_block_natAbs_2_3

end LiteralP13HodgeCertificate
end GroupApproximation
