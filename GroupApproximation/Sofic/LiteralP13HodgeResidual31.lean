import GroupApproximation.Sofic.LiteralP13HodgeResidual13

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_3_1 :
    ∑ c : Fin 293, (residualNumerator 3 1 c).natAbs = 6215318798 := by
  rw [sum_residual_natAbs_transpose_of_ne 1 3 (by decide)]
  exact residual_block_natAbs_1_3

end LiteralP13HodgeCertificate
end GroupApproximation

