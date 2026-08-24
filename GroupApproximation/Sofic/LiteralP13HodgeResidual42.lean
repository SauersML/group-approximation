import GroupApproximation.Sofic.LiteralP13HodgeResidual24

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_4_2 :
    ∑ c : Fin 293, (residualNumerator 4 2 c).natAbs = 7779090332 := by
  rw [sum_residual_natAbs_transpose_of_ne 2 4 (by decide)]
  exact residual_block_natAbs_2_4

end LiteralP13HodgeCertificate
end GroupApproximation

