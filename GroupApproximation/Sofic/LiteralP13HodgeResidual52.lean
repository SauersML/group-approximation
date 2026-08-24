import GroupApproximation.Sofic.LiteralP13HodgeResidual25

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

theorem residual_block_natAbs_5_2 :
    ∑ c : Fin 293, (residualNumerator 5 2 c).natAbs = 7921451991 := by
  rw [sum_residual_natAbs_transpose_of_ne 2 5 (by decide)]
  exact residual_block_natAbs_2_5

end LiteralP13HodgeCertificate
end GroupApproximation
