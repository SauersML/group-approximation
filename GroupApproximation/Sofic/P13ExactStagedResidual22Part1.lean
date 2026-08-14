import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (2, 2). -/

theorem residual_chunk_2_2_9 : initialChunk 2 2 9 = 393821038 := by
  decide

theorem residual_chunk_2_2_10 : initialChunk 2 2 10 = 111695230 := by
  decide

theorem residual_chunk_2_2_11 : initialChunk 2 2 11 = 117854830 := by
  decide

theorem residual_chunk_2_2_12 : initialChunk 2 2 12 = 362164837 := by
  decide

theorem residual_chunk_2_2_13 : initialChunk 2 2 13 = 284878911 := by
  decide

theorem residual_chunk_2_2_14 : initialChunk 2 2 14 = 319629592 := by
  decide

theorem residual_chunk_2_2_15 : initialChunk 2 2 15 = 141841327 := by
  decide

theorem residual_chunk_2_2_16 : initialChunk 2 2 16 = 310245465 := by
  decide

theorem residual_chunk_2_2_17 : initialChunk 2 2 17 = 235480252 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_2_1 : initialPart 2 2 1 = 2277611482 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((1 : Fin 4), (0 : Fin 9)) = (9 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (1 : Fin 9)) = (10 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (2 : Fin 9)) = (11 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (3 : Fin 9)) = (12 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (4 : Fin 9)) = (13 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (5 : Fin 9)) = (14 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (6 : Fin 9)) = (15 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (7 : Fin 9)) = (16 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (8 : Fin 9)) = (17 : Fin 36) by decide]
  rw [residual_chunk_2_2_9, residual_chunk_2_2_10, residual_chunk_2_2_11, residual_chunk_2_2_12, residual_chunk_2_2_13, residual_chunk_2_2_14, residual_chunk_2_2_15, residual_chunk_2_2_16, residual_chunk_2_2_17]

end LiteralP13HodgeCertificate
end GroupApproximation

