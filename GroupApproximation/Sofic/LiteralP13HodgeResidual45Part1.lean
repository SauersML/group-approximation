import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (4, 5). -/

theorem residual_chunk_4_5_9 : initialChunk 4 5 9 = 381547933 := by
  decide

theorem residual_chunk_4_5_10 : initialChunk 4 5 10 = 335556497 := by
  decide

theorem residual_chunk_4_5_11 : initialChunk 4 5 11 = 91714946 := by
  decide

theorem residual_chunk_4_5_12 : initialChunk 4 5 12 = 372196339 := by
  decide

theorem residual_chunk_4_5_13 : initialChunk 4 5 13 = 179754732 := by
  decide

theorem residual_chunk_4_5_14 : initialChunk 4 5 14 = 61056032 := by
  decide

theorem residual_chunk_4_5_15 : initialChunk 4 5 15 = 78273576 := by
  decide

theorem residual_chunk_4_5_16 : initialChunk 4 5 16 = 163117216 := by
  decide

theorem residual_chunk_4_5_17 : initialChunk 4 5 17 = 137064845 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_5_1 : initialPart 4 5 1 = 1800282116 := by
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
  rw [residual_chunk_4_5_9, residual_chunk_4_5_10, residual_chunk_4_5_11, residual_chunk_4_5_12, residual_chunk_4_5_13, residual_chunk_4_5_14, residual_chunk_4_5_15, residual_chunk_4_5_16, residual_chunk_4_5_17]

end LiteralP13HodgeCertificate
end GroupApproximation
