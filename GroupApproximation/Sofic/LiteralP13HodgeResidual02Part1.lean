import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (0, 2). -/

theorem residual_chunk_0_2_9 : initialChunk 0 2 9 = 305892543 := by
  decide

theorem residual_chunk_0_2_10 : initialChunk 0 2 10 = 224880617 := by
  decide

theorem residual_chunk_0_2_11 : initialChunk 0 2 11 = 270461214 := by
  decide

theorem residual_chunk_0_2_12 : initialChunk 0 2 12 = 282710208 := by
  decide

theorem residual_chunk_0_2_13 : initialChunk 0 2 13 = 176476043 := by
  decide

theorem residual_chunk_0_2_14 : initialChunk 0 2 14 = 308746219 := by
  decide

theorem residual_chunk_0_2_15 : initialChunk 0 2 15 = 127795137 := by
  decide

theorem residual_chunk_0_2_16 : initialChunk 0 2 16 = 207579014 := by
  decide

theorem residual_chunk_0_2_17 : initialChunk 0 2 17 = 286133967 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_2_1 : initialPart 0 2 1 = 2190674962 := by
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
  rw [residual_chunk_0_2_9, residual_chunk_0_2_10, residual_chunk_0_2_11, residual_chunk_0_2_12, residual_chunk_0_2_13, residual_chunk_0_2_14, residual_chunk_0_2_15, residual_chunk_0_2_16, residual_chunk_0_2_17]

end LiteralP13HodgeCertificate
end GroupApproximation
