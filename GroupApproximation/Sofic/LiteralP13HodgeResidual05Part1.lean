import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (0, 5). -/

theorem residual_chunk_0_5_9 : initialChunk 0 5 9 = 387780438 := by
  decide

theorem residual_chunk_0_5_10 : initialChunk 0 5 10 = 289055858 := by
  decide

theorem residual_chunk_0_5_11 : initialChunk 0 5 11 = 193061809 := by
  decide

theorem residual_chunk_0_5_12 : initialChunk 0 5 12 = 245808926 := by
  decide

theorem residual_chunk_0_5_13 : initialChunk 0 5 13 = 115272923 := by
  decide

theorem residual_chunk_0_5_14 : initialChunk 0 5 14 = 164962075 := by
  decide

theorem residual_chunk_0_5_15 : initialChunk 0 5 15 = 112898344 := by
  decide

theorem residual_chunk_0_5_16 : initialChunk 0 5 16 = 234803243 := by
  decide

theorem residual_chunk_0_5_17 : initialChunk 0 5 17 = 179186698 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_5_1 : initialPart 0 5 1 = 1922830314 := by
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
  rw [residual_chunk_0_5_9, residual_chunk_0_5_10, residual_chunk_0_5_11, residual_chunk_0_5_12, residual_chunk_0_5_13, residual_chunk_0_5_14, residual_chunk_0_5_15, residual_chunk_0_5_16, residual_chunk_0_5_17]

end LiteralP13HodgeCertificate
end GroupApproximation
