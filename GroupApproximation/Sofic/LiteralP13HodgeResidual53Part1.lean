import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (5, 3). -/

theorem residual_chunk_5_3_9 : initialChunk 5 3 9 = 289251817 := by
  decide

theorem residual_chunk_5_3_10 : initialChunk 5 3 10 = 171011151 := by
  decide

theorem residual_chunk_5_3_11 : initialChunk 5 3 11 = 148337224 := by
  decide

theorem residual_chunk_5_3_12 : initialChunk 5 3 12 = 163188234 := by
  decide

theorem residual_chunk_5_3_13 : initialChunk 5 3 13 = 83128885 := by
  decide

theorem residual_chunk_5_3_14 : initialChunk 5 3 14 = 89406393 := by
  decide

theorem residual_chunk_5_3_15 : initialChunk 5 3 15 = 189684432 := by
  decide

theorem residual_chunk_5_3_16 : initialChunk 5 3 16 = 147278537 := by
  decide

theorem residual_chunk_5_3_17 : initialChunk 5 3 17 = 186211109 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_3_1 : initialPart 5 3 1 = 1467497782 := by
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
  rw [residual_chunk_5_3_9, residual_chunk_5_3_10, residual_chunk_5_3_11, residual_chunk_5_3_12, residual_chunk_5_3_13, residual_chunk_5_3_14, residual_chunk_5_3_15, residual_chunk_5_3_16, residual_chunk_5_3_17]

end LiteralP13HodgeCertificate
end GroupApproximation
