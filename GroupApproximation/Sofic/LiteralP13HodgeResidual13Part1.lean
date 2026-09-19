import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (1, 3). -/

theorem residual_chunk_1_3_9 : initialChunk 1 3 9 = 344056389 := by
  decide

theorem residual_chunk_1_3_10 : initialChunk 1 3 10 = 259078930 := by
  decide

theorem residual_chunk_1_3_11 : initialChunk 1 3 11 = 97095700 := by
  decide

theorem residual_chunk_1_3_12 : initialChunk 1 3 12 = 178198895 := by
  decide

theorem residual_chunk_1_3_13 : initialChunk 1 3 13 = 183831860 := by
  decide

theorem residual_chunk_1_3_14 : initialChunk 1 3 14 = 97299854 := by
  decide

theorem residual_chunk_1_3_15 : initialChunk 1 3 15 = 196070636 := by
  decide

theorem residual_chunk_1_3_16 : initialChunk 1 3 16 = 91921514 := by
  decide

theorem residual_chunk_1_3_17 : initialChunk 1 3 17 = 159147522 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_3_1 : initialPart 1 3 1 = 1606701300 := by
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
  rw [residual_chunk_1_3_9, residual_chunk_1_3_10, residual_chunk_1_3_11, residual_chunk_1_3_12, residual_chunk_1_3_13, residual_chunk_1_3_14, residual_chunk_1_3_15, residual_chunk_1_3_16, residual_chunk_1_3_17]

end LiteralP13HodgeCertificate
end GroupApproximation
