import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (2, 4). -/

theorem residual_chunk_2_4_9 : initialChunk 2 4 9 = 179535587 := by
  decide

theorem residual_chunk_2_4_10 : initialChunk 2 4 10 = 107933351 := by
  decide

theorem residual_chunk_2_4_11 : initialChunk 2 4 11 = 107589658 := by
  decide

theorem residual_chunk_2_4_12 : initialChunk 2 4 12 = 300648816 := by
  decide

theorem residual_chunk_2_4_13 : initialChunk 2 4 13 = 220870363 := by
  decide

theorem residual_chunk_2_4_14 : initialChunk 2 4 14 = 140561454 := by
  decide

theorem residual_chunk_2_4_15 : initialChunk 2 4 15 = 237246748 := by
  decide

theorem residual_chunk_2_4_16 : initialChunk 2 4 16 = 210163523 := by
  decide

theorem residual_chunk_2_4_17 : initialChunk 2 4 17 = 229024739 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_4_1 : initialPart 2 4 1 = 1733574239 := by
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
  rw [residual_chunk_2_4_9, residual_chunk_2_4_10, residual_chunk_2_4_11, residual_chunk_2_4_12, residual_chunk_2_4_13, residual_chunk_2_4_14, residual_chunk_2_4_15, residual_chunk_2_4_16, residual_chunk_2_4_17]

end LiteralP13HodgeCertificate
end GroupApproximation
