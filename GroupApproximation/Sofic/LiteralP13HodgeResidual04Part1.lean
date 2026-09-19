import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (0, 4). -/

theorem residual_chunk_0_4_9 : initialChunk 0 4 9 = 484712804 := by
  decide

theorem residual_chunk_0_4_10 : initialChunk 0 4 10 = 168176175 := by
  decide

theorem residual_chunk_0_4_11 : initialChunk 0 4 11 = 229171690 := by
  decide

theorem residual_chunk_0_4_12 : initialChunk 0 4 12 = 456941447 := by
  decide

theorem residual_chunk_0_4_13 : initialChunk 0 4 13 = 86681136 := by
  decide

theorem residual_chunk_0_4_14 : initialChunk 0 4 14 = 147568612 := by
  decide

theorem residual_chunk_0_4_15 : initialChunk 0 4 15 = 196177958 := by
  decide

theorem residual_chunk_0_4_16 : initialChunk 0 4 16 = 91987604 := by
  decide

theorem residual_chunk_0_4_17 : initialChunk 0 4 17 = 206098725 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_4_1 : initialPart 0 4 1 = 2067516151 := by
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
  rw [residual_chunk_0_4_9, residual_chunk_0_4_10, residual_chunk_0_4_11, residual_chunk_0_4_12, residual_chunk_0_4_13, residual_chunk_0_4_14, residual_chunk_0_4_15, residual_chunk_0_4_16, residual_chunk_0_4_17]

end LiteralP13HodgeCertificate
end GroupApproximation
