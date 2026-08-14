import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (4, 1). -/

theorem residual_chunk_4_1_9 : initialChunk 4 1 9 = 110653140 := by
  decide

theorem residual_chunk_4_1_10 : initialChunk 4 1 10 = 158325357 := by
  decide

theorem residual_chunk_4_1_11 : initialChunk 4 1 11 = 52177095 := by
  decide

theorem residual_chunk_4_1_12 : initialChunk 4 1 12 = 174838610 := by
  decide

theorem residual_chunk_4_1_13 : initialChunk 4 1 13 = 258242664 := by
  decide

theorem residual_chunk_4_1_14 : initialChunk 4 1 14 = 106992483 := by
  decide

theorem residual_chunk_4_1_15 : initialChunk 4 1 15 = 175034294 := by
  decide

theorem residual_chunk_4_1_16 : initialChunk 4 1 16 = 178453588 := by
  decide

theorem residual_chunk_4_1_17 : initialChunk 4 1 17 = 324382020 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_1_1 : initialPart 4 1 1 = 1539099251 := by
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
  rw [residual_chunk_4_1_9, residual_chunk_4_1_10, residual_chunk_4_1_11, residual_chunk_4_1_12, residual_chunk_4_1_13, residual_chunk_4_1_14, residual_chunk_4_1_15, residual_chunk_4_1_16, residual_chunk_4_1_17]

end LiteralP13HodgeCertificate
end GroupApproximation

