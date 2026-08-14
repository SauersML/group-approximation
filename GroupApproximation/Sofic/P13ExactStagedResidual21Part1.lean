import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (2, 1). -/

theorem residual_chunk_2_1_9 : initialChunk 2 1 9 = 304725228 := by
  decide

theorem residual_chunk_2_1_10 : initialChunk 2 1 10 = 64034822 := by
  decide

theorem residual_chunk_2_1_11 : initialChunk 2 1 11 = 87389645 := by
  decide

theorem residual_chunk_2_1_12 : initialChunk 2 1 12 = 283378248 := by
  decide

theorem residual_chunk_2_1_13 : initialChunk 2 1 13 = 190921518 := by
  decide

theorem residual_chunk_2_1_14 : initialChunk 2 1 14 = 68693903 := by
  decide

theorem residual_chunk_2_1_15 : initialChunk 2 1 15 = 174661060 := by
  decide

theorem residual_chunk_2_1_16 : initialChunk 2 1 16 = 122166403 := by
  decide

theorem residual_chunk_2_1_17 : initialChunk 2 1 17 = 87737365 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_1_1 : initialPart 2 1 1 = 1383708192 := by
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
  rw [residual_chunk_2_1_9, residual_chunk_2_1_10, residual_chunk_2_1_11, residual_chunk_2_1_12, residual_chunk_2_1_13, residual_chunk_2_1_14, residual_chunk_2_1_15, residual_chunk_2_1_16, residual_chunk_2_1_17]

end LiteralP13HodgeCertificate
end GroupApproximation

