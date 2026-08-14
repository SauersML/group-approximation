import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (3, 2). -/

theorem residual_chunk_3_2_9 : initialChunk 3 2 9 = 251280345 := by
  decide

theorem residual_chunk_3_2_10 : initialChunk 3 2 10 = 207499302 := by
  decide

theorem residual_chunk_3_2_11 : initialChunk 3 2 11 = 254357189 := by
  decide

theorem residual_chunk_3_2_12 : initialChunk 3 2 12 = 175414137 := by
  decide

theorem residual_chunk_3_2_13 : initialChunk 3 2 13 = 407220845 := by
  decide

theorem residual_chunk_3_2_14 : initialChunk 3 2 14 = 193082455 := by
  decide

theorem residual_chunk_3_2_15 : initialChunk 3 2 15 = 268133241 := by
  decide

theorem residual_chunk_3_2_16 : initialChunk 3 2 16 = 185481761 := by
  decide

theorem residual_chunk_3_2_17 : initialChunk 3 2 17 = 197824123 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_2_1 : initialPart 3 2 1 = 2140293398 := by
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
  rw [residual_chunk_3_2_9, residual_chunk_3_2_10, residual_chunk_3_2_11, residual_chunk_3_2_12, residual_chunk_3_2_13, residual_chunk_3_2_14, residual_chunk_3_2_15, residual_chunk_3_2_16, residual_chunk_3_2_17]

end LiteralP13HodgeCertificate
end GroupApproximation

