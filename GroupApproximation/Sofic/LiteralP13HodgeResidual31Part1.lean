import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (3, 1). -/

theorem residual_chunk_3_1_9 : initialChunk 3 1 9 = 170304636 := by
  decide

theorem residual_chunk_3_1_10 : initialChunk 3 1 10 = 141252357 := by
  decide

theorem residual_chunk_3_1_11 : initialChunk 3 1 11 = 170300865 := by
  decide

theorem residual_chunk_3_1_12 : initialChunk 3 1 12 = 271916877 := by
  decide

theorem residual_chunk_3_1_13 : initialChunk 3 1 13 = 226392020 := by
  decide

theorem residual_chunk_3_1_14 : initialChunk 3 1 14 = 120758487 := by
  decide

theorem residual_chunk_3_1_15 : initialChunk 3 1 15 = 253444890 := by
  decide

theorem residual_chunk_3_1_16 : initialChunk 3 1 16 = 180342853 := by
  decide

theorem residual_chunk_3_1_17 : initialChunk 3 1 17 = 221596124 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_1_1 : initialPart 3 1 1 = 1756309109 := by
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
  rw [residual_chunk_3_1_9, residual_chunk_3_1_10, residual_chunk_3_1_11, residual_chunk_3_1_12, residual_chunk_3_1_13, residual_chunk_3_1_14, residual_chunk_3_1_15, residual_chunk_3_1_16, residual_chunk_3_1_17]

end LiteralP13HodgeCertificate
end GroupApproximation
