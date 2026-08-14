import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (1, 5). -/

theorem residual_chunk_1_5_9 : initialChunk 1 5 9 = 182822329 := by
  decide

theorem residual_chunk_1_5_10 : initialChunk 1 5 10 = 321918539 := by
  decide

theorem residual_chunk_1_5_11 : initialChunk 1 5 11 = 146183810 := by
  decide

theorem residual_chunk_1_5_12 : initialChunk 1 5 12 = 244250420 := by
  decide

theorem residual_chunk_1_5_13 : initialChunk 1 5 13 = 171006354 := by
  decide

theorem residual_chunk_1_5_14 : initialChunk 1 5 14 = 163138744 := by
  decide

theorem residual_chunk_1_5_15 : initialChunk 1 5 15 = 113159239 := by
  decide

theorem residual_chunk_1_5_16 : initialChunk 1 5 16 = 76208923 := by
  decide

theorem residual_chunk_1_5_17 : initialChunk 1 5 17 = 157277451 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_5_1 : initialPart 1 5 1 = 1575965809 := by
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
  rw [residual_chunk_1_5_9, residual_chunk_1_5_10, residual_chunk_1_5_11, residual_chunk_1_5_12, residual_chunk_1_5_13, residual_chunk_1_5_14, residual_chunk_1_5_15, residual_chunk_1_5_16, residual_chunk_1_5_17]

end LiteralP13HodgeCertificate
end GroupApproximation

