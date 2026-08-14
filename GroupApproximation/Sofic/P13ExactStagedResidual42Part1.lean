import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (4, 2). -/

theorem residual_chunk_4_2_9 : initialChunk 4 2 9 = 342784900 := by
  decide

theorem residual_chunk_4_2_10 : initialChunk 4 2 10 = 209730840 := by
  decide

theorem residual_chunk_4_2_11 : initialChunk 4 2 11 = 145005112 := by
  decide

theorem residual_chunk_4_2_12 : initialChunk 4 2 12 = 208967523 := by
  decide

theorem residual_chunk_4_2_13 : initialChunk 4 2 13 = 313555532 := by
  decide

theorem residual_chunk_4_2_14 : initialChunk 4 2 14 = 154935752 := by
  decide

theorem residual_chunk_4_2_15 : initialChunk 4 2 15 = 155420392 := by
  decide

theorem residual_chunk_4_2_16 : initialChunk 4 2 16 = 220895247 := by
  decide

theorem residual_chunk_4_2_17 : initialChunk 4 2 17 = 280058593 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_2_1 : initialPart 4 2 1 = 2031353891 := by
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
  rw [residual_chunk_4_2_9, residual_chunk_4_2_10, residual_chunk_4_2_11, residual_chunk_4_2_12, residual_chunk_4_2_13, residual_chunk_4_2_14, residual_chunk_4_2_15, residual_chunk_4_2_16, residual_chunk_4_2_17]

end LiteralP13HodgeCertificate
end GroupApproximation

