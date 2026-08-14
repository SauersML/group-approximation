import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (1, 2). -/

theorem residual_chunk_1_2_9 : initialChunk 1 2 9 = 276149464 := by
  decide

theorem residual_chunk_1_2_10 : initialChunk 1 2 10 = 255771507 := by
  decide

theorem residual_chunk_1_2_11 : initialChunk 1 2 11 = 160586088 := by
  decide

theorem residual_chunk_1_2_12 : initialChunk 1 2 12 = 314571052 := by
  decide

theorem residual_chunk_1_2_13 : initialChunk 1 2 13 = 197947315 := by
  decide

theorem residual_chunk_1_2_14 : initialChunk 1 2 14 = 221909818 := by
  decide

theorem residual_chunk_1_2_15 : initialChunk 1 2 15 = 264672573 := by
  decide

theorem residual_chunk_1_2_16 : initialChunk 1 2 16 = 224116558 := by
  decide

theorem residual_chunk_1_2_17 : initialChunk 1 2 17 = 414575047 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_2_1 : initialPart 1 2 1 = 2330299422 := by
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
  rw [residual_chunk_1_2_9, residual_chunk_1_2_10, residual_chunk_1_2_11, residual_chunk_1_2_12, residual_chunk_1_2_13, residual_chunk_1_2_14, residual_chunk_1_2_15, residual_chunk_1_2_16, residual_chunk_1_2_17]

end LiteralP13HodgeCertificate
end GroupApproximation

