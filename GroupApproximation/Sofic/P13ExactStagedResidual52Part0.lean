import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (5, 2). -/

theorem residual_chunk_5_2_0 : initialChunk 5 2 0 = 141915000 := by
  decide

theorem residual_chunk_5_2_1 : initialChunk 5 2 1 = 175303609 := by
  decide

theorem residual_chunk_5_2_2 : initialChunk 5 2 2 = 93026413 := by
  decide

theorem residual_chunk_5_2_3 : initialChunk 5 2 3 = 384173362 := by
  decide

theorem residual_chunk_5_2_4 : initialChunk 5 2 4 = 90492615 := by
  decide

theorem residual_chunk_5_2_5 : initialChunk 5 2 5 = 172264182 := by
  decide

theorem residual_chunk_5_2_6 : initialChunk 5 2 6 = 319305802 := by
  decide

theorem residual_chunk_5_2_7 : initialChunk 5 2 7 = 170136576 := by
  decide

theorem residual_chunk_5_2_8 : initialChunk 5 2 8 = 344233234 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_2_0 : initialPart 5 2 0 = 1890850793 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((0 : Fin 4), (0 : Fin 9)) = (0 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (1 : Fin 9)) = (1 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (2 : Fin 9)) = (2 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (3 : Fin 9)) = (3 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (4 : Fin 9)) = (4 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (5 : Fin 9)) = (5 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (6 : Fin 9)) = (6 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (7 : Fin 9)) = (7 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (8 : Fin 9)) = (8 : Fin 36) by decide]
  rw [residual_chunk_5_2_0, residual_chunk_5_2_1, residual_chunk_5_2_2, residual_chunk_5_2_3, residual_chunk_5_2_4, residual_chunk_5_2_5, residual_chunk_5_2_6, residual_chunk_5_2_7, residual_chunk_5_2_8]

end LiteralP13HodgeCertificate
end GroupApproximation

