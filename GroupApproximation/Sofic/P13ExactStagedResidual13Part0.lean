import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (1, 3). -/

theorem residual_chunk_1_3_0 : initialChunk 1 3 0 = 83628076 := by
  decide

theorem residual_chunk_1_3_1 : initialChunk 1 3 1 = 158352336 := by
  decide

theorem residual_chunk_1_3_2 : initialChunk 1 3 2 = 184374268 := by
  decide

theorem residual_chunk_1_3_3 : initialChunk 1 3 3 = 196273022 := by
  decide

theorem residual_chunk_1_3_4 : initialChunk 1 3 4 = 155557166 := by
  decide

theorem residual_chunk_1_3_5 : initialChunk 1 3 5 = 166499966 := by
  decide

theorem residual_chunk_1_3_6 : initialChunk 1 3 6 = 108650158 := by
  decide

theorem residual_chunk_1_3_7 : initialChunk 1 3 7 = 59820522 := by
  decide

theorem residual_chunk_1_3_8 : initialChunk 1 3 8 = 109534192 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_3_0 : initialPart 1 3 0 = 1222689706 := by
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
  rw [residual_chunk_1_3_0, residual_chunk_1_3_1, residual_chunk_1_3_2, residual_chunk_1_3_3, residual_chunk_1_3_4, residual_chunk_1_3_5, residual_chunk_1_3_6, residual_chunk_1_3_7, residual_chunk_1_3_8]

end LiteralP13HodgeCertificate
end GroupApproximation

