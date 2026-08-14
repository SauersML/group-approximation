import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (3, 2). -/

theorem residual_chunk_3_2_0 : initialChunk 3 2 0 = 105957020 := by
  decide

theorem residual_chunk_3_2_1 : initialChunk 3 2 1 = 208516020 := by
  decide

theorem residual_chunk_3_2_2 : initialChunk 3 2 2 = 95363483 := by
  decide

theorem residual_chunk_3_2_3 : initialChunk 3 2 3 = 298486942 := by
  decide

theorem residual_chunk_3_2_4 : initialChunk 3 2 4 = 147438617 := by
  decide

theorem residual_chunk_3_2_5 : initialChunk 3 2 5 = 359438412 := by
  decide

theorem residual_chunk_3_2_6 : initialChunk 3 2 6 = 261438210 := by
  decide

theorem residual_chunk_3_2_7 : initialChunk 3 2 7 = 204344131 := by
  decide

theorem residual_chunk_3_2_8 : initialChunk 3 2 8 = 369484924 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_2_0 : initialPart 3 2 0 = 2050467759 := by
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
  rw [residual_chunk_3_2_0, residual_chunk_3_2_1, residual_chunk_3_2_2, residual_chunk_3_2_3, residual_chunk_3_2_4, residual_chunk_3_2_5, residual_chunk_3_2_6, residual_chunk_3_2_7, residual_chunk_3_2_8]

end LiteralP13HodgeCertificate
end GroupApproximation
