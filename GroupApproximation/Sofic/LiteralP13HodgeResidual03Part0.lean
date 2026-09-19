import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (0, 3). -/

theorem residual_chunk_0_3_0 : initialChunk 0 3 0 = 327941016 := by
  decide

theorem residual_chunk_0_3_1 : initialChunk 0 3 1 = 297661602 := by
  decide

theorem residual_chunk_0_3_2 : initialChunk 0 3 2 = 155870006 := by
  decide

theorem residual_chunk_0_3_3 : initialChunk 0 3 3 = 505304306 := by
  decide

theorem residual_chunk_0_3_4 : initialChunk 0 3 4 = 246752542 := by
  decide

theorem residual_chunk_0_3_5 : initialChunk 0 3 5 = 285538031 := by
  decide

theorem residual_chunk_0_3_6 : initialChunk 0 3 6 = 128826140 := by
  decide

theorem residual_chunk_0_3_7 : initialChunk 0 3 7 = 158390225 := by
  decide

theorem residual_chunk_0_3_8 : initialChunk 0 3 8 = 159386154 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_3_0 : initialPart 0 3 0 = 2265670022 := by
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
  rw [residual_chunk_0_3_0, residual_chunk_0_3_1, residual_chunk_0_3_2, residual_chunk_0_3_3, residual_chunk_0_3_4, residual_chunk_0_3_5, residual_chunk_0_3_6, residual_chunk_0_3_7, residual_chunk_0_3_8]

end LiteralP13HodgeCertificate
end GroupApproximation
