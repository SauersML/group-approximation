import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (2, 1). -/

theorem residual_chunk_2_1_0 : initialChunk 2 1 0 = 315180829 := by
  decide

theorem residual_chunk_2_1_1 : initialChunk 2 1 1 = 189339271 := by
  decide

theorem residual_chunk_2_1_2 : initialChunk 2 1 2 = 272945360 := by
  decide

theorem residual_chunk_2_1_3 : initialChunk 2 1 3 = 121864196 := by
  decide

theorem residual_chunk_2_1_4 : initialChunk 2 1 4 = 142290017 := by
  decide

theorem residual_chunk_2_1_5 : initialChunk 2 1 5 = 165967864 := by
  decide

theorem residual_chunk_2_1_6 : initialChunk 2 1 6 = 183171948 := by
  decide

theorem residual_chunk_2_1_7 : initialChunk 2 1 7 = 177656444 := by
  decide

theorem residual_chunk_2_1_8 : initialChunk 2 1 8 = 188818527 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_1_0 : initialPart 2 1 0 = 1757234456 := by
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
  rw [residual_chunk_2_1_0, residual_chunk_2_1_1, residual_chunk_2_1_2, residual_chunk_2_1_3, residual_chunk_2_1_4, residual_chunk_2_1_5, residual_chunk_2_1_6, residual_chunk_2_1_7, residual_chunk_2_1_8]

end LiteralP13HodgeCertificate
end GroupApproximation
