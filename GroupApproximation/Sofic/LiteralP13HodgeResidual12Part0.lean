import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (1, 2). -/

theorem residual_chunk_1_2_0 : initialChunk 1 2 0 = 150163000 := by
  decide

theorem residual_chunk_1_2_1 : initialChunk 1 2 1 = 97731644 := by
  decide

theorem residual_chunk_1_2_2 : initialChunk 1 2 2 = 107832318 := by
  decide

theorem residual_chunk_1_2_3 : initialChunk 1 2 3 = 182076999 := by
  decide

theorem residual_chunk_1_2_4 : initialChunk 1 2 4 = 156181676 := by
  decide

theorem residual_chunk_1_2_5 : initialChunk 1 2 5 = 247460293 := by
  decide

theorem residual_chunk_1_2_6 : initialChunk 1 2 6 = 302964656 := by
  decide

theorem residual_chunk_1_2_7 : initialChunk 1 2 7 = 174162025 := by
  decide

theorem residual_chunk_1_2_8 : initialChunk 1 2 8 = 240752762 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_2_0 : initialPart 1 2 0 = 1659325373 := by
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
  rw [residual_chunk_1_2_0, residual_chunk_1_2_1, residual_chunk_1_2_2, residual_chunk_1_2_3, residual_chunk_1_2_4, residual_chunk_1_2_5, residual_chunk_1_2_6, residual_chunk_1_2_7, residual_chunk_1_2_8]

end LiteralP13HodgeCertificate
end GroupApproximation
