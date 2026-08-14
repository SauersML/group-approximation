import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (1, 1). -/

theorem residual_chunk_1_1_0 : initialChunk 1 1 0 = 144026588 := by
  decide

theorem residual_chunk_1_1_1 : initialChunk 1 1 1 = 199176131 := by
  decide

theorem residual_chunk_1_1_2 : initialChunk 1 1 2 = 77958473 := by
  decide

theorem residual_chunk_1_1_3 : initialChunk 1 1 3 = 343376639 := by
  decide

theorem residual_chunk_1_1_4 : initialChunk 1 1 4 = 137079977 := by
  decide

theorem residual_chunk_1_1_5 : initialChunk 1 1 5 = 127361326 := by
  decide

theorem residual_chunk_1_1_6 : initialChunk 1 1 6 = 86334501 := by
  decide

theorem residual_chunk_1_1_7 : initialChunk 1 1 7 = 111821575 := by
  decide

theorem residual_chunk_1_1_8 : initialChunk 1 1 8 = 92243031 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_1_0 : initialPart 1 1 0 = 1319378241 := by
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
  rw [residual_chunk_1_1_0, residual_chunk_1_1_1, residual_chunk_1_1_2, residual_chunk_1_1_3, residual_chunk_1_1_4, residual_chunk_1_1_5, residual_chunk_1_1_6, residual_chunk_1_1_7, residual_chunk_1_1_8]

end LiteralP13HodgeCertificate
end GroupApproximation
