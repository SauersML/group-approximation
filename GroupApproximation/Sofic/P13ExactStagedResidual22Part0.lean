import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (2, 2). -/

theorem residual_chunk_2_2_0 : initialChunk 2 2 0 = 208118416 := by
  decide

theorem residual_chunk_2_2_1 : initialChunk 2 2 1 = 167486313 := by
  decide

theorem residual_chunk_2_2_2 : initialChunk 2 2 2 = 279610856 := by
  decide

theorem residual_chunk_2_2_3 : initialChunk 2 2 3 = 377369740 := by
  decide

theorem residual_chunk_2_2_4 : initialChunk 2 2 4 = 151734542 := by
  decide

theorem residual_chunk_2_2_5 : initialChunk 2 2 5 = 438067472 := by
  decide

theorem residual_chunk_2_2_6 : initialChunk 2 2 6 = 224873082 := by
  decide

theorem residual_chunk_2_2_7 : initialChunk 2 2 7 = 298344821 := by
  decide

theorem residual_chunk_2_2_8 : initialChunk 2 2 8 = 447600413 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_2_0 : initialPart 2 2 0 = 2593205655 := by
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
  rw [residual_chunk_2_2_0, residual_chunk_2_2_1, residual_chunk_2_2_2, residual_chunk_2_2_3, residual_chunk_2_2_4, residual_chunk_2_2_5, residual_chunk_2_2_6, residual_chunk_2_2_7, residual_chunk_2_2_8]

end LiteralP13HodgeCertificate
end GroupApproximation

