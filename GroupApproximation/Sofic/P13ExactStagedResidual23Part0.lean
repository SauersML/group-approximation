import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (2, 3). -/

theorem residual_chunk_2_3_0 : initialChunk 2 3 0 = 205579440 := by
  decide

theorem residual_chunk_2_3_1 : initialChunk 2 3 1 = 203155491 := by
  decide

theorem residual_chunk_2_3_2 : initialChunk 2 3 2 = 202816401 := by
  decide

theorem residual_chunk_2_3_3 : initialChunk 2 3 3 = 259039555 := by
  decide

theorem residual_chunk_2_3_4 : initialChunk 2 3 4 = 209997286 := by
  decide

theorem residual_chunk_2_3_5 : initialChunk 2 3 5 = 339610182 := by
  decide

theorem residual_chunk_2_3_6 : initialChunk 2 3 6 = 195057085 := by
  decide

theorem residual_chunk_2_3_7 : initialChunk 2 3 7 = 110471383 := by
  decide

theorem residual_chunk_2_3_8 : initialChunk 2 3 8 = 332904649 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_3_0 : initialPart 2 3 0 = 2058631472 := by
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
  rw [residual_chunk_2_3_0, residual_chunk_2_3_1, residual_chunk_2_3_2, residual_chunk_2_3_3, residual_chunk_2_3_4, residual_chunk_2_3_5, residual_chunk_2_3_6, residual_chunk_2_3_7, residual_chunk_2_3_8]

end LiteralP13HodgeCertificate
end GroupApproximation

