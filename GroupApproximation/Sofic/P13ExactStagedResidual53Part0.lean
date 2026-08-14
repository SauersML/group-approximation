import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (5, 3). -/

theorem residual_chunk_5_3_0 : initialChunk 5 3 0 = 221601658 := by
  decide

theorem residual_chunk_5_3_1 : initialChunk 5 3 1 = 211246128 := by
  decide

theorem residual_chunk_5_3_2 : initialChunk 5 3 2 = 176194123 := by
  decide

theorem residual_chunk_5_3_3 : initialChunk 5 3 3 = 354503416 := by
  decide

theorem residual_chunk_5_3_4 : initialChunk 5 3 4 = 78800323 := by
  decide

theorem residual_chunk_5_3_5 : initialChunk 5 3 5 = 229013008 := by
  decide

theorem residual_chunk_5_3_6 : initialChunk 5 3 6 = 97623137 := by
  decide

theorem residual_chunk_5_3_7 : initialChunk 5 3 7 = 96829612 := by
  decide

theorem residual_chunk_5_3_8 : initialChunk 5 3 8 = 176507248 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_3_0 : initialPart 5 3 0 = 1642318653 := by
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
  rw [residual_chunk_5_3_0, residual_chunk_5_3_1, residual_chunk_5_3_2, residual_chunk_5_3_3, residual_chunk_5_3_4, residual_chunk_5_3_5, residual_chunk_5_3_6, residual_chunk_5_3_7, residual_chunk_5_3_8]

end LiteralP13HodgeCertificate
end GroupApproximation

