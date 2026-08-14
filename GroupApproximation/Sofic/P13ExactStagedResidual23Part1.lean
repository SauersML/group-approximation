import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (2, 3). -/

theorem residual_chunk_2_3_9 : initialChunk 2 3 9 = 217719880 := by
  decide

theorem residual_chunk_2_3_10 : initialChunk 2 3 10 = 115635826 := by
  decide

theorem residual_chunk_2_3_11 : initialChunk 2 3 11 = 64813993 := by
  decide

theorem residual_chunk_2_3_12 : initialChunk 2 3 12 = 283480893 := by
  decide

theorem residual_chunk_2_3_13 : initialChunk 2 3 13 = 68175167 := by
  decide

theorem residual_chunk_2_3_14 : initialChunk 2 3 14 = 119284973 := by
  decide

theorem residual_chunk_2_3_15 : initialChunk 2 3 15 = 129895751 := by
  decide

theorem residual_chunk_2_3_16 : initialChunk 2 3 16 = 177865814 := by
  decide

theorem residual_chunk_2_3_17 : initialChunk 2 3 17 = 263653971 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_3_1 : initialPart 2 3 1 = 1440526268 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((1 : Fin 4), (0 : Fin 9)) = (9 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (1 : Fin 9)) = (10 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (2 : Fin 9)) = (11 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (3 : Fin 9)) = (12 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (4 : Fin 9)) = (13 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (5 : Fin 9)) = (14 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (6 : Fin 9)) = (15 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (7 : Fin 9)) = (16 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (8 : Fin 9)) = (17 : Fin 36) by decide]
  rw [residual_chunk_2_3_9, residual_chunk_2_3_10, residual_chunk_2_3_11, residual_chunk_2_3_12, residual_chunk_2_3_13, residual_chunk_2_3_14, residual_chunk_2_3_15, residual_chunk_2_3_16, residual_chunk_2_3_17]

end LiteralP13HodgeCertificate
end GroupApproximation

