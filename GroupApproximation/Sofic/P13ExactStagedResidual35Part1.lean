import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (3, 5). -/

theorem residual_chunk_3_5_9 : initialChunk 3 5 9 = 147383964 := by
  decide

theorem residual_chunk_3_5_10 : initialChunk 3 5 10 = 194047980 := by
  decide

theorem residual_chunk_3_5_11 : initialChunk 3 5 11 = 121528635 := by
  decide

theorem residual_chunk_3_5_12 : initialChunk 3 5 12 = 300210707 := by
  decide

theorem residual_chunk_3_5_13 : initialChunk 3 5 13 = 160239740 := by
  decide

theorem residual_chunk_3_5_14 : initialChunk 3 5 14 = 125260703 := by
  decide

theorem residual_chunk_3_5_15 : initialChunk 3 5 15 = 196005047 := by
  decide

theorem residual_chunk_3_5_16 : initialChunk 3 5 16 = 107840914 := by
  decide

theorem residual_chunk_3_5_17 : initialChunk 3 5 17 = 237018125 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_5_1 : initialPart 3 5 1 = 1589535815 := by
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
  rw [residual_chunk_3_5_9, residual_chunk_3_5_10, residual_chunk_3_5_11, residual_chunk_3_5_12, residual_chunk_3_5_13, residual_chunk_3_5_14, residual_chunk_3_5_15, residual_chunk_3_5_16, residual_chunk_3_5_17]

end LiteralP13HodgeCertificate
end GroupApproximation

