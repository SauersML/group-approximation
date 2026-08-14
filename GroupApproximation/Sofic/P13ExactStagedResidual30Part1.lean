import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (3, 0). -/

theorem residual_chunk_3_0_9 : initialChunk 3 0 9 = 337195967 := by
  decide

theorem residual_chunk_3_0_10 : initialChunk 3 0 10 = 196168820 := by
  decide

theorem residual_chunk_3_0_11 : initialChunk 3 0 11 = 180263603 := by
  decide

theorem residual_chunk_3_0_12 : initialChunk 3 0 12 = 547841255 := by
  decide

theorem residual_chunk_3_0_13 : initialChunk 3 0 13 = 318017808 := by
  decide

theorem residual_chunk_3_0_14 : initialChunk 3 0 14 = 408181518 := by
  decide

theorem residual_chunk_3_0_15 : initialChunk 3 0 15 = 201332737 := by
  decide

theorem residual_chunk_3_0_16 : initialChunk 3 0 16 = 465498090 := by
  decide

theorem residual_chunk_3_0_17 : initialChunk 3 0 17 = 493262010 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_0_1 : initialPart 3 0 1 = 3147761808 := by
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
  rw [residual_chunk_3_0_9, residual_chunk_3_0_10, residual_chunk_3_0_11, residual_chunk_3_0_12, residual_chunk_3_0_13, residual_chunk_3_0_14, residual_chunk_3_0_15, residual_chunk_3_0_16, residual_chunk_3_0_17]

end LiteralP13HodgeCertificate
end GroupApproximation

