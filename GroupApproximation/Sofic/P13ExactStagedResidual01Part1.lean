import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (0, 1). -/

theorem residual_chunk_0_1_9 : initialChunk 0 1 9 = 366295743 := by
  decide

theorem residual_chunk_0_1_10 : initialChunk 0 1 10 = 175313683 := by
  decide

theorem residual_chunk_0_1_11 : initialChunk 0 1 11 = 133934563 := by
  decide

theorem residual_chunk_0_1_12 : initialChunk 0 1 12 = 288775169 := by
  decide

theorem residual_chunk_0_1_13 : initialChunk 0 1 13 = 142721433 := by
  decide

theorem residual_chunk_0_1_14 : initialChunk 0 1 14 = 160988991 := by
  decide

theorem residual_chunk_0_1_15 : initialChunk 0 1 15 = 245144881 := by
  decide

theorem residual_chunk_0_1_16 : initialChunk 0 1 16 = 103373620 := by
  decide

theorem residual_chunk_0_1_17 : initialChunk 0 1 17 = 296087283 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_1_1 : initialPart 0 1 1 = 1912635366 := by
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
  rw [residual_chunk_0_1_9, residual_chunk_0_1_10, residual_chunk_0_1_11, residual_chunk_0_1_12, residual_chunk_0_1_13, residual_chunk_0_1_14, residual_chunk_0_1_15, residual_chunk_0_1_16, residual_chunk_0_1_17]

end LiteralP13HodgeCertificate
end GroupApproximation

