import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (4, 0). -/

theorem residual_chunk_4_0_9 : initialChunk 4 0 9 = 495910437 := by
  decide

theorem residual_chunk_4_0_10 : initialChunk 4 0 10 = 170673769 := by
  decide

theorem residual_chunk_4_0_11 : initialChunk 4 0 11 = 157028904 := by
  decide

theorem residual_chunk_4_0_12 : initialChunk 4 0 12 = 457388425 := by
  decide

theorem residual_chunk_4_0_13 : initialChunk 4 0 13 = 182193402 := by
  decide

theorem residual_chunk_4_0_14 : initialChunk 4 0 14 = 280659064 := by
  decide

theorem residual_chunk_4_0_15 : initialChunk 4 0 15 = 152909733 := by
  decide

theorem residual_chunk_4_0_16 : initialChunk 4 0 16 = 371309934 := by
  decide

theorem residual_chunk_4_0_17 : initialChunk 4 0 17 = 185431393 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_0_1 : initialPart 4 0 1 = 2453505061 := by
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
  rw [residual_chunk_4_0_9, residual_chunk_4_0_10, residual_chunk_4_0_11, residual_chunk_4_0_12, residual_chunk_4_0_13, residual_chunk_4_0_14, residual_chunk_4_0_15, residual_chunk_4_0_16, residual_chunk_4_0_17]

end LiteralP13HodgeCertificate
end GroupApproximation

