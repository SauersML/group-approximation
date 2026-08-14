import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (5, 0). -/

theorem residual_chunk_5_0_9 : initialChunk 5 0 9 = 238008776 := by
  decide

theorem residual_chunk_5_0_10 : initialChunk 5 0 10 = 147810605 := by
  decide

theorem residual_chunk_5_0_11 : initialChunk 5 0 11 = 98231798 := by
  decide

theorem residual_chunk_5_0_12 : initialChunk 5 0 12 = 374787018 := by
  decide

theorem residual_chunk_5_0_13 : initialChunk 5 0 13 = 422391273 := by
  decide

theorem residual_chunk_5_0_14 : initialChunk 5 0 14 = 289706305 := by
  decide

theorem residual_chunk_5_0_15 : initialChunk 5 0 15 = 106662214 := by
  decide

theorem residual_chunk_5_0_16 : initialChunk 5 0 16 = 119360136 := by
  decide

theorem residual_chunk_5_0_17 : initialChunk 5 0 17 = 350340311 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_0_1 : initialPart 5 0 1 = 2147298436 := by
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
  rw [residual_chunk_5_0_9, residual_chunk_5_0_10, residual_chunk_5_0_11, residual_chunk_5_0_12, residual_chunk_5_0_13, residual_chunk_5_0_14, residual_chunk_5_0_15, residual_chunk_5_0_16, residual_chunk_5_0_17]

end LiteralP13HodgeCertificate
end GroupApproximation

