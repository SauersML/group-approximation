import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (5, 1). -/

theorem residual_chunk_5_1_9 : initialChunk 5 1 9 = 190934352 := by
  decide

theorem residual_chunk_5_1_10 : initialChunk 5 1 10 = 119436053 := by
  decide

theorem residual_chunk_5_1_11 : initialChunk 5 1 11 = 128402954 := by
  decide

theorem residual_chunk_5_1_12 : initialChunk 5 1 12 = 164170852 := by
  decide

theorem residual_chunk_5_1_13 : initialChunk 5 1 13 = 110561569 := by
  decide

theorem residual_chunk_5_1_14 : initialChunk 5 1 14 = 110886803 := by
  decide

theorem residual_chunk_5_1_15 : initialChunk 5 1 15 = 124540534 := by
  decide

theorem residual_chunk_5_1_16 : initialChunk 5 1 16 = 110679805 := by
  decide

theorem residual_chunk_5_1_17 : initialChunk 5 1 17 = 374730230 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_1_1 : initialPart 5 1 1 = 1434343152 := by
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
  rw [residual_chunk_5_1_9, residual_chunk_5_1_10, residual_chunk_5_1_11, residual_chunk_5_1_12, residual_chunk_5_1_13, residual_chunk_5_1_14, residual_chunk_5_1_15, residual_chunk_5_1_16, residual_chunk_5_1_17]

end LiteralP13HodgeCertificate
end GroupApproximation
