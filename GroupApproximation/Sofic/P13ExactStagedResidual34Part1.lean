import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (3, 4). -/

theorem residual_chunk_3_4_9 : initialChunk 3 4 9 = 115981649 := by
  decide

theorem residual_chunk_3_4_10 : initialChunk 3 4 10 = 144604361 := by
  decide

theorem residual_chunk_3_4_11 : initialChunk 3 4 11 = 258579664 := by
  decide

theorem residual_chunk_3_4_12 : initialChunk 3 4 12 = 307256724 := by
  decide

theorem residual_chunk_3_4_13 : initialChunk 3 4 13 = 108698197 := by
  decide

theorem residual_chunk_3_4_14 : initialChunk 3 4 14 = 98340029 := by
  decide

theorem residual_chunk_3_4_15 : initialChunk 3 4 15 = 64853739 := by
  decide

theorem residual_chunk_3_4_16 : initialChunk 3 4 16 = 250806774 := by
  decide

theorem residual_chunk_3_4_17 : initialChunk 3 4 17 = 35680047 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_4_1 : initialPart 3 4 1 = 1384801184 := by
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
  rw [residual_chunk_3_4_9, residual_chunk_3_4_10, residual_chunk_3_4_11, residual_chunk_3_4_12, residual_chunk_3_4_13, residual_chunk_3_4_14, residual_chunk_3_4_15, residual_chunk_3_4_16, residual_chunk_3_4_17]

end LiteralP13HodgeCertificate
end GroupApproximation

