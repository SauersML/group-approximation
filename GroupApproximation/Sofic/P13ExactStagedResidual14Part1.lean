import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (1, 4). -/

theorem residual_chunk_1_4_9 : initialChunk 1 4 9 = 131363680 := by
  decide

theorem residual_chunk_1_4_10 : initialChunk 1 4 10 = 187610698 := by
  decide

theorem residual_chunk_1_4_11 : initialChunk 1 4 11 = 150735069 := by
  decide

theorem residual_chunk_1_4_12 : initialChunk 1 4 12 = 163974694 := by
  decide

theorem residual_chunk_1_4_13 : initialChunk 1 4 13 = 68379702 := by
  decide

theorem residual_chunk_1_4_14 : initialChunk 1 4 14 = 69777407 := by
  decide

theorem residual_chunk_1_4_15 : initialChunk 1 4 15 = 161588543 := by
  decide

theorem residual_chunk_1_4_16 : initialChunk 1 4 16 = 337639236 := by
  decide

theorem residual_chunk_1_4_17 : initialChunk 1 4 17 = 189281365 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_4_1 : initialPart 1 4 1 = 1460350394 := by
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
  rw [residual_chunk_1_4_9, residual_chunk_1_4_10, residual_chunk_1_4_11, residual_chunk_1_4_12, residual_chunk_1_4_13, residual_chunk_1_4_14, residual_chunk_1_4_15, residual_chunk_1_4_16, residual_chunk_1_4_17]

end LiteralP13HodgeCertificate
end GroupApproximation

