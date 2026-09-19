import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (2, 0). -/

theorem residual_chunk_2_0_9 : initialChunk 2 0 9 = 194721147 := by
  decide

theorem residual_chunk_2_0_10 : initialChunk 2 0 10 = 137775976 := by
  decide

theorem residual_chunk_2_0_11 : initialChunk 2 0 11 = 202109901 := by
  decide

theorem residual_chunk_2_0_12 : initialChunk 2 0 12 = 313211694 := by
  decide

theorem residual_chunk_2_0_13 : initialChunk 2 0 13 = 386434503 := by
  decide

theorem residual_chunk_2_0_14 : initialChunk 2 0 14 = 325877676 := by
  decide

theorem residual_chunk_2_0_15 : initialChunk 2 0 15 = 285861236 := by
  decide

theorem residual_chunk_2_0_16 : initialChunk 2 0 16 = 190592574 := by
  decide

theorem residual_chunk_2_0_17 : initialChunk 2 0 17 = 336799138 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_0_1 : initialPart 2 0 1 = 2373383845 := by
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
  rw [residual_chunk_2_0_9, residual_chunk_2_0_10, residual_chunk_2_0_11, residual_chunk_2_0_12, residual_chunk_2_0_13, residual_chunk_2_0_14, residual_chunk_2_0_15, residual_chunk_2_0_16, residual_chunk_2_0_17]

end LiteralP13HodgeCertificate
end GroupApproximation
