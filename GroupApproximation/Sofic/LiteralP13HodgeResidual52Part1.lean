import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (5, 2). -/

theorem residual_chunk_5_2_9 : initialChunk 5 2 9 = 187486945 := by
  decide

theorem residual_chunk_5_2_10 : initialChunk 5 2 10 = 170330298 := by
  decide

theorem residual_chunk_5_2_11 : initialChunk 5 2 11 = 189903052 := by
  decide

theorem residual_chunk_5_2_12 : initialChunk 5 2 12 = 197002571 := by
  decide

theorem residual_chunk_5_2_13 : initialChunk 5 2 13 = 400124210 := by
  decide

theorem residual_chunk_5_2_14 : initialChunk 5 2 14 = 254350310 := by
  decide

theorem residual_chunk_5_2_15 : initialChunk 5 2 15 = 198223858 := by
  decide

theorem residual_chunk_5_2_16 : initialChunk 5 2 16 = 162034112 := by
  decide

theorem residual_chunk_5_2_17 : initialChunk 5 2 17 = 427184872 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_2_1 : initialPart 5 2 1 = 2186640228 := by
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
  rw [residual_chunk_5_2_9, residual_chunk_5_2_10, residual_chunk_5_2_11, residual_chunk_5_2_12, residual_chunk_5_2_13, residual_chunk_5_2_14, residual_chunk_5_2_15, residual_chunk_5_2_16, residual_chunk_5_2_17]

end LiteralP13HodgeCertificate
end GroupApproximation
