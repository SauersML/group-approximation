import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (1, 0). -/

theorem residual_chunk_1_0_9 : initialChunk 1 0 9 = 319506856 := by
  decide

theorem residual_chunk_1_0_10 : initialChunk 1 0 10 = 139073461 := by
  decide

theorem residual_chunk_1_0_11 : initialChunk 1 0 11 = 255016814 := by
  decide

theorem residual_chunk_1_0_12 : initialChunk 1 0 12 = 272375377 := by
  decide

theorem residual_chunk_1_0_13 : initialChunk 1 0 13 = 406578192 := by
  decide

theorem residual_chunk_1_0_14 : initialChunk 1 0 14 = 300856321 := by
  decide

theorem residual_chunk_1_0_15 : initialChunk 1 0 15 = 93963119 := by
  decide

theorem residual_chunk_1_0_16 : initialChunk 1 0 16 = 322772103 := by
  decide

theorem residual_chunk_1_0_17 : initialChunk 1 0 17 = 439287646 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_0_1 : initialPart 1 0 1 = 2549429889 := by
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
  rw [residual_chunk_1_0_9, residual_chunk_1_0_10, residual_chunk_1_0_11, residual_chunk_1_0_12, residual_chunk_1_0_13, residual_chunk_1_0_14, residual_chunk_1_0_15, residual_chunk_1_0_16, residual_chunk_1_0_17]

end LiteralP13HodgeCertificate
end GroupApproximation
