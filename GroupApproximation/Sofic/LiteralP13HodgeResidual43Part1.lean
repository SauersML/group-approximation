import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (4, 3). -/

theorem residual_chunk_4_3_9 : initialChunk 4 3 9 = 308473369 := by
  decide

theorem residual_chunk_4_3_10 : initialChunk 4 3 10 = 188145943 := by
  decide

theorem residual_chunk_4_3_11 : initialChunk 4 3 11 = 81399163 := by
  decide

theorem residual_chunk_4_3_12 : initialChunk 4 3 12 = 118577447 := by
  decide

theorem residual_chunk_4_3_13 : initialChunk 4 3 13 = 35738905 := by
  decide

theorem residual_chunk_4_3_14 : initialChunk 4 3 14 = 86182232 := by
  decide

theorem residual_chunk_4_3_15 : initialChunk 4 3 15 = 82356239 := by
  decide

theorem residual_chunk_4_3_16 : initialChunk 4 3 16 = 99030882 := by
  decide

theorem residual_chunk_4_3_17 : initialChunk 4 3 17 = 128036902 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_3_1 : initialPart 4 3 1 = 1127941082 := by
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
  rw [residual_chunk_4_3_9, residual_chunk_4_3_10, residual_chunk_4_3_11, residual_chunk_4_3_12, residual_chunk_4_3_13, residual_chunk_4_3_14, residual_chunk_4_3_15, residual_chunk_4_3_16, residual_chunk_4_3_17]

end LiteralP13HodgeCertificate
end GroupApproximation
