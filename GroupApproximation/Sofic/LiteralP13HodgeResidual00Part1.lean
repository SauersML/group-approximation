import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (0, 0). -/

theorem residual_chunk_0_0_9 : initialChunk 0 0 9 = 425318460 := by
  decide

theorem residual_chunk_0_0_10 : initialChunk 0 0 10 = 356119725 := by
  decide

theorem residual_chunk_0_0_11 : initialChunk 0 0 11 = 164702686 := by
  decide

theorem residual_chunk_0_0_12 : initialChunk 0 0 12 = 500757898 := by
  decide

theorem residual_chunk_0_0_13 : initialChunk 0 0 13 = 241977432 := by
  decide

theorem residual_chunk_0_0_14 : initialChunk 0 0 14 = 336177331 := by
  decide

theorem residual_chunk_0_0_15 : initialChunk 0 0 15 = 299460875 := by
  decide

theorem residual_chunk_0_0_16 : initialChunk 0 0 16 = 283698506 := by
  decide

theorem residual_chunk_0_0_17 : initialChunk 0 0 17 = 413968582 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_0_1 : initialPart 0 0 1 = 3022181495 := by
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
  rw [residual_chunk_0_0_9, residual_chunk_0_0_10, residual_chunk_0_0_11, residual_chunk_0_0_12, residual_chunk_0_0_13, residual_chunk_0_0_14, residual_chunk_0_0_15, residual_chunk_0_0_16, residual_chunk_0_0_17]

end LiteralP13HodgeCertificate
end GroupApproximation
