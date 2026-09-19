import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (4, 4). -/

theorem residual_chunk_4_4_9 : initialChunk 4 4 9 = 294373690 := by
  decide

theorem residual_chunk_4_4_10 : initialChunk 4 4 10 = 146378763 := by
  decide

theorem residual_chunk_4_4_11 : initialChunk 4 4 11 = 137866914 := by
  decide

theorem residual_chunk_4_4_12 : initialChunk 4 4 12 = 270286474 := by
  decide

theorem residual_chunk_4_4_13 : initialChunk 4 4 13 = 93711733 := by
  decide

theorem residual_chunk_4_4_14 : initialChunk 4 4 14 = 112119005 := by
  decide

theorem residual_chunk_4_4_15 : initialChunk 4 4 15 = 89377687 := by
  decide

theorem residual_chunk_4_4_16 : initialChunk 4 4 16 = 195934448 := by
  decide

theorem residual_chunk_4_4_17 : initialChunk 4 4 17 = 215604961 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_4_1 : initialPart 4 4 1 = 1555653675 := by
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
  rw [residual_chunk_4_4_9, residual_chunk_4_4_10, residual_chunk_4_4_11, residual_chunk_4_4_12, residual_chunk_4_4_13, residual_chunk_4_4_14, residual_chunk_4_4_15, residual_chunk_4_4_16, residual_chunk_4_4_17]

end LiteralP13HodgeCertificate
end GroupApproximation
