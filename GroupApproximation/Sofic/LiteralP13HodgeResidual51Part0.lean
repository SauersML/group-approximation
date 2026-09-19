import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (5, 1). -/

theorem residual_chunk_5_1_0 : initialChunk 5 1 0 = 192516353 := by
  decide

theorem residual_chunk_5_1_1 : initialChunk 5 1 1 = 155285425 := by
  decide

theorem residual_chunk_5_1_2 : initialChunk 5 1 2 = 138140841 := by
  decide

theorem residual_chunk_5_1_3 : initialChunk 5 1 3 = 143303465 := by
  decide

theorem residual_chunk_5_1_4 : initialChunk 5 1 4 = 120351172 := by
  decide

theorem residual_chunk_5_1_5 : initialChunk 5 1 5 = 183826858 := by
  decide

theorem residual_chunk_5_1_6 : initialChunk 5 1 6 = 94522034 := by
  decide

theorem residual_chunk_5_1_7 : initialChunk 5 1 7 = 110588873 := by
  decide

theorem residual_chunk_5_1_8 : initialChunk 5 1 8 = 245334553 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_1_0 : initialPart 5 1 0 = 1383869574 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((0 : Fin 4), (0 : Fin 9)) = (0 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (1 : Fin 9)) = (1 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (2 : Fin 9)) = (2 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (3 : Fin 9)) = (3 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (4 : Fin 9)) = (4 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (5 : Fin 9)) = (5 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (6 : Fin 9)) = (6 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (7 : Fin 9)) = (7 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (8 : Fin 9)) = (8 : Fin 36) by decide]
  rw [residual_chunk_5_1_0, residual_chunk_5_1_1, residual_chunk_5_1_2, residual_chunk_5_1_3, residual_chunk_5_1_4, residual_chunk_5_1_5, residual_chunk_5_1_6, residual_chunk_5_1_7, residual_chunk_5_1_8]

end LiteralP13HodgeCertificate
end GroupApproximation
