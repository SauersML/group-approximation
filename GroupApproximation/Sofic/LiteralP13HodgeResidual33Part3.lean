import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (3, 3). -/

theorem residual_chunk_3_3_27 : initialChunk 3 3 27 = 227686714 := by
  decide

theorem residual_chunk_3_3_28 : initialChunk 3 3 28 = 219912663 := by
  decide

theorem residual_chunk_3_3_29 : initialChunk 3 3 29 = 354811377 := by
  decide

theorem residual_chunk_3_3_30 : initialChunk 3 3 30 = 180422800 := by
  decide

theorem residual_chunk_3_3_31 : initialChunk 3 3 31 = 120092464 := by
  decide

theorem residual_chunk_3_3_32 : initialChunk 3 3 32 = 165578772 := by
  decide

theorem residual_chunk_3_3_33 : initialChunk 3 3 33 = 120695415 := by
  decide

theorem residual_chunk_3_3_34 : initialChunk 3 3 34 = 65047509 := by
  decide

theorem residual_chunk_3_3_35 : initialChunk 3 3 35 = 69144868 := by
  decide

theorem residual_chunk_3_3_36 : finalChunk 3 3 = 69150489 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_3_3 : initialPart 3 3 3 + finalChunk 3 3 = 1592543071 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((3 : Fin 4), (0 : Fin 9)) = (27 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (1 : Fin 9)) = (28 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (2 : Fin 9)) = (29 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (3 : Fin 9)) = (30 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (4 : Fin 9)) = (31 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (5 : Fin 9)) = (32 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (6 : Fin 9)) = (33 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (7 : Fin 9)) = (34 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (8 : Fin 9)) = (35 : Fin 36) by decide]
  rw [residual_chunk_3_3_27, residual_chunk_3_3_28, residual_chunk_3_3_29, residual_chunk_3_3_30, residual_chunk_3_3_31, residual_chunk_3_3_32, residual_chunk_3_3_33, residual_chunk_3_3_34, residual_chunk_3_3_35, residual_chunk_3_3_36]

end LiteralP13HodgeCertificate
end GroupApproximation
