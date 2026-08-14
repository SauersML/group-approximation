import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (3, 2). -/

theorem residual_chunk_3_2_27 : initialChunk 3 2 27 = 239819160 := by
  decide

theorem residual_chunk_3_2_28 : initialChunk 3 2 28 = 55198010 := by
  decide

theorem residual_chunk_3_2_29 : initialChunk 3 2 29 = 309742511 := by
  decide

theorem residual_chunk_3_2_30 : initialChunk 3 2 30 = 132493775 := by
  decide

theorem residual_chunk_3_2_31 : initialChunk 3 2 31 = 241633672 := by
  decide

theorem residual_chunk_3_2_32 : initialChunk 3 2 32 = 100090685 := by
  decide

theorem residual_chunk_3_2_33 : initialChunk 3 2 33 = 285901462 := by
  decide

theorem residual_chunk_3_2_34 : initialChunk 3 2 34 = 225759013 := by
  decide

theorem residual_chunk_3_2_35 : initialChunk 3 2 35 = 202609522 := by
  decide

theorem residual_chunk_3_2_36 : finalChunk 3 2 = 103178781 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_2_3 : initialPart 3 2 3 + finalChunk 3 2 = 1896426591 := by
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
  rw [residual_chunk_3_2_27, residual_chunk_3_2_28, residual_chunk_3_2_29, residual_chunk_3_2_30, residual_chunk_3_2_31, residual_chunk_3_2_32, residual_chunk_3_2_33, residual_chunk_3_2_34, residual_chunk_3_2_35, residual_chunk_3_2_36]

end LiteralP13HodgeCertificate
end GroupApproximation
