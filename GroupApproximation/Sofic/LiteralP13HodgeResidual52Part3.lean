import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (5, 2). -/

theorem residual_chunk_5_2_27 : initialChunk 5 2 27 = 157417813 := by
  decide

theorem residual_chunk_5_2_28 : initialChunk 5 2 28 = 149926409 := by
  decide

theorem residual_chunk_5_2_29 : initialChunk 5 2 29 = 145657489 := by
  decide

theorem residual_chunk_5_2_30 : initialChunk 5 2 30 = 280223914 := by
  decide

theorem residual_chunk_5_2_31 : initialChunk 5 2 31 = 164222330 := by
  decide

theorem residual_chunk_5_2_32 : initialChunk 5 2 32 = 111982986 := by
  decide

theorem residual_chunk_5_2_33 : initialChunk 5 2 33 = 279290681 := by
  decide

theorem residual_chunk_5_2_34 : initialChunk 5 2 34 = 79656213 := by
  decide

theorem residual_chunk_5_2_35 : initialChunk 5 2 35 = 128896099 := by
  decide

theorem residual_chunk_5_2_36 : finalChunk 5 2 = 78331689 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_2_3 : initialPart 5 2 3 + finalChunk 5 2 = 1575605623 := by
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
  rw [residual_chunk_5_2_27, residual_chunk_5_2_28, residual_chunk_5_2_29, residual_chunk_5_2_30, residual_chunk_5_2_31, residual_chunk_5_2_32, residual_chunk_5_2_33, residual_chunk_5_2_34, residual_chunk_5_2_35, residual_chunk_5_2_36]

end LiteralP13HodgeCertificate
end GroupApproximation
