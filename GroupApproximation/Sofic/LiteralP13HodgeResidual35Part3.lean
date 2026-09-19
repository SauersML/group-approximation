import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (3, 5). -/

theorem residual_chunk_3_5_27 : initialChunk 3 5 27 = 304840540 := by
  decide

theorem residual_chunk_3_5_28 : initialChunk 3 5 28 = 92997787 := by
  decide

theorem residual_chunk_3_5_29 : initialChunk 3 5 29 = 208438334 := by
  decide

theorem residual_chunk_3_5_30 : initialChunk 3 5 30 = 197783748 := by
  decide

theorem residual_chunk_3_5_31 : initialChunk 3 5 31 = 133957941 := by
  decide

theorem residual_chunk_3_5_32 : initialChunk 3 5 32 = 199628442 := by
  decide

theorem residual_chunk_3_5_33 : initialChunk 3 5 33 = 210186067 := by
  decide

theorem residual_chunk_3_5_34 : initialChunk 3 5 34 = 172960870 := by
  decide

theorem residual_chunk_3_5_35 : initialChunk 3 5 35 = 99697515 := by
  decide

theorem residual_chunk_3_5_36 : finalChunk 3 5 = 145771692 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_5_3 : initialPart 3 5 3 + finalChunk 3 5 = 1766262936 := by
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
  rw [residual_chunk_3_5_27, residual_chunk_3_5_28, residual_chunk_3_5_29, residual_chunk_3_5_30, residual_chunk_3_5_31, residual_chunk_3_5_32, residual_chunk_3_5_33, residual_chunk_3_5_34, residual_chunk_3_5_35, residual_chunk_3_5_36]

end LiteralP13HodgeCertificate
end GroupApproximation
