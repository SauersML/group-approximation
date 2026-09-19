import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (4, 4). -/

theorem residual_chunk_4_4_27 : initialChunk 4 4 27 = 488080679 := by
  decide

theorem residual_chunk_4_4_28 : initialChunk 4 4 28 = 149050923 := by
  decide

theorem residual_chunk_4_4_29 : initialChunk 4 4 29 = 287180539 := by
  decide

theorem residual_chunk_4_4_30 : initialChunk 4 4 30 = 241016098 := by
  decide

theorem residual_chunk_4_4_31 : initialChunk 4 4 31 = 98657623 := by
  decide

theorem residual_chunk_4_4_32 : initialChunk 4 4 32 = 212014374 := by
  decide

theorem residual_chunk_4_4_33 : initialChunk 4 4 33 = 271115097 := by
  decide

theorem residual_chunk_4_4_34 : initialChunk 4 4 34 = 167551873 := by
  decide

theorem residual_chunk_4_4_35 : initialChunk 4 4 35 = 120984589 := by
  decide

theorem residual_chunk_4_4_36 : finalChunk 4 4 = 36559071 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_4_3 : initialPart 4 4 3 + finalChunk 4 4 = 2072210866 := by
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
  rw [residual_chunk_4_4_27, residual_chunk_4_4_28, residual_chunk_4_4_29, residual_chunk_4_4_30, residual_chunk_4_4_31, residual_chunk_4_4_32, residual_chunk_4_4_33, residual_chunk_4_4_34, residual_chunk_4_4_35, residual_chunk_4_4_36]

end LiteralP13HodgeCertificate
end GroupApproximation
