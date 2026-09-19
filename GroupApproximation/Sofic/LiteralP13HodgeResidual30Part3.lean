import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (3, 0). -/

theorem residual_chunk_3_0_27 : initialChunk 3 0 27 = 167813997 := by
  decide

theorem residual_chunk_3_0_28 : initialChunk 3 0 28 = 74431147 := by
  decide

theorem residual_chunk_3_0_29 : initialChunk 3 0 29 = 263106589 := by
  decide

theorem residual_chunk_3_0_30 : initialChunk 3 0 30 = 331264126 := by
  decide

theorem residual_chunk_3_0_31 : initialChunk 3 0 31 = 239755763 := by
  decide

theorem residual_chunk_3_0_32 : initialChunk 3 0 32 = 72932691 := by
  decide

theorem residual_chunk_3_0_33 : initialChunk 3 0 33 = 186243149 := by
  decide

theorem residual_chunk_3_0_34 : initialChunk 3 0 34 = 93361483 := by
  decide

theorem residual_chunk_3_0_35 : initialChunk 3 0 35 = 189543583 := by
  decide

theorem residual_chunk_3_0_36 : finalChunk 3 0 = 40968773 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_0_3 : initialPart 3 0 3 + finalChunk 3 0 = 1659421301 := by
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
  rw [residual_chunk_3_0_27, residual_chunk_3_0_28, residual_chunk_3_0_29, residual_chunk_3_0_30, residual_chunk_3_0_31, residual_chunk_3_0_32, residual_chunk_3_0_33, residual_chunk_3_0_34, residual_chunk_3_0_35, residual_chunk_3_0_36]

end LiteralP13HodgeCertificate
end GroupApproximation
