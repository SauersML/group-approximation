import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (5, 5). -/

theorem residual_chunk_5_5_27 : initialChunk 5 5 27 = 199490336 := by
  decide

theorem residual_chunk_5_5_28 : initialChunk 5 5 28 = 143363943 := by
  decide

theorem residual_chunk_5_5_29 : initialChunk 5 5 29 = 217912533 := by
  decide

theorem residual_chunk_5_5_30 : initialChunk 5 5 30 = 127253297 := by
  decide

theorem residual_chunk_5_5_31 : initialChunk 5 5 31 = 114923136 := by
  decide

theorem residual_chunk_5_5_32 : initialChunk 5 5 32 = 211730918 := by
  decide

theorem residual_chunk_5_5_33 : initialChunk 5 5 33 = 351908883 := by
  decide

theorem residual_chunk_5_5_34 : initialChunk 5 5 34 = 154941081 := by
  decide

theorem residual_chunk_5_5_35 : initialChunk 5 5 35 = 88472766 := by
  decide

theorem residual_chunk_5_5_36 : finalChunk 5 5 = 61221881 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_5_3 : initialPart 5 5 3 + finalChunk 5 5 = 1671218774 := by
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
  rw [residual_chunk_5_5_27, residual_chunk_5_5_28, residual_chunk_5_5_29, residual_chunk_5_5_30, residual_chunk_5_5_31, residual_chunk_5_5_32, residual_chunk_5_5_33, residual_chunk_5_5_34, residual_chunk_5_5_35, residual_chunk_5_5_36]

end LiteralP13HodgeCertificate
end GroupApproximation
