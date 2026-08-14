import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (2, 2). -/

theorem residual_chunk_2_2_27 : initialChunk 2 2 27 = 281455569 := by
  decide

theorem residual_chunk_2_2_28 : initialChunk 2 2 28 = 232407945 := by
  decide

theorem residual_chunk_2_2_29 : initialChunk 2 2 29 = 181101385 := by
  decide

theorem residual_chunk_2_2_30 : initialChunk 2 2 30 = 159782569 := by
  decide

theorem residual_chunk_2_2_31 : initialChunk 2 2 31 = 107745005 := by
  decide

theorem residual_chunk_2_2_32 : initialChunk 2 2 32 = 139280217 := by
  decide

theorem residual_chunk_2_2_33 : initialChunk 2 2 33 = 383065664 := by
  decide

theorem residual_chunk_2_2_34 : initialChunk 2 2 34 = 145289743 := by
  decide

theorem residual_chunk_2_2_35 : initialChunk 2 2 35 = 234863801 := by
  decide

theorem residual_chunk_2_2_36 : finalChunk 2 2 = 145289968 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_2_3 : initialPart 2 2 3 + finalChunk 2 2 = 2010281866 := by
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
  rw [residual_chunk_2_2_27, residual_chunk_2_2_28, residual_chunk_2_2_29, residual_chunk_2_2_30, residual_chunk_2_2_31, residual_chunk_2_2_32, residual_chunk_2_2_33, residual_chunk_2_2_34, residual_chunk_2_2_35, residual_chunk_2_2_36]

end LiteralP13HodgeCertificate
end GroupApproximation
