import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (5, 4). -/

theorem residual_chunk_5_4_27 : initialChunk 5 4 27 = 214275699 := by
  decide

theorem residual_chunk_5_4_28 : initialChunk 5 4 28 = 151025248 := by
  decide

theorem residual_chunk_5_4_29 : initialChunk 5 4 29 = 123257655 := by
  decide

theorem residual_chunk_5_4_30 : initialChunk 5 4 30 = 264920376 := by
  decide

theorem residual_chunk_5_4_31 : initialChunk 5 4 31 = 117399283 := by
  decide

theorem residual_chunk_5_4_32 : initialChunk 5 4 32 = 277659501 := by
  decide

theorem residual_chunk_5_4_33 : initialChunk 5 4 33 = 117715760 := by
  decide

theorem residual_chunk_5_4_34 : initialChunk 5 4 34 = 181715960 := by
  decide

theorem residual_chunk_5_4_35 : initialChunk 5 4 35 = 123061295 := by
  decide

theorem residual_chunk_5_4_36 : finalChunk 5 4 = 59475969 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_4_3 : initialPart 5 4 3 + finalChunk 5 4 = 1630506746 := by
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
  rw [residual_chunk_5_4_27, residual_chunk_5_4_28, residual_chunk_5_4_29, residual_chunk_5_4_30, residual_chunk_5_4_31, residual_chunk_5_4_32, residual_chunk_5_4_33, residual_chunk_5_4_34, residual_chunk_5_4_35, residual_chunk_5_4_36]

end LiteralP13HodgeCertificate
end GroupApproximation
