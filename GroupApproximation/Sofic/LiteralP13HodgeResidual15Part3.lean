import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (1, 5). -/

theorem residual_chunk_1_5_27 : initialChunk 1 5 27 = 117465281 := by
  decide

theorem residual_chunk_1_5_28 : initialChunk 1 5 28 = 167513280 := by
  decide

theorem residual_chunk_1_5_29 : initialChunk 1 5 29 = 181237348 := by
  decide

theorem residual_chunk_1_5_30 : initialChunk 1 5 30 = 144947336 := by
  decide

theorem residual_chunk_1_5_31 : initialChunk 1 5 31 = 259928507 := by
  decide

theorem residual_chunk_1_5_32 : initialChunk 1 5 32 = 119471072 := by
  decide

theorem residual_chunk_1_5_33 : initialChunk 1 5 33 = 356846174 := by
  decide

theorem residual_chunk_1_5_34 : initialChunk 1 5 34 = 82122346 := by
  decide

theorem residual_chunk_1_5_35 : initialChunk 1 5 35 = 105954117 := by
  decide

theorem residual_chunk_1_5_36 : finalChunk 1 5 = 110200767 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_5_3 : initialPart 1 5 3 + finalChunk 1 5 = 1645686228 := by
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
  rw [residual_chunk_1_5_27, residual_chunk_1_5_28, residual_chunk_1_5_29, residual_chunk_1_5_30, residual_chunk_1_5_31, residual_chunk_1_5_32, residual_chunk_1_5_33, residual_chunk_1_5_34, residual_chunk_1_5_35, residual_chunk_1_5_36]

end LiteralP13HodgeCertificate
end GroupApproximation
