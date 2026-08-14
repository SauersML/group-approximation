import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (2, 5). -/

theorem residual_chunk_2_5_27 : initialChunk 2 5 27 = 429067536 := by
  decide

theorem residual_chunk_2_5_28 : initialChunk 2 5 28 = 194715246 := by
  decide

theorem residual_chunk_2_5_29 : initialChunk 2 5 29 = 219115583 := by
  decide

theorem residual_chunk_2_5_30 : initialChunk 2 5 30 = 288082005 := by
  decide

theorem residual_chunk_2_5_31 : initialChunk 2 5 31 = 294969655 := by
  decide

theorem residual_chunk_2_5_32 : initialChunk 2 5 32 = 171961432 := by
  decide

theorem residual_chunk_2_5_33 : initialChunk 2 5 33 = 362152930 := by
  decide

theorem residual_chunk_2_5_34 : initialChunk 2 5 34 = 241552341 := by
  decide

theorem residual_chunk_2_5_35 : initialChunk 2 5 35 = 102913704 := by
  decide

theorem residual_chunk_2_5_36 : finalChunk 2 5 = 115541178 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_5_3 : initialPart 2 5 3 + finalChunk 2 5 = 2420071610 := by
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
  rw [residual_chunk_2_5_27, residual_chunk_2_5_28, residual_chunk_2_5_29, residual_chunk_2_5_30, residual_chunk_2_5_31, residual_chunk_2_5_32, residual_chunk_2_5_33, residual_chunk_2_5_34, residual_chunk_2_5_35, residual_chunk_2_5_36]

end LiteralP13HodgeCertificate
end GroupApproximation
