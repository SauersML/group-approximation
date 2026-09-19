import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (5, 0). -/

theorem residual_chunk_5_0_27 : initialChunk 5 0 27 = 331395755 := by
  decide

theorem residual_chunk_5_0_28 : initialChunk 5 0 28 = 94006091 := by
  decide

theorem residual_chunk_5_0_29 : initialChunk 5 0 29 = 219348731 := by
  decide

theorem residual_chunk_5_0_30 : initialChunk 5 0 30 = 232172323 := by
  decide

theorem residual_chunk_5_0_31 : initialChunk 5 0 31 = 177066349 := by
  decide

theorem residual_chunk_5_0_32 : initialChunk 5 0 32 = 178448668 := by
  decide

theorem residual_chunk_5_0_33 : initialChunk 5 0 33 = 272293111 := by
  decide

theorem residual_chunk_5_0_34 : initialChunk 5 0 34 = 98966838 := by
  decide

theorem residual_chunk_5_0_35 : initialChunk 5 0 35 = 146500412 := by
  decide

theorem residual_chunk_5_0_36 : finalChunk 5 0 = 40469299 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_0_3 : initialPart 5 0 3 + finalChunk 5 0 = 1790667577 := by
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
  rw [residual_chunk_5_0_27, residual_chunk_5_0_28, residual_chunk_5_0_29, residual_chunk_5_0_30, residual_chunk_5_0_31, residual_chunk_5_0_32, residual_chunk_5_0_33, residual_chunk_5_0_34, residual_chunk_5_0_35, residual_chunk_5_0_36]

end LiteralP13HodgeCertificate
end GroupApproximation
