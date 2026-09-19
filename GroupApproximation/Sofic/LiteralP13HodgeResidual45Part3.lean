import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (4, 5). -/

theorem residual_chunk_4_5_27 : initialChunk 4 5 27 = 251285096 := by
  decide

theorem residual_chunk_4_5_28 : initialChunk 4 5 28 = 126827665 := by
  decide

theorem residual_chunk_4_5_29 : initialChunk 4 5 29 = 185850999 := by
  decide

theorem residual_chunk_4_5_30 : initialChunk 4 5 30 = 115195462 := by
  decide

theorem residual_chunk_4_5_31 : initialChunk 4 5 31 = 199034620 := by
  decide

theorem residual_chunk_4_5_32 : initialChunk 4 5 32 = 138128891 := by
  decide

theorem residual_chunk_4_5_33 : initialChunk 4 5 33 = 521751286 := by
  decide

theorem residual_chunk_4_5_34 : initialChunk 4 5 34 = 141970658 := by
  decide

theorem residual_chunk_4_5_35 : initialChunk 4 5 35 = 71147006 := by
  decide

theorem residual_chunk_4_5_36 : finalChunk 4 5 = 28445865 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_5_3 : initialPart 4 5 3 + finalChunk 4 5 = 1779637548 := by
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
  rw [residual_chunk_4_5_27, residual_chunk_4_5_28, residual_chunk_4_5_29, residual_chunk_4_5_30, residual_chunk_4_5_31, residual_chunk_4_5_32, residual_chunk_4_5_33, residual_chunk_4_5_34, residual_chunk_4_5_35, residual_chunk_4_5_36]

end LiteralP13HodgeCertificate
end GroupApproximation
