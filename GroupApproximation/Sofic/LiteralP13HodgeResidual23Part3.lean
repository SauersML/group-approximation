import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (2, 3). -/

theorem residual_chunk_2_3_27 : initialChunk 2 3 27 = 434204217 := by
  decide

theorem residual_chunk_2_3_28 : initialChunk 2 3 28 = 214322675 := by
  decide

theorem residual_chunk_2_3_29 : initialChunk 2 3 29 = 363760820 := by
  decide

theorem residual_chunk_2_3_30 : initialChunk 2 3 30 = 168570971 := by
  decide

theorem residual_chunk_2_3_31 : initialChunk 2 3 31 = 186466323 := by
  decide

theorem residual_chunk_2_3_32 : initialChunk 2 3 32 = 201430488 := by
  decide

theorem residual_chunk_2_3_33 : initialChunk 2 3 33 = 228700349 := by
  decide

theorem residual_chunk_2_3_34 : initialChunk 2 3 34 = 214202398 := by
  decide

theorem residual_chunk_2_3_35 : initialChunk 2 3 35 = 93251293 := by
  decide

theorem residual_chunk_2_3_36 : finalChunk 2 3 = 121045054 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_3_3 : initialPart 2 3 3 + finalChunk 2 3 = 2225954588 := by
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
  rw [residual_chunk_2_3_27, residual_chunk_2_3_28, residual_chunk_2_3_29, residual_chunk_2_3_30, residual_chunk_2_3_31, residual_chunk_2_3_32, residual_chunk_2_3_33, residual_chunk_2_3_34, residual_chunk_2_3_35, residual_chunk_2_3_36]

end LiteralP13HodgeCertificate
end GroupApproximation
