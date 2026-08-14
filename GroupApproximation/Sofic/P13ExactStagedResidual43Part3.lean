import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (4, 3). -/

theorem residual_chunk_4_3_27 : initialChunk 4 3 27 = 381380295 := by
  decide

theorem residual_chunk_4_3_28 : initialChunk 4 3 28 = 157288113 := by
  decide

theorem residual_chunk_4_3_29 : initialChunk 4 3 29 = 306526994 := by
  decide

theorem residual_chunk_4_3_30 : initialChunk 4 3 30 = 270524039 := by
  decide

theorem residual_chunk_4_3_31 : initialChunk 4 3 31 = 206544457 := by
  decide

theorem residual_chunk_4_3_32 : initialChunk 4 3 32 = 150858787 := by
  decide

theorem residual_chunk_4_3_33 : initialChunk 4 3 33 = 171832237 := by
  decide

theorem residual_chunk_4_3_34 : initialChunk 4 3 34 = 127479617 := by
  decide

theorem residual_chunk_4_3_35 : initialChunk 4 3 35 = 79844080 := by
  decide

theorem residual_chunk_4_3_36 : finalChunk 4 3 = 91168040 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_3_3 : initialPart 4 3 3 + finalChunk 4 3 = 1943446659 := by
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
  rw [residual_chunk_4_3_27, residual_chunk_4_3_28, residual_chunk_4_3_29, residual_chunk_4_3_30, residual_chunk_4_3_31, residual_chunk_4_3_32, residual_chunk_4_3_33, residual_chunk_4_3_34, residual_chunk_4_3_35, residual_chunk_4_3_36]

end LiteralP13HodgeCertificate
end GroupApproximation

