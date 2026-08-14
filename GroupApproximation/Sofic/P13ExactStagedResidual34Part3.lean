import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (3, 4). -/

theorem residual_chunk_3_4_27 : initialChunk 3 4 27 = 436844896 := by
  decide

theorem residual_chunk_3_4_28 : initialChunk 3 4 28 = 230039536 := by
  decide

theorem residual_chunk_3_4_29 : initialChunk 3 4 29 = 213931516 := by
  decide

theorem residual_chunk_3_4_30 : initialChunk 3 4 30 = 83449951 := by
  decide

theorem residual_chunk_3_4_31 : initialChunk 3 4 31 = 125362787 := by
  decide

theorem residual_chunk_3_4_32 : initialChunk 3 4 32 = 149291560 := by
  decide

theorem residual_chunk_3_4_33 : initialChunk 3 4 33 = 134259297 := by
  decide

theorem residual_chunk_3_4_34 : initialChunk 3 4 34 = 132194929 := by
  decide

theorem residual_chunk_3_4_35 : initialChunk 3 4 35 = 150211477 := by
  decide

theorem residual_chunk_3_4_36 : finalChunk 3 4 = 90585782 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_4_3 : initialPart 3 4 3 + finalChunk 3 4 = 1746171731 := by
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
  rw [residual_chunk_3_4_27, residual_chunk_3_4_28, residual_chunk_3_4_29, residual_chunk_3_4_30, residual_chunk_3_4_31, residual_chunk_3_4_32, residual_chunk_3_4_33, residual_chunk_3_4_34, residual_chunk_3_4_35, residual_chunk_3_4_36]

end LiteralP13HodgeCertificate
end GroupApproximation

