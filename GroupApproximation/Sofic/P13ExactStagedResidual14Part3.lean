import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (1, 4). -/

theorem residual_chunk_1_4_27 : initialChunk 1 4 27 = 405376409 := by
  decide

theorem residual_chunk_1_4_28 : initialChunk 1 4 28 = 75569630 := by
  decide

theorem residual_chunk_1_4_29 : initialChunk 1 4 29 = 345762701 := by
  decide

theorem residual_chunk_1_4_30 : initialChunk 1 4 30 = 190971945 := by
  decide

theorem residual_chunk_1_4_31 : initialChunk 1 4 31 = 207065816 := by
  decide

theorem residual_chunk_1_4_32 : initialChunk 1 4 32 = 261388696 := by
  decide

theorem residual_chunk_1_4_33 : initialChunk 1 4 33 = 406897235 := by
  decide

theorem residual_chunk_1_4_34 : initialChunk 1 4 34 = 159650965 := by
  decide

theorem residual_chunk_1_4_35 : initialChunk 1 4 35 = 106599220 := by
  decide

theorem residual_chunk_1_4_36 : finalChunk 1 4 = 51595012 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_4_3 : initialPart 1 4 3 + finalChunk 1 4 = 2210877629 := by
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
  rw [residual_chunk_1_4_27, residual_chunk_1_4_28, residual_chunk_1_4_29, residual_chunk_1_4_30, residual_chunk_1_4_31, residual_chunk_1_4_32, residual_chunk_1_4_33, residual_chunk_1_4_34, residual_chunk_1_4_35, residual_chunk_1_4_36]

end LiteralP13HodgeCertificate
end GroupApproximation

