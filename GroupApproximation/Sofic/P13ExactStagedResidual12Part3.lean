import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (1, 2). -/

theorem residual_chunk_1_2_27 : initialChunk 1 2 27 = 539088129 := by
  decide

theorem residual_chunk_1_2_28 : initialChunk 1 2 28 = 111421976 := by
  decide

theorem residual_chunk_1_2_29 : initialChunk 1 2 29 = 190793085 := by
  decide

theorem residual_chunk_1_2_30 : initialChunk 1 2 30 = 85070103 := by
  decide

theorem residual_chunk_1_2_31 : initialChunk 1 2 31 = 85003817 := by
  decide

theorem residual_chunk_1_2_32 : initialChunk 1 2 32 = 130067624 := by
  decide

theorem residual_chunk_1_2_33 : initialChunk 1 2 33 = 118900498 := by
  decide

theorem residual_chunk_1_2_34 : initialChunk 1 2 34 = 124875390 := by
  decide

theorem residual_chunk_1_2_35 : initialChunk 1 2 35 = 93534009 := by
  decide

theorem residual_chunk_1_2_36 : finalChunk 1 2 = 180122826 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_2_3 : initialPart 1 2 3 + finalChunk 1 2 = 1658877457 := by
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
  rw [residual_chunk_1_2_27, residual_chunk_1_2_28, residual_chunk_1_2_29, residual_chunk_1_2_30, residual_chunk_1_2_31, residual_chunk_1_2_32, residual_chunk_1_2_33, residual_chunk_1_2_34, residual_chunk_1_2_35, residual_chunk_1_2_36]

end LiteralP13HodgeCertificate
end GroupApproximation

