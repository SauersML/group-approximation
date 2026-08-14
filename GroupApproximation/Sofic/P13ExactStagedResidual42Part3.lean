import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (4, 2). -/

theorem residual_chunk_4_2_27 : initialChunk 4 2 27 = 155206215 := by
  decide

theorem residual_chunk_4_2_28 : initialChunk 4 2 28 = 137459750 := by
  decide

theorem residual_chunk_4_2_29 : initialChunk 4 2 29 = 111102755 := by
  decide

theorem residual_chunk_4_2_30 : initialChunk 4 2 30 = 199316319 := by
  decide

theorem residual_chunk_4_2_31 : initialChunk 4 2 31 = 110976823 := by
  decide

theorem residual_chunk_4_2_32 : initialChunk 4 2 32 = 121767527 := by
  decide

theorem residual_chunk_4_2_33 : initialChunk 4 2 33 = 269775101 := by
  decide

theorem residual_chunk_4_2_34 : initialChunk 4 2 34 = 119104304 := by
  decide

theorem residual_chunk_4_2_35 : initialChunk 4 2 35 = 119832151 := by
  decide

theorem residual_chunk_4_2_36 : finalChunk 4 2 = 39312725 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_2_3 : initialPart 4 2 3 + finalChunk 4 2 = 1383853670 := by
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
  rw [residual_chunk_4_2_27, residual_chunk_4_2_28, residual_chunk_4_2_29, residual_chunk_4_2_30, residual_chunk_4_2_31, residual_chunk_4_2_32, residual_chunk_4_2_33, residual_chunk_4_2_34, residual_chunk_4_2_35, residual_chunk_4_2_36]

end LiteralP13HodgeCertificate
end GroupApproximation

