import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (5, 1). -/

theorem residual_chunk_5_1_27 : initialChunk 5 1 27 = 349612626 := by
  decide

theorem residual_chunk_5_1_28 : initialChunk 5 1 28 = 131524147 := by
  decide

theorem residual_chunk_5_1_29 : initialChunk 5 1 29 = 256109580 := by
  decide

theorem residual_chunk_5_1_30 : initialChunk 5 1 30 = 120864684 := by
  decide

theorem residual_chunk_5_1_31 : initialChunk 5 1 31 = 134928450 := by
  decide

theorem residual_chunk_5_1_32 : initialChunk 5 1 32 = 307430088 := by
  decide

theorem residual_chunk_5_1_33 : initialChunk 5 1 33 = 93746672 := by
  decide

theorem residual_chunk_5_1_34 : initialChunk 5 1 34 = 185185837 := by
  decide

theorem residual_chunk_5_1_35 : initialChunk 5 1 35 = 127612507 := by
  decide

theorem residual_chunk_5_1_36 : finalChunk 5 1 = 25061239 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_1_3 : initialPart 5 1 3 + finalChunk 5 1 = 1732075830 := by
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
  rw [residual_chunk_5_1_27, residual_chunk_5_1_28, residual_chunk_5_1_29, residual_chunk_5_1_30, residual_chunk_5_1_31, residual_chunk_5_1_32, residual_chunk_5_1_33, residual_chunk_5_1_34, residual_chunk_5_1_35, residual_chunk_5_1_36]

end LiteralP13HodgeCertificate
end GroupApproximation

