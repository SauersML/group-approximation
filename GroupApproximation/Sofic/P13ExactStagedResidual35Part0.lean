import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (3, 5). -/

theorem residual_chunk_3_5_0 : initialChunk 3 5 0 = 86408652 := by
  decide

theorem residual_chunk_3_5_1 : initialChunk 3 5 1 = 207172130 := by
  decide

theorem residual_chunk_3_5_2 : initialChunk 3 5 2 = 29694138 := by
  decide

theorem residual_chunk_3_5_3 : initialChunk 3 5 3 = 409357903 := by
  decide

theorem residual_chunk_3_5_4 : initialChunk 3 5 4 = 133942120 := by
  decide

theorem residual_chunk_3_5_5 : initialChunk 3 5 5 = 312989454 := by
  decide

theorem residual_chunk_3_5_6 : initialChunk 3 5 6 = 156423707 := by
  decide

theorem residual_chunk_3_5_7 : initialChunk 3 5 7 = 168519421 := by
  decide

theorem residual_chunk_3_5_8 : initialChunk 3 5 8 = 140634733 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_5_0 : initialPart 3 5 0 = 1645142258 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((0 : Fin 4), (0 : Fin 9)) = (0 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (1 : Fin 9)) = (1 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (2 : Fin 9)) = (2 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (3 : Fin 9)) = (3 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (4 : Fin 9)) = (4 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (5 : Fin 9)) = (5 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (6 : Fin 9)) = (6 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (7 : Fin 9)) = (7 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (8 : Fin 9)) = (8 : Fin 36) by decide]
  rw [residual_chunk_3_5_0, residual_chunk_3_5_1, residual_chunk_3_5_2, residual_chunk_3_5_3, residual_chunk_3_5_4, residual_chunk_3_5_5, residual_chunk_3_5_6, residual_chunk_3_5_7, residual_chunk_3_5_8]

end LiteralP13HodgeCertificate
end GroupApproximation

