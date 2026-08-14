import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (4, 5). -/

theorem residual_chunk_4_5_0 : initialChunk 4 5 0 = 129298834 := by
  decide

theorem residual_chunk_4_5_1 : initialChunk 4 5 1 = 210224621 := by
  decide

theorem residual_chunk_4_5_2 : initialChunk 4 5 2 = 128383953 := by
  decide

theorem residual_chunk_4_5_3 : initialChunk 4 5 3 = 338595893 := by
  decide

theorem residual_chunk_4_5_4 : initialChunk 4 5 4 = 64393825 := by
  decide

theorem residual_chunk_4_5_5 : initialChunk 4 5 5 = 236398631 := by
  decide

theorem residual_chunk_4_5_6 : initialChunk 4 5 6 = 61207812 := by
  decide

theorem residual_chunk_4_5_7 : initialChunk 4 5 7 = 105562060 := by
  decide

theorem residual_chunk_4_5_8 : initialChunk 4 5 8 = 107251577 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_5_0 : initialPart 4 5 0 = 1381317206 := by
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
  rw [residual_chunk_4_5_0, residual_chunk_4_5_1, residual_chunk_4_5_2, residual_chunk_4_5_3, residual_chunk_4_5_4, residual_chunk_4_5_5, residual_chunk_4_5_6, residual_chunk_4_5_7, residual_chunk_4_5_8]

end LiteralP13HodgeCertificate
end GroupApproximation

