import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (3, 3). -/

theorem residual_chunk_3_3_0 : initialChunk 3 3 0 = 97978778 := by
  decide

theorem residual_chunk_3_3_1 : initialChunk 3 3 1 = 143169887 := by
  decide

theorem residual_chunk_3_3_2 : initialChunk 3 3 2 = 194791993 := by
  decide

theorem residual_chunk_3_3_3 : initialChunk 3 3 3 = 99745131 := by
  decide

theorem residual_chunk_3_3_4 : initialChunk 3 3 4 = 157642663 := by
  decide

theorem residual_chunk_3_3_5 : initialChunk 3 3 5 = 140788309 := by
  decide

theorem residual_chunk_3_3_6 : initialChunk 3 3 6 = 150953253 := by
  decide

theorem residual_chunk_3_3_7 : initialChunk 3 3 7 = 75708203 := by
  decide

theorem residual_chunk_3_3_8 : initialChunk 3 3 8 = 135538732 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_3_0 : initialPart 3 3 0 = 1196316949 := by
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
  rw [residual_chunk_3_3_0, residual_chunk_3_3_1, residual_chunk_3_3_2, residual_chunk_3_3_3, residual_chunk_3_3_4, residual_chunk_3_3_5, residual_chunk_3_3_6, residual_chunk_3_3_7, residual_chunk_3_3_8]

end LiteralP13HodgeCertificate
end GroupApproximation

