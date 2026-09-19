import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (2, 5). -/

theorem residual_chunk_2_5_0 : initialChunk 2 5 0 = 137445276 := by
  decide

theorem residual_chunk_2_5_1 : initialChunk 2 5 1 = 189793485 := by
  decide

theorem residual_chunk_2_5_2 : initialChunk 2 5 2 = 241839723 := by
  decide

theorem residual_chunk_2_5_3 : initialChunk 2 5 3 = 355204624 := by
  decide

theorem residual_chunk_2_5_4 : initialChunk 2 5 4 = 111012588 := by
  decide

theorem residual_chunk_2_5_5 : initialChunk 2 5 5 = 312676294 := by
  decide

theorem residual_chunk_2_5_6 : initialChunk 2 5 6 = 208586353 := by
  decide

theorem residual_chunk_2_5_7 : initialChunk 2 5 7 = 200928460 := by
  decide

theorem residual_chunk_2_5_8 : initialChunk 2 5 8 = 169475844 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_5_0 : initialPart 2 5 0 = 1926962647 := by
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
  rw [residual_chunk_2_5_0, residual_chunk_2_5_1, residual_chunk_2_5_2, residual_chunk_2_5_3, residual_chunk_2_5_4, residual_chunk_2_5_5, residual_chunk_2_5_6, residual_chunk_2_5_7, residual_chunk_2_5_8]

end LiteralP13HodgeCertificate
end GroupApproximation
