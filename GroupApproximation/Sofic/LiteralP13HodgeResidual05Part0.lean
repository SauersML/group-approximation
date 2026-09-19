import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (0, 5). -/

theorem residual_chunk_0_5_0 : initialChunk 0 5 0 = 218600977 := by
  decide

theorem residual_chunk_0_5_1 : initialChunk 0 5 1 = 189914318 := by
  decide

theorem residual_chunk_0_5_2 : initialChunk 0 5 2 = 248147136 := by
  decide

theorem residual_chunk_0_5_3 : initialChunk 0 5 3 = 352062813 := by
  decide

theorem residual_chunk_0_5_4 : initialChunk 0 5 4 = 158506573 := by
  decide

theorem residual_chunk_0_5_5 : initialChunk 0 5 5 = 339643979 := by
  decide

theorem residual_chunk_0_5_6 : initialChunk 0 5 6 = 115034212 := by
  decide

theorem residual_chunk_0_5_7 : initialChunk 0 5 7 = 290627146 := by
  decide

theorem residual_chunk_0_5_8 : initialChunk 0 5 8 = 162188077 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_5_0 : initialPart 0 5 0 = 2074725231 := by
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
  rw [residual_chunk_0_5_0, residual_chunk_0_5_1, residual_chunk_0_5_2, residual_chunk_0_5_3, residual_chunk_0_5_4, residual_chunk_0_5_5, residual_chunk_0_5_6, residual_chunk_0_5_7, residual_chunk_0_5_8]

end LiteralP13HodgeCertificate
end GroupApproximation
