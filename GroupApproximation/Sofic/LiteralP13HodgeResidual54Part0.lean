import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (5, 4). -/

theorem residual_chunk_5_4_0 : initialChunk 5 4 0 = 107597476 := by
  decide

theorem residual_chunk_5_4_1 : initialChunk 5 4 1 = 220070694 := by
  decide

theorem residual_chunk_5_4_2 : initialChunk 5 4 2 = 182215084 := by
  decide

theorem residual_chunk_5_4_3 : initialChunk 5 4 3 = 244689359 := by
  decide

theorem residual_chunk_5_4_4 : initialChunk 5 4 4 = 101641497 := by
  decide

theorem residual_chunk_5_4_5 : initialChunk 5 4 5 = 171423228 := by
  decide

theorem residual_chunk_5_4_6 : initialChunk 5 4 6 = 96930138 := by
  decide

theorem residual_chunk_5_4_7 : initialChunk 5 4 7 = 130079181 := by
  decide

theorem residual_chunk_5_4_8 : initialChunk 5 4 8 = 79150236 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_4_0 : initialPart 5 4 0 = 1333796893 := by
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
  rw [residual_chunk_5_4_0, residual_chunk_5_4_1, residual_chunk_5_4_2, residual_chunk_5_4_3, residual_chunk_5_4_4, residual_chunk_5_4_5, residual_chunk_5_4_6, residual_chunk_5_4_7, residual_chunk_5_4_8]

end LiteralP13HodgeCertificate
end GroupApproximation
