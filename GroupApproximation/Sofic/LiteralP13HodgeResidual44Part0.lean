import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (4, 4). -/

theorem residual_chunk_4_4_0 : initialChunk 4 4 0 = 137933707 := by
  decide

theorem residual_chunk_4_4_1 : initialChunk 4 4 1 = 272481024 := by
  decide

theorem residual_chunk_4_4_2 : initialChunk 4 4 2 = 94815025 := by
  decide

theorem residual_chunk_4_4_3 : initialChunk 4 4 3 = 279876657 := by
  decide

theorem residual_chunk_4_4_4 : initialChunk 4 4 4 = 79498369 := by
  decide

theorem residual_chunk_4_4_5 : initialChunk 4 4 5 = 244022303 := by
  decide

theorem residual_chunk_4_4_6 : initialChunk 4 4 6 = 139659156 := by
  decide

theorem residual_chunk_4_4_7 : initialChunk 4 4 7 = 82209067 := by
  decide

theorem residual_chunk_4_4_8 : initialChunk 4 4 8 = 133520175 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_4_0 : initialPart 4 4 0 = 1464015483 := by
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
  rw [residual_chunk_4_4_0, residual_chunk_4_4_1, residual_chunk_4_4_2, residual_chunk_4_4_3, residual_chunk_4_4_4, residual_chunk_4_4_5, residual_chunk_4_4_6, residual_chunk_4_4_7, residual_chunk_4_4_8]

end LiteralP13HodgeCertificate
end GroupApproximation
