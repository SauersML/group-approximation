import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (4, 2). -/

theorem residual_chunk_4_2_0 : initialChunk 4 2 0 = 138439383 := by
  decide

theorem residual_chunk_4_2_1 : initialChunk 4 2 1 = 197369424 := by
  decide

theorem residual_chunk_4_2_2 : initialChunk 4 2 2 = 114802111 := by
  decide

theorem residual_chunk_4_2_3 : initialChunk 4 2 3 = 287443880 := by
  decide

theorem residual_chunk_4_2_4 : initialChunk 4 2 4 = 137081082 := by
  decide

theorem residual_chunk_4_2_5 : initialChunk 4 2 5 = 386472443 := by
  decide

theorem residual_chunk_4_2_6 : initialChunk 4 2 6 = 224565998 := by
  decide

theorem residual_chunk_4_2_7 : initialChunk 4 2 7 = 211666686 := by
  decide

theorem residual_chunk_4_2_8 : initialChunk 4 2 8 = 429180947 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_2_0 : initialPart 4 2 0 = 2127021954 := by
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
  rw [residual_chunk_4_2_0, residual_chunk_4_2_1, residual_chunk_4_2_2, residual_chunk_4_2_3, residual_chunk_4_2_4, residual_chunk_4_2_5, residual_chunk_4_2_6, residual_chunk_4_2_7, residual_chunk_4_2_8]

end LiteralP13HodgeCertificate
end GroupApproximation
