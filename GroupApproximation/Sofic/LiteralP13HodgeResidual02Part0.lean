import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (0, 2). -/

theorem residual_chunk_0_2_0 : initialChunk 0 2 0 = 255478202 := by
  decide

theorem residual_chunk_0_2_1 : initialChunk 0 2 1 = 242477604 := by
  decide

theorem residual_chunk_0_2_2 : initialChunk 0 2 2 = 316344191 := by
  decide

theorem residual_chunk_0_2_3 : initialChunk 0 2 3 = 391368958 := by
  decide

theorem residual_chunk_0_2_4 : initialChunk 0 2 4 = 150885791 := by
  decide

theorem residual_chunk_0_2_5 : initialChunk 0 2 5 = 203328172 := by
  decide

theorem residual_chunk_0_2_6 : initialChunk 0 2 6 = 208564315 := by
  decide

theorem residual_chunk_0_2_7 : initialChunk 0 2 7 = 206860890 := by
  decide

theorem residual_chunk_0_2_8 : initialChunk 0 2 8 = 204851301 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_2_0 : initialPart 0 2 0 = 2180159424 := by
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
  rw [residual_chunk_0_2_0, residual_chunk_0_2_1, residual_chunk_0_2_2, residual_chunk_0_2_3, residual_chunk_0_2_4, residual_chunk_0_2_5, residual_chunk_0_2_6, residual_chunk_0_2_7, residual_chunk_0_2_8]

end LiteralP13HodgeCertificate
end GroupApproximation
