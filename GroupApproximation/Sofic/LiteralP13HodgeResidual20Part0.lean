import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (2, 0). -/

theorem residual_chunk_2_0_0 : initialChunk 2 0 0 = 215144378 := by
  decide

theorem residual_chunk_2_0_1 : initialChunk 2 0 1 = 242618424 := by
  decide

theorem residual_chunk_2_0_2 : initialChunk 2 0 2 = 341864759 := by
  decide

theorem residual_chunk_2_0_3 : initialChunk 2 0 3 = 394049014 := by
  decide

theorem residual_chunk_2_0_4 : initialChunk 2 0 4 = 97030212 := by
  decide

theorem residual_chunk_2_0_5 : initialChunk 2 0 5 = 222201621 := by
  decide

theorem residual_chunk_2_0_6 : initialChunk 2 0 6 = 287467193 := by
  decide

theorem residual_chunk_2_0_7 : initialChunk 2 0 7 = 316893076 := by
  decide

theorem residual_chunk_2_0_8 : initialChunk 2 0 8 = 196668814 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_0_0 : initialPart 2 0 0 = 2313937491 := by
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
  rw [residual_chunk_2_0_0, residual_chunk_2_0_1, residual_chunk_2_0_2, residual_chunk_2_0_3, residual_chunk_2_0_4, residual_chunk_2_0_5, residual_chunk_2_0_6, residual_chunk_2_0_7, residual_chunk_2_0_8]

end LiteralP13HodgeCertificate
end GroupApproximation
