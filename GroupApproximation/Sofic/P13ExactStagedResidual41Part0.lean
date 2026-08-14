import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (4, 1). -/

theorem residual_chunk_4_1_0 : initialChunk 4 1 0 = 153503574 := by
  decide

theorem residual_chunk_4_1_1 : initialChunk 4 1 1 = 103051344 := by
  decide

theorem residual_chunk_4_1_2 : initialChunk 4 1 2 = 165806216 := by
  decide

theorem residual_chunk_4_1_3 : initialChunk 4 1 3 = 213275276 := by
  decide

theorem residual_chunk_4_1_4 : initialChunk 4 1 4 = 99803359 := by
  decide

theorem residual_chunk_4_1_5 : initialChunk 4 1 5 = 155153477 := by
  decide

theorem residual_chunk_4_1_6 : initialChunk 4 1 6 = 178168368 := by
  decide

theorem residual_chunk_4_1_7 : initialChunk 4 1 7 = 139468734 := by
  decide

theorem residual_chunk_4_1_8 : initialChunk 4 1 8 = 134665778 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_1_0 : initialPart 4 1 0 = 1342896126 := by
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
  rw [residual_chunk_4_1_0, residual_chunk_4_1_1, residual_chunk_4_1_2, residual_chunk_4_1_3, residual_chunk_4_1_4, residual_chunk_4_1_5, residual_chunk_4_1_6, residual_chunk_4_1_7, residual_chunk_4_1_8]

end LiteralP13HodgeCertificate
end GroupApproximation

