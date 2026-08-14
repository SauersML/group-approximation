import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (3, 1). -/

theorem residual_chunk_3_1_0 : initialChunk 3 1 0 = 127267763 := by
  decide

theorem residual_chunk_3_1_1 : initialChunk 3 1 1 = 87347284 := by
  decide

theorem residual_chunk_3_1_2 : initialChunk 3 1 2 = 214395150 := by
  decide

theorem residual_chunk_3_1_3 : initialChunk 3 1 3 = 182130615 := by
  decide

theorem residual_chunk_3_1_4 : initialChunk 3 1 4 = 133813974 := by
  decide

theorem residual_chunk_3_1_5 : initialChunk 3 1 5 = 111730560 := by
  decide

theorem residual_chunk_3_1_6 : initialChunk 3 1 6 = 135688706 := by
  decide

theorem residual_chunk_3_1_7 : initialChunk 3 1 7 = 126445099 := by
  decide

theorem residual_chunk_3_1_8 : initialChunk 3 1 8 = 149289763 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_1_0 : initialPart 3 1 0 = 1268108914 := by
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
  rw [residual_chunk_3_1_0, residual_chunk_3_1_1, residual_chunk_3_1_2, residual_chunk_3_1_3, residual_chunk_3_1_4, residual_chunk_3_1_5, residual_chunk_3_1_6, residual_chunk_3_1_7, residual_chunk_3_1_8]

end LiteralP13HodgeCertificate
end GroupApproximation

