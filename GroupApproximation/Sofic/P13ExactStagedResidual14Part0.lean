import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (1, 4). -/

theorem residual_chunk_1_4_0 : initialChunk 1 4 0 = 116386946 := by
  decide

theorem residual_chunk_1_4_1 : initialChunk 1 4 1 = 245556026 := by
  decide

theorem residual_chunk_1_4_2 : initialChunk 1 4 2 = 102240432 := by
  decide

theorem residual_chunk_1_4_3 : initialChunk 1 4 3 = 230225815 := by
  decide

theorem residual_chunk_1_4_4 : initialChunk 1 4 4 = 107463134 := by
  decide

theorem residual_chunk_1_4_5 : initialChunk 1 4 5 = 64402886 := by
  decide

theorem residual_chunk_1_4_6 : initialChunk 1 4 6 = 211657250 := by
  decide

theorem residual_chunk_1_4_7 : initialChunk 1 4 7 = 125693116 := by
  decide

theorem residual_chunk_1_4_8 : initialChunk 1 4 8 = 121195356 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_4_0 : initialPart 1 4 0 = 1324820961 := by
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
  rw [residual_chunk_1_4_0, residual_chunk_1_4_1, residual_chunk_1_4_2, residual_chunk_1_4_3, residual_chunk_1_4_4, residual_chunk_1_4_5, residual_chunk_1_4_6, residual_chunk_1_4_7, residual_chunk_1_4_8]

end LiteralP13HodgeCertificate
end GroupApproximation

