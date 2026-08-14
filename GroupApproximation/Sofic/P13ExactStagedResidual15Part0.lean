import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (1, 5). -/

theorem residual_chunk_1_5_0 : initialChunk 1 5 0 = 104978163 := by
  decide

theorem residual_chunk_1_5_1 : initialChunk 1 5 1 = 255065150 := by
  decide

theorem residual_chunk_1_5_2 : initialChunk 1 5 2 = 103171271 := by
  decide

theorem residual_chunk_1_5_3 : initialChunk 1 5 3 = 147983692 := by
  decide

theorem residual_chunk_1_5_4 : initialChunk 1 5 4 = 95080032 := by
  decide

theorem residual_chunk_1_5_5 : initialChunk 1 5 5 = 348471622 := by
  decide

theorem residual_chunk_1_5_6 : initialChunk 1 5 6 = 149503388 := by
  decide

theorem residual_chunk_1_5_7 : initialChunk 1 5 7 = 88124881 := by
  decide

theorem residual_chunk_1_5_8 : initialChunk 1 5 8 = 96366120 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_5_0 : initialPart 1 5 0 = 1388744319 := by
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
  rw [residual_chunk_1_5_0, residual_chunk_1_5_1, residual_chunk_1_5_2, residual_chunk_1_5_3, residual_chunk_1_5_4, residual_chunk_1_5_5, residual_chunk_1_5_6, residual_chunk_1_5_7, residual_chunk_1_5_8]

end LiteralP13HodgeCertificate
end GroupApproximation

