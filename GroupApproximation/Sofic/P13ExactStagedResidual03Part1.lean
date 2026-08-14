import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (0, 3). -/

theorem residual_chunk_0_3_9 : initialChunk 0 3 9 = 559945198 := by
  decide

theorem residual_chunk_0_3_10 : initialChunk 0 3 10 = 119314885 := by
  decide

theorem residual_chunk_0_3_11 : initialChunk 0 3 11 = 146226403 := by
  decide

theorem residual_chunk_0_3_12 : initialChunk 0 3 12 = 333922989 := by
  decide

theorem residual_chunk_0_3_13 : initialChunk 0 3 13 = 167093843 := by
  decide

theorem residual_chunk_0_3_14 : initialChunk 0 3 14 = 175510977 := by
  decide

theorem residual_chunk_0_3_15 : initialChunk 0 3 15 = 149393136 := by
  decide

theorem residual_chunk_0_3_16 : initialChunk 0 3 16 = 87483148 := by
  decide

theorem residual_chunk_0_3_17 : initialChunk 0 3 17 = 263201260 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_3_1 : initialPart 0 3 1 = 2002091839 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((1 : Fin 4), (0 : Fin 9)) = (9 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (1 : Fin 9)) = (10 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (2 : Fin 9)) = (11 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (3 : Fin 9)) = (12 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (4 : Fin 9)) = (13 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (5 : Fin 9)) = (14 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (6 : Fin 9)) = (15 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (7 : Fin 9)) = (16 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (8 : Fin 9)) = (17 : Fin 36) by decide]
  rw [residual_chunk_0_3_9, residual_chunk_0_3_10, residual_chunk_0_3_11, residual_chunk_0_3_12, residual_chunk_0_3_13, residual_chunk_0_3_14, residual_chunk_0_3_15, residual_chunk_0_3_16, residual_chunk_0_3_17]

end LiteralP13HodgeCertificate
end GroupApproximation

