import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (1, 0). -/

theorem residual_chunk_1_0_27 : initialChunk 1 0 27 = 243363460 := by
  decide

theorem residual_chunk_1_0_28 : initialChunk 1 0 28 = 67092993 := by
  decide

theorem residual_chunk_1_0_29 : initialChunk 1 0 29 = 269451190 := by
  decide

theorem residual_chunk_1_0_30 : initialChunk 1 0 30 = 337471738 := by
  decide

theorem residual_chunk_1_0_31 : initialChunk 1 0 31 = 116648654 := by
  decide

theorem residual_chunk_1_0_32 : initialChunk 1 0 32 = 168868509 := by
  decide

theorem residual_chunk_1_0_33 : initialChunk 1 0 33 = 274733082 := by
  decide

theorem residual_chunk_1_0_34 : initialChunk 1 0 34 = 129215332 := by
  decide

theorem residual_chunk_1_0_35 : initialChunk 1 0 35 = 151590417 := by
  decide

theorem residual_chunk_1_0_36 : finalChunk 1 0 = 66277262 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_0_3 : initialPart 1 0 3 + finalChunk 1 0 = 1824712637 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((3 : Fin 4), (0 : Fin 9)) = (27 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (1 : Fin 9)) = (28 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (2 : Fin 9)) = (29 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (3 : Fin 9)) = (30 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (4 : Fin 9)) = (31 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (5 : Fin 9)) = (32 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (6 : Fin 9)) = (33 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (7 : Fin 9)) = (34 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (8 : Fin 9)) = (35 : Fin 36) by decide]
  rw [residual_chunk_1_0_27, residual_chunk_1_0_28, residual_chunk_1_0_29, residual_chunk_1_0_30, residual_chunk_1_0_31, residual_chunk_1_0_32, residual_chunk_1_0_33, residual_chunk_1_0_34, residual_chunk_1_0_35, residual_chunk_1_0_36]

end LiteralP13HodgeCertificate
end GroupApproximation
