import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (0, 0). -/

theorem residual_chunk_0_0_27 : initialChunk 0 0 27 = 505460100 := by
  decide

theorem residual_chunk_0_0_28 : initialChunk 0 0 28 = 110058022 := by
  decide

theorem residual_chunk_0_0_29 : initialChunk 0 0 29 = 168642692 := by
  decide

theorem residual_chunk_0_0_30 : initialChunk 0 0 30 = 218374553 := by
  decide

theorem residual_chunk_0_0_31 : initialChunk 0 0 31 = 189904196 := by
  decide

theorem residual_chunk_0_0_32 : initialChunk 0 0 32 = 210016037 := by
  decide

theorem residual_chunk_0_0_33 : initialChunk 0 0 33 = 411804396 := by
  decide

theorem residual_chunk_0_0_34 : initialChunk 0 0 34 = 151374799 := by
  decide

theorem residual_chunk_0_0_35 : initialChunk 0 0 35 = 255700704 := by
  decide

theorem residual_chunk_0_0_36 : finalChunk 0 0 = 169654143 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_0_3 : initialPart 0 0 3 + finalChunk 0 0 = 2390989642 := by
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
  rw [residual_chunk_0_0_27, residual_chunk_0_0_28, residual_chunk_0_0_29, residual_chunk_0_0_30, residual_chunk_0_0_31, residual_chunk_0_0_32, residual_chunk_0_0_33, residual_chunk_0_0_34, residual_chunk_0_0_35, residual_chunk_0_0_36]

end LiteralP13HodgeCertificate
end GroupApproximation
