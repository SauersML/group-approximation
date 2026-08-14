import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (2, 1). -/

theorem residual_chunk_2_1_27 : initialChunk 2 1 27 = 486884614 := by
  decide

theorem residual_chunk_2_1_28 : initialChunk 2 1 28 = 105938048 := by
  decide

theorem residual_chunk_2_1_29 : initialChunk 2 1 29 = 184123852 := by
  decide

theorem residual_chunk_2_1_30 : initialChunk 2 1 30 = 197428592 := by
  decide

theorem residual_chunk_2_1_31 : initialChunk 2 1 31 = 155315240 := by
  decide

theorem residual_chunk_2_1_32 : initialChunk 2 1 32 = 252923219 := by
  decide

theorem residual_chunk_2_1_33 : initialChunk 2 1 33 = 423854243 := by
  decide

theorem residual_chunk_2_1_34 : initialChunk 2 1 34 = 103515265 := by
  decide

theorem residual_chunk_2_1_35 : initialChunk 2 1 35 = 213182923 := by
  decide

theorem residual_chunk_2_1_36 : finalChunk 2 1 = 91070484 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_1_3 : initialPart 2 1 3 + finalChunk 2 1 = 2214236480 := by
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
  rw [residual_chunk_2_1_27, residual_chunk_2_1_28, residual_chunk_2_1_29, residual_chunk_2_1_30, residual_chunk_2_1_31, residual_chunk_2_1_32, residual_chunk_2_1_33, residual_chunk_2_1_34, residual_chunk_2_1_35, residual_chunk_2_1_36]

end LiteralP13HodgeCertificate
end GroupApproximation
