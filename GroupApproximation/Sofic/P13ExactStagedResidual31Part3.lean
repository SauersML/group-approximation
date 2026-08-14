import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (3, 1). -/

theorem residual_chunk_3_1_27 : initialChunk 3 1 27 = 139976971 := by
  decide

theorem residual_chunk_3_1_28 : initialChunk 3 1 28 = 127343554 := by
  decide

theorem residual_chunk_3_1_29 : initialChunk 3 1 29 = 233824047 := by
  decide

theorem residual_chunk_3_1_30 : initialChunk 3 1 30 = 147757226 := by
  decide

theorem residual_chunk_3_1_31 : initialChunk 3 1 31 = 131283239 := by
  decide

theorem residual_chunk_3_1_32 : initialChunk 3 1 32 = 252491146 := by
  decide

theorem residual_chunk_3_1_33 : initialChunk 3 1 33 = 144287849 := by
  decide

theorem residual_chunk_3_1_34 : initialChunk 3 1 34 = 228119762 := by
  decide

theorem residual_chunk_3_1_35 : initialChunk 3 1 35 = 107269227 := by
  decide

theorem residual_chunk_3_1_36 : finalChunk 3 1 = 45509156 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_1_3 : initialPart 3 1 3 + finalChunk 3 1 = 1557862177 := by
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
  rw [residual_chunk_3_1_27, residual_chunk_3_1_28, residual_chunk_3_1_29, residual_chunk_3_1_30, residual_chunk_3_1_31, residual_chunk_3_1_32, residual_chunk_3_1_33, residual_chunk_3_1_34, residual_chunk_3_1_35, residual_chunk_3_1_36]

end LiteralP13HodgeCertificate
end GroupApproximation

