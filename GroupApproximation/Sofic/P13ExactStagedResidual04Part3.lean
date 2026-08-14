import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (0, 4). -/

theorem residual_chunk_0_4_27 : initialChunk 0 4 27 = 423804752 := by
  decide

theorem residual_chunk_0_4_28 : initialChunk 0 4 28 = 127414522 := by
  decide

theorem residual_chunk_0_4_29 : initialChunk 0 4 29 = 281504671 := by
  decide

theorem residual_chunk_0_4_30 : initialChunk 0 4 30 = 93258888 := by
  decide

theorem residual_chunk_0_4_31 : initialChunk 0 4 31 = 237222437 := by
  decide

theorem residual_chunk_0_4_32 : initialChunk 0 4 32 = 98380628 := by
  decide

theorem residual_chunk_0_4_33 : initialChunk 0 4 33 = 364263359 := by
  decide

theorem residual_chunk_0_4_34 : initialChunk 0 4 34 = 168545334 := by
  decide

theorem residual_chunk_0_4_35 : initialChunk 0 4 35 = 227414321 := by
  decide

theorem residual_chunk_0_4_36 : finalChunk 0 4 = 97670360 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_4_3 : initialPart 0 4 3 + finalChunk 0 4 = 2119479272 := by
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
  rw [residual_chunk_0_4_27, residual_chunk_0_4_28, residual_chunk_0_4_29, residual_chunk_0_4_30, residual_chunk_0_4_31, residual_chunk_0_4_32, residual_chunk_0_4_33, residual_chunk_0_4_34, residual_chunk_0_4_35, residual_chunk_0_4_36]

end LiteralP13HodgeCertificate
end GroupApproximation

