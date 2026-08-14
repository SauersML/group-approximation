import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (2, 4). -/

theorem residual_chunk_2_4_27 : initialChunk 2 4 27 = 325769861 := by
  decide

theorem residual_chunk_2_4_28 : initialChunk 2 4 28 = 142506775 := by
  decide

theorem residual_chunk_2_4_29 : initialChunk 2 4 29 = 153442338 := by
  decide

theorem residual_chunk_2_4_30 : initialChunk 2 4 30 = 122467945 := by
  decide

theorem residual_chunk_2_4_31 : initialChunk 2 4 31 = 243767297 := by
  decide

theorem residual_chunk_2_4_32 : initialChunk 2 4 32 = 145220013 := by
  decide

theorem residual_chunk_2_4_33 : initialChunk 2 4 33 = 322567034 := by
  decide

theorem residual_chunk_2_4_34 : initialChunk 2 4 34 = 199614930 := by
  decide

theorem residual_chunk_2_4_35 : initialChunk 2 4 35 = 171246492 := by
  decide

theorem residual_chunk_2_4_36 : finalChunk 2 4 = 129511605 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_4_3 : initialPart 2 4 3 + finalChunk 2 4 = 1956114290 := by
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
  rw [residual_chunk_2_4_27, residual_chunk_2_4_28, residual_chunk_2_4_29, residual_chunk_2_4_30, residual_chunk_2_4_31, residual_chunk_2_4_32, residual_chunk_2_4_33, residual_chunk_2_4_34, residual_chunk_2_4_35, residual_chunk_2_4_36]

end LiteralP13HodgeCertificate
end GroupApproximation

