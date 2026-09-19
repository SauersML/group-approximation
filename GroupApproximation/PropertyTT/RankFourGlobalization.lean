import GroupApproximation.PropertyTT.KazhdanGlobalization
import GroupApproximation.PropertyTT.RankFourParabolicGeometry

/-!
# Rank-four globalization from six root estimates

The theorem in this file is independent of the coefficient ring.  Relative
`(TT)/T` on the six roots meeting one coordinate gives boundedness on the
opposite row and column parabolics.  Those parabolics generate `EL₄` and
are normalized by the stabilized `EL₃`; Kazhdan globalization therefore
gives relative `(TT)/T` for the entire stabilized rank-three subgroup.
-/

namespace GroupApproximation
namespace RankFourGlobalization

open RankFourParabolicGeometry

universe v

noncomputable section

variable {R : Type*} [Ring R]

abbrev E4 := elementaryGroup (Fin 4) R

/-- The stabilized rank-three elementary subgroup. -/
def coreRange : Subgroup (E4 (R := R)) :=
  MonoidHom.range (RankFour.coreEmbedding (A := R))

private theorem boundedOn_columnGroup
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {rho : E4 (R := R) →* (E ≃ₗᵢ[ℂ] E)} {b : E4 (R := R) → E}
    {D : ℝ} (hb : IsQuasiCocycle rho b D)
    (h0 : IsNormBoundedOn b (X03 (R := R) : Set (E4 (R := R))))
    (h1 : IsNormBoundedOn b (X13 (R := R) : Set (E4 (R := R))))
    (h2 : IsNormBoundedOn b (X23 (R := R) : Set (E4 (R := R)))) :
    IsNormBoundedOn b (columnGroup (R := R) : Set (E4 (R := R))) := by
  obtain ⟨C0, hC0, h0⟩ := h0
  obtain ⟨C1, hC1, h1⟩ := h1
  obtain ⟨C2, hC2, h2⟩ := h2
  refine ⟨C0 + C1 + C2 + 2 * D,
    add_nonneg (add_nonneg (add_nonneg hC0 hC1) hC2)
      (mul_nonneg (by norm_num) hb.1), ?_⟩
  intro g hg
  obtain ⟨a, c, d, rfl⟩ := exists_three_column_roots hg
  let x0 := elementaryRoot (0 : Fin 4) 3 (by decide) a
  let x1 := elementaryRoot (1 : Fin 4) 3 (by decide) c
  let x2 := elementaryRoot (2 : Fin 4) 3 (by decide) d
  calc
    ‖b (x0 * x1 * x2)‖ ≤ ‖b (x0 * x1)‖ + ‖b x2‖ + D :=
      hb.norm_mul_le (x0 * x1) x2
    _ ≤ (‖b x0‖ + ‖b x1‖ + D) + ‖b x2‖ + D := by
      gcongr
      exact hb.norm_mul_le x0 x1
    _ ≤ (C0 + C1 + D) + C2 + D := by
      gcongr
      · exact h0 x0 ⟨a, rfl⟩
      · exact h1 x1 ⟨c, rfl⟩
      · exact h2 x2 ⟨d, rfl⟩
    _ = C0 + C1 + C2 + 2 * D := by ring

private theorem boundedOn_rowGroup
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {rho : E4 (R := R) →* (E ≃ₗᵢ[ℂ] E)} {b : E4 (R := R) → E}
    {D : ℝ} (hb : IsQuasiCocycle rho b D)
    (h0 : IsNormBoundedOn b (X30 (R := R) : Set (E4 (R := R))))
    (h1 : IsNormBoundedOn b (X31 (R := R) : Set (E4 (R := R))))
    (h2 : IsNormBoundedOn b (X32 (R := R) : Set (E4 (R := R)))) :
    IsNormBoundedOn b (rowGroup (R := R) : Set (E4 (R := R))) := by
  obtain ⟨C0, hC0, h0⟩ := h0
  obtain ⟨C1, hC1, h1⟩ := h1
  obtain ⟨C2, hC2, h2⟩ := h2
  refine ⟨C0 + C1 + C2 + 2 * D,
    add_nonneg (add_nonneg (add_nonneg hC0 hC1) hC2)
      (mul_nonneg (by norm_num) hb.1), ?_⟩
  intro g hg
  obtain ⟨a, c, d, rfl⟩ := exists_three_row_roots hg
  let x0 := elementaryRoot (3 : Fin 4) 0 (by decide) a
  let x1 := elementaryRoot (3 : Fin 4) 1 (by decide) c
  let x2 := elementaryRoot (3 : Fin 4) 2 (by decide) d
  calc
    ‖b (x0 * x1 * x2)‖ ≤ ‖b (x0 * x1)‖ + ‖b x2‖ + D :=
      hb.norm_mul_le (x0 * x1) x2
    _ ≤ (‖b x0‖ + ‖b x1‖ + D) + ‖b x2‖ + D := by
      gcongr
      exact hb.norm_mul_le x0 x1
    _ ≤ (C0 + C1 + D) + C2 + D := by
      gcongr
      · exact h0 x0 ⟨a, rfl⟩
      · exact h1 x1 ⟨c, rfl⟩
      · exact h2 x2 ⟨d, rfl⟩
    _ = C0 + C1 + C2 + 2 * D := by ring

/-- Six relative root estimates imply boundedness on the union of the
opposite row and column parabolics. -/
theorem hasRelativeTTmodTOnSet_column_row
    (h03 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X03 (R := R)))
    (h13 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X13 (R := R)))
    (h23 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X23 (R := R)))
    (h30 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X30 (R := R)))
    (h31 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X31 (R := R)))
    (h32 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X32 (R := R))) :
    HasRelativeTTmodTOnSet.{_, v} (E4 (R := R))
      ((columnGroup (R := R) : Set (E4 (R := R))) ∪
        (rowGroup (R := R) : Set (E4 (R := R)))) := by
  intro E _ _ _ rho hno b D hb
  have hc := boundedOn_columnGroup hb
    (h03 E rho hno b D hb) (h13 E rho hno b D hb) (h23 E rho hno b D hb)
  have hr := boundedOn_rowGroup hb
    (h30 E rho hno b D hb) (h31 E rho hno b D hb) (h32 E rho hno b D hb)
  exact isNormBoundedOn_of_finite_cover ({false, true} : Finset Bool)
    ((columnGroup (R := R) : Set (E4 (R := R))) ∪
      (rowGroup (R := R) : Set (E4 (R := R))))
    (fun t ↦ if t then (rowGroup (R := R) : Set (E4 (R := R)))
      else (columnGroup (R := R) : Set (E4 (R := R))))
    (by
      intro g hg
      rcases hg with hg | hg
      · exact ⟨false, by simp, by simpa using hg⟩
      · exact ⟨true, by simp, by simpa using hg⟩)
    (by
      intro t _
      cases t
      · simpa using hc
      · simpa using hr)

/-- **General rank-four relative globalization.**  Over any ring, property
`(T)` for `EL₄` and relative `(TT)/T` for the six roots meeting the last
coordinate imply relative `(TT)/T` for the stabilized `EL₃`. -/
theorem hasRelativeTTmodT_coreRange_of_roots
    (hT : HasKazhdanPropertyT.{_, v} (E4 (R := R)))
    (h03 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X03 (R := R)))
    (h13 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X13 (R := R)))
    (h23 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X23 (R := R)))
    (h30 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X30 (R := R)))
    (h31 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X31 (R := R)))
    (h32 : HasRelativeTTmodT.{_, v} (E4 (R := R)) (X32 (R := R))) :
    HasRelativeTTmodT.{_, v} (E4 (R := R)) (coreRange (R := R)) := by
  apply hasRelativeTTmodT_of_kazhdan_of_normalized_set
    (coreRange (R := R))
    ((columnGroup (R := R) : Set (E4 (R := R))) ∪
      (rowGroup (R := R) : Set (E4 (R := R))))
    hT column_row_generate
  · intro h hh q hq
    obtain ⟨g, rfl⟩ := hh
    rcases hq with hq | hq
    · exact Or.inl ((Subgroup.mem_normalizer_iff''.mp
        (coreEmbedding_mem_normalizer_columnGroup g) q).mp hq)
    · exact Or.inr ((Subgroup.mem_normalizer_iff''.mp
        (coreEmbedding_mem_normalizer_rowGroup g) q).mp hq)
  · exact hasRelativeTTmodTOnSet_column_row h03 h13 h23 h30 h31 h32

end
end RankFourGlobalization
end GroupApproximation
