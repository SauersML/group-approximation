import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTDecay

/-!
# Elements of the Higson--Kasparov--Trout algebra decay radially

Lane TWWUCT-C (WO-TWWUCT-C).  The stage generators `e^{-r²} k(foot h)` and
`e^{-r²} c(t, perp h) k(foot h)` vanish at infinity in `ℝ × H`: far out, either the foot
`foot h ∈ V` is large, so `k(foot h)` is small (`k ∈ C₀(V)`), or `t² + ‖perp h‖²` is large, so
the Gaussian factor is small (HKT 1998, §4).  Since vanishing at infinity is a closed
⋆-subalgebra condition (`decaySubalgebra`), every element of `A(H)` vanishes at infinity.

* `FinDimAffine.decaysRadially_evenGen`, `FinDimAffine.decaysRadially_oddGen`.
* `hktSubalgebra_le_decaySubalgebra : hktSubalgebra H C ≤ decaySubalgebra H C`.
* `decaysRadially_of_mem (F : HKTAlgebraOf H C)`.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe v w

namespace FinDimAffine

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (E : FinDimAffine H)

/-- Far out in `ℝ × H` with the foot bounded, the radial variable is large. -/
theorem le_radiusSq_of_lt {M S t : ℝ} {y : H} (hty : ‖E.base‖ + M + S + 2 < |t| + ‖y‖)
    (hfoot : ‖E.foot y‖ ≤ M) : S ≤ E.radiusSq (t, y) := by
  have hy := E.norm_le_base_add_foot_add_perp y
  have h2 := E.abs_add_norm_perp_le t y
  linarith

variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

theorem decaysRadially_evenGen {k : E.dir →ᵇ C} (hk : E.IsStageCoeff k) :
    DecaysRadially (E.evenGen k) := by
  intro ε hε
  obtain ⟨M, hM⟩ := hk.exists_norm_le hε
  have hk1 : 0 < ‖k‖ + 1 := by positivity
  obtain ⟨S, hS⟩ := exists_two_add_mul_exp_neg_le (div_pos hε hk1)
  refine ⟨‖E.base‖ + M + S + 2, fun t y hty => ?_⟩
  show ‖E.gaussian (t, y) • k (E.foot y)‖ ≤ ε
  rw [norm_smul, E.norm_gaussian]
  have hr0 := E.radiusSq_nonneg (t, y)
  have hpos : 0 ≤ Real.exp (-(E.radiusSq (t, y))) := (Real.exp_pos _).le
  by_cases hfoot : M < ‖E.foot y‖
  · exact (mul_le_of_le_one_left (norm_nonneg _) (exp_neg_le_one hr0)).trans (hM _ hfoot)
  · have hrad := E.le_radiusSq_of_lt hty (not_lt.1 hfoot)
    calc Real.exp (-(E.radiusSq (t, y))) * ‖k (E.foot y)‖
        ≤ Real.exp (-(E.radiusSq (t, y))) * (‖k‖ + 1) :=
          mul_le_mul_of_nonneg_left
            ((k.norm_coe_le_norm _).trans (le_add_of_nonneg_right zero_le_one)) hpos
      _ ≤ (2 + E.radiusSq (t, y)) * Real.exp (-(E.radiusSq (t, y))) * (‖k‖ + 1) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hpos (by linarith)) hk1.le
      _ ≤ ε / (‖k‖ + 1) * (‖k‖ + 1) := mul_le_mul_of_nonneg_right (hS _ hrad) hk1.le
      _ = ε := div_mul_cancel₀ ε hk1.ne'

theorem decaysRadially_oddGen {k : E.dir →ᵇ C} (hk : E.IsStageCoeff k) :
    DecaysRadially (E.oddGen k) := by
  intro ε hε
  obtain ⟨M, hM⟩ := hk.exists_norm_le hε
  have hk1 : 0 < ‖k‖ + 1 := by positivity
  obtain ⟨S, hS⟩ := exists_two_add_mul_exp_neg_le (div_pos hε hk1)
  refine ⟨‖E.base‖ + M + S + 2, fun t y hty => ?_⟩
  show ‖E.gaussian (t, y) • ((CliffordSystem.clifford (t, E.perp y) : C) * k (E.foot y))‖ ≤ ε
  rw [norm_smul, E.norm_gaussian]
  have hr0 := E.radiusSq_nonneg (t, y)
  have hpos : 0 ≤ Real.exp (-(E.radiusSq (t, y))) := (Real.exp_pos _).le
  have hc : ‖(CliffordSystem.clifford (t, E.perp y) : C)‖ ≤ |t| + ‖E.perp y‖ :=
    CliffordSystem.norm_clifford_le (H := H) (C := C) (t, E.perp y)
  have hprod : ‖(CliffordSystem.clifford (t, E.perp y) : C) * k (E.foot y)‖ ≤
      (|t| + ‖E.perp y‖) * ‖k (E.foot y)‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  calc Real.exp (-(E.radiusSq (t, y))) *
        ‖(CliffordSystem.clifford (t, E.perp y) : C) * k (E.foot y)‖
      ≤ Real.exp (-(E.radiusSq (t, y))) * ((|t| + ‖E.perp y‖) * ‖k (E.foot y)‖) :=
        mul_le_mul_of_nonneg_left hprod hpos
    _ = Real.exp (-(E.radiusSq (t, y))) * (|t| + ‖E.perp y‖) * ‖k (E.foot y)‖ :=
        (mul_assoc _ _ _).symm
    _ ≤ ε := by
        by_cases hfoot : M < ‖E.foot y‖
        · have hexp : Real.exp (-(E.radiusSq (t, y))) * (|t| + ‖E.perp y‖) ≤ 1 :=
            exp_neg_mul_le_one t ‖E.perp y‖
          exact (mul_le_of_le_one_left (norm_nonneg _) hexp).trans (hM _ hfoot)
        · have hrad := E.le_radiusSq_of_lt hty (not_lt.1 hfoot)
          have h2 := E.abs_add_norm_perp_le t y
          have hA : Real.exp (-(E.radiusSq (t, y))) * (|t| + ‖E.perp y‖) ≤
              (2 + E.radiusSq (t, y)) * Real.exp (-(E.radiusSq (t, y))) :=
            (mul_le_mul_of_nonneg_left h2 hpos).trans_eq (mul_comm _ _)
          have hB : ‖k (E.foot y)‖ ≤ ‖k‖ + 1 :=
            (k.norm_coe_le_norm _).trans (le_add_of_nonneg_right zero_le_one)
          have hA0 : 0 ≤ (2 + E.radiusSq (t, y)) * Real.exp (-(E.radiusSq (t, y))) :=
            mul_nonneg (by linarith) hpos
          calc Real.exp (-(E.radiusSq (t, y))) * (|t| + ‖E.perp y‖) * ‖k (E.foot y)‖
              ≤ (2 + E.radiusSq (t, y)) * Real.exp (-(E.radiusSq (t, y))) * (‖k‖ + 1) :=
                mul_le_mul hA hB (norm_nonneg _) hA0
            _ ≤ ε / (‖k‖ + 1) * (‖k‖ + 1) := mul_le_mul_of_nonneg_right (hS _ hrad) hk1.le
            _ = ε := div_mul_cancel₀ ε hk1.ne'

theorem decaysRadially_of_mem_stageGenerators {E : FinDimAffine H} {F : ℝ × H →ᵇ C}
    (hF : F ∈ E.stageGenerators C) : DecaysRadially F := by
  obtain ⟨k, hk, rfl | rfl⟩ := hF
  · exact E.decaysRadially_evenGen hk
  · exact E.decaysRadially_oddGen hk

end FinDimAffine

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- Every element of the Higson--Kasparov--Trout algebra vanishes at infinity on `ℝ × H`. -/
theorem hktSubalgebra_le_decaySubalgebra : hktSubalgebra H C ≤ decaySubalgebra H C := by
  show (NonUnitalStarAlgebra.adjoin ℂ
    (⋃ E : FinDimAffine H, E.stageGenerators C)).topologicalClosure ≤ _
  refine NonUnitalStarSubalgebra.topologicalClosure_minimal _ ?_ isClosed_decaySubalgebra
  refine NonUnitalStarAlgebra.adjoin_le fun F hF => ?_
  obtain ⟨E, hE⟩ := Set.mem_iUnion.1 hF
  rw [SetLike.mem_coe, mem_decaySubalgebra]
  exact FinDimAffine.decaysRadially_of_mem_stageGenerators hE

theorem decaysRadially_of_mem (F : HKTAlgebraOf H C) : DecaysRadially (F : ℝ × H →ᵇ C) :=
  mem_decaySubalgebra.1 (hktSubalgebra_le_decaySubalgebra F.2)

/-- The norm of `A(H)` is the sup norm on `ℝ × H`. -/
theorem norm_hktAlgebra (F : HKTAlgebraOf H C) : ‖F‖ = ‖(F : ℝ × H →ᵇ C)‖ :=
  rfl

end

end GroupApproximation.Full.TWWUCT
