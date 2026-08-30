import GroupApproximation.Analysis.VoiculescuStageSchedule

/-!
# The approximate unit can be taken positive

`improveUnit e f` is `≥ e` because `√(1-e) f √(1-e)` is positive, and `≤ 1`
because that term is at most `1 - e`; both need `0 ≤ f ≤ 1`.  The landed (V1)
datum `QuasicentralApproximateUnitSeparableStatement` records its members as
selfadjoint contractions and says nothing about positivity, so the recursion
cannot use it as it stands.

Squaring repairs this and costs nothing.  For `f` selfadjoint, `f² = f⋆f ≥ 0`,
and `‖f²‖ ≤ ‖f‖² ≤ 1` puts it below the identity.  Both other clauses survive
because the defect of the square is the defect of the original, twice over:

    `T - f²T = (T - fT) + f (T - fT)` ,   `[f², S] = f [f, S] + [f, S] f` ,

so each is bounded by `2` times the corresponding defect of `f`.  Nothing about
the construction of the unit is touched — this is a fact about any selfadjoint
sequential unit.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive contraction is below the identity. -/
theorem le_one_of_nonneg_of_norm_le_one {a : H →L[ℂ] H} (h0 : 0 ≤ a) (hn : ‖a‖ ≤ 1) :
    a ≤ 1 := by
  refine le_trans (IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg h0)) ?_
  have h : algebraMap ℝ (H →L[ℂ] H) 1 = 1 := map_one _
  rw [← h]
  exact algebraMap_mono _ hn

/-- **The unit can be taken positive.**  Squaring a selfadjoint sequential
compact unit gives a positive one, keeping absorption and quasicentrality. -/
theorem exists_positive_sequentialCompactUnit (u : SequentialCompactUnit H)
    (S : ℕ → (H →L[ℂ] H))
    (hq : ∀ k, Tendsto (fun n ↦ ‖u.toFun n * S k - S k * u.toFun n‖) atTop (𝓝 0)) :
    ∃ v : SequentialCompactUnit H, (∀ n, 0 ≤ v.toFun n) ∧ (∀ n, v.toFun n ≤ 1) ∧
      ∀ k, Tendsto (fun n ↦ ‖v.toFun n * S k - S k * v.toFun n‖) atTop (𝓝 0) := by
  have h0 : ∀ n, (0 : H →L[ℂ] H) ≤ u.toFun n * u.toFun n := by
    intro n
    have h := star_mul_self_nonneg (u.toFun n)
    rwa [(u.isSelfAdjoint n).star_eq] at h
  have hn : ∀ n, ‖u.toFun n * u.toFun n‖ ≤ 1 := by
    intro n
    refine le_trans (norm_mul_le _ _) ?_
    nlinarith [u.norm_le n, norm_nonneg (u.toFun n)]
  have h1 : ∀ n, u.toFun n * u.toFun n ≤ 1 := fun n ↦
    le_one_of_nonneg_of_norm_le_one (h0 n) (hn n)
  refine ⟨{ toFun := fun n ↦ u.toFun n * u.toFun n
            isCompact := fun n ↦ (u.isCompact n).comp_clm (u.toFun n)
            isSelfAdjoint := fun n ↦ IsSelfAdjoint.of_nonneg (h0 n)
            norm_le := hn
            tendsto_left := fun T hT ↦ ?_ }, h0, h1, fun k ↦ ?_⟩
  · have hb : ∀ n, ‖T - u.toFun n * u.toFun n * T‖ ≤ 2 * ‖T - u.toFun n * T‖ := by
      intro n
      have hid : T - u.toFun n * u.toFun n * T
          = (T - u.toFun n * T) + u.toFun n * (T - u.toFun n * T) := by
        noncomm_ring
      rw [hid]
      refine le_trans (norm_add_le _ _) ?_
      have h2 : ‖u.toFun n * (T - u.toFun n * T)‖ ≤ ‖T - u.toFun n * T‖ := by
        refine le_trans (norm_mul_le _ _) ?_
        nlinarith [u.norm_le n, norm_nonneg (T - u.toFun n * T), norm_nonneg (u.toFun n)]
      linarith
    exact squeeze_zero (fun n ↦ norm_nonneg _) hb
      (by simpa using (u.tendsto_left T hT).const_mul 2)
  · have hb : ∀ n, ‖u.toFun n * u.toFun n * S k - S k * (u.toFun n * u.toFun n)‖
        ≤ 2 * ‖u.toFun n * S k - S k * u.toFun n‖ := by
      intro n
      have hid : u.toFun n * u.toFun n * S k - S k * (u.toFun n * u.toFun n)
          = u.toFun n * (u.toFun n * S k - S k * u.toFun n)
            + (u.toFun n * S k - S k * u.toFun n) * u.toFun n := by
        noncomm_ring
      rw [hid]
      refine le_trans (norm_add_le _ _) ?_
      have hA : ‖u.toFun n * (u.toFun n * S k - S k * u.toFun n)‖
          ≤ ‖u.toFun n * S k - S k * u.toFun n‖ := by
        refine le_trans (norm_mul_le _ _) ?_
        nlinarith [u.norm_le n, norm_nonneg (u.toFun n * S k - S k * u.toFun n),
          norm_nonneg (u.toFun n)]
      have hB : ‖(u.toFun n * S k - S k * u.toFun n) * u.toFun n‖
          ≤ ‖u.toFun n * S k - S k * u.toFun n‖ := by
        refine le_trans (norm_mul_le _ _) ?_
        nlinarith [u.norm_le n, norm_nonneg (u.toFun n * S k - S k * u.toFun n),
          norm_nonneg (u.toFun n)]
      linarith
    exact squeeze_zero (fun n ↦ norm_nonneg _) hb
      (by simpa using (hq k).const_mul 2)

end

end ShulmanFill
end GroupApproximation
