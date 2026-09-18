import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtRing

/-!
# Completeness of the standard module `H_J`

Lane `TWWSch3d3-2C`, work order `WO-3d3-2C`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), through the Busby picture of `Ext(S, J)` used in
Schafhauser's proof of the Tikuisis--White--Winter theorem.

The operator algebra `𝓛(H_J)` is complete because `H_J = standardModule ℕ J` is. This file proves
the second fact in the `ε`--`N` form used by `StdOperatorAlgebraComplete` (Lance, *Hilbert
C⋆-modules*, Ch. 1, the example `H_A`):

* `stdModule_norm_coord_le`: `‖f i‖ ≤ ‖f‖`, so the coordinates of a Cauchy sequence are Cauchy;
* `stdModule_norm_partial_le`, `stdModule_norm_sq_le_of_partial`: the norm is controlled by, and
  controls, the finite partial sums;
* `stdModule_cauchy_limit`: every Cauchy sequence in `H_J` has a limit.

The limit is built coordinatewise; its square-summability is the Cauchy criterion for the partial
sums, obtained from the triangle inequality in the finite modules `J^t`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule Filter Topology

noncomputable section

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- A real number bounded by every positive multiple of a nonnegative constant is nonpositive
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem stdAux_le_zero {a C : ℝ} (hC : 0 ≤ C) (h : ∀ ε > 0, a ≤ ε * C) : a ≤ 0 := by
  refine le_of_not_gt fun ha => ?_
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < a / (C + 1) := div_pos ha hC1
  have h1 := h (a / (C + 1)) hδ
  have h3 : a / (C + 1) * (C + 1) = a := div_mul_cancel₀ a hC1.ne'
  nlinarith

/-- Coordinates of a difference in `H_J` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem stdModule_sub_apply (f g : (standardModule ℕ J).carrier) (i : ℕ) :
    (f - g).1 i = f.1 i - g.1 i := rfl

/-- A finite partial sum of `∑ f(i)⋆f(i)` is bounded by `‖f‖²` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem stdModule_norm_partial_le (f : (standardModule ℕ J).carrier) (s : Finset ℕ) :
    ‖∑ i ∈ s, star (f.1 i) * f.1 i‖ ≤ (standardModule ℕ J).norm f ^ 2 := by
  rw [(standardModule ℕ J).norm_sq f]
  exact OrderZero.norm_le_norm_of_nonneg_of_le
    (Finset.sum_nonneg fun i _ => star_mul_self_nonneg (f.1 i))
    (sum_le_hasSum s (fun i _ => star_mul_self_nonneg (f.1 i)) (summable_coe f).hasSum)

/-- A uniform bound on the partial sums bounds `‖f‖²` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem stdModule_norm_sq_le_of_partial (f : (standardModule ℕ J).carrier) (C : ℝ)
    (h : ∀ k, ‖∑ i ∈ Finset.range k, star (f.1 i) * f.1 i‖ ≤ C) :
    (standardModule ℕ J).norm f ^ 2 ≤ C := by
  rw [(standardModule ℕ J).norm_sq f]
  exact le_of_tendsto' (summable_coe f).hasSum.tendsto_sum_nat.norm h

/-- Each coordinate is bounded by the norm (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem stdModule_norm_coord_le (f : (standardModule ℕ J).carrier) (i : ℕ) :
    ‖f.1 i‖ ≤ (standardModule ℕ J).norm f := by
  have h := stdModule_norm_partial_le f {i}
  rw [Finset.sum_singleton, CStarRing.norm_star_mul_self, ← pow_two ‖f.1 i‖] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) ((standardModule ℕ J).norm_nonneg f)
    two_ne_zero).1 h

/-- The triangle inequality for finite partial sums, read in the module `J^s`
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem stdAux_sqrt_add_le (s : Finset ℕ) (a b : ℕ → J) :
    Real.sqrt ‖∑ i ∈ s, star (a i + b i) * (a i + b i)‖
      ≤ Real.sqrt ‖∑ i ∈ s, star (a i) * a i‖ + Real.sqrt ‖∑ i ∈ s, star (b i) * b i‖ := by
  have hpi : ∀ h : ℕ → J, (piSelf (↥s) J).norm (fun i : ↥s => h (i : ℕ))
      = Real.sqrt ‖∑ i ∈ s, star (h i) * h i‖ := by
    intro h
    rw [CStarModule.norm_def]
    congr 1
    show ‖∑ i : ↥s, star (h (i : ℕ)) * h (i : ℕ)‖ = ‖∑ i ∈ s, star (h i) * h i‖
    rw [← Finset.sum_coe_sort s]
  calc Real.sqrt ‖∑ i ∈ s, star (a i + b i) * (a i + b i)‖
      = (piSelf (↥s) J).norm ((fun i : ↥s => a (i : ℕ)) + fun i : ↥s => b (i : ℕ)) :=
        (hpi fun i => a i + b i).symm
    _ ≤ (piSelf (↥s) J).norm (fun i : ↥s => a (i : ℕ))
          + (piSelf (↥s) J).norm (fun i : ↥s => b (i : ℕ)) :=
        (piSelf (↥s) J).norm_add_le _ _
    _ = Real.sqrt ‖∑ i ∈ s, star (a i) * a i‖ + Real.sqrt ‖∑ i ∈ s, star (b i) * b i‖ := by
        rw [hpi a, hpi b]

/-- **`H_J` is complete** (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`; Lance,
Ch. 1): a sequence that is Cauchy for the Hilbert-module norm has a limit. -/
theorem stdModule_cauchy_limit (u : ℕ → (standardModule ℕ J).carrier)
    (hu : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, (standardModule ℕ J).norm (u m - u n) ≤ ε) :
    ∃ g : (standardModule ℕ J).carrier, ∀ ε > 0, ∃ N, ∀ n ≥ N,
      (standardModule ℕ J).norm (u n - g) ≤ ε := by
  have hcoord : ∀ i, CauchySeq fun n => (u n).1 i := by
    intro i
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hu (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm_sub]
    have h1 := stdModule_norm_coord_le (u m - u n) i
    rw [stdModule_sub_apply] at h1
    linarith [hN m hm n hn]
  choose g0 hg0 using fun i => cauchySeq_tendsto_of_complete (hcoord i)
  have hK : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t : Finset ℕ,
      ‖∑ i ∈ t, star (g0 i - (u n).1 i) * (g0 i - (u n).1 i)‖ ≤ ε ^ 2 := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun n hn t => ?_⟩
    have hlim : Tendsto
        (fun m => ‖∑ i ∈ t, star ((u m).1 i - (u n).1 i) * ((u m).1 i - (u n).1 i)‖)
        atTop (𝓝 ‖∑ i ∈ t, star (g0 i - (u n).1 i) * (g0 i - (u n).1 i)‖) :=
      (tendsto_finsetSum t fun i _ =>
        (((hg0 i).sub_const ((u n).1 i)).star).mul ((hg0 i).sub_const ((u n).1 i))).norm
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    have h1 := stdModule_norm_partial_le (u m - u n) t
    simp only [stdModule_sub_apply] at h1
    exact h1.trans (pow_le_pow_left₀ ((standardModule ℕ J).norm_nonneg _) (hN m hm n hn) 2)
  have hsum : Summable fun i => star (g0 i) * g0 i := by
    refine summable_iff_vanishing_norm.2 fun ε hε => ?_
    have hη : 0 < Real.sqrt ε / 3 := div_pos (Real.sqrt_pos.2 hε) (by norm_num)
    obtain ⟨N, hN⟩ := hK (Real.sqrt ε / 3) hη
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 (summable_coe (u N))
      ((Real.sqrt ε / 3) ^ 2) (pow_pos hη 2)
    refine ⟨s, fun t ht => ?_⟩
    have h1 := stdAux_sqrt_add_le t (fun i => g0 i - (u N).1 i) (fun i => (u N).1 i)
    simp only [sub_add_cancel] at h1
    have h2 : Real.sqrt ‖∑ i ∈ t, star (g0 i - (u N).1 i) * (g0 i - (u N).1 i)‖
        ≤ Real.sqrt ε / 3 :=
      (Real.sqrt_le_sqrt (hN N le_rfl t)).trans_eq (Real.sqrt_sq hη.le)
    have h3 : Real.sqrt ‖∑ i ∈ t, star ((u N).1 i) * (u N).1 i‖ < Real.sqrt ε / 3 :=
      ((Real.sqrt_lt_sqrt_iff (norm_nonneg _)).2 (hs t ht)).trans_eq (Real.sqrt_sq hη.le)
    have h4 : Real.sqrt ‖∑ i ∈ t, star (g0 i) * g0 i‖ < Real.sqrt ε := by
      linarith [Real.sqrt_nonneg ε]
    exact (Real.sqrt_lt_sqrt_iff (norm_nonneg _)).1 h4
  obtain ⟨g, hg⟩ : ∃ g : (standardModule ℕ J).carrier, ∀ i, g.1 i = g0 i :=
    ⟨⟨g0, hsum⟩, fun _ => rfl⟩
  refine ⟨g, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hK ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [← neg_sub, (standardModule ℕ J).norm_neg]
  have hp : ∀ k, ‖∑ i ∈ Finset.range k, star ((g - u n).1 i) * (g - u n).1 i‖ ≤ ε ^ 2 := by
    intro k
    simp only [stdModule_sub_apply, hg]
    exact hN n hn (Finset.range k)
  have h1 := stdModule_norm_sq_le_of_partial (g - u n) (ε ^ 2) hp
  exact (pow_le_pow_iff_left₀ ((standardModule ℕ J).norm_nonneg _) hε.le two_ne_zero).1 h1

end

end GroupApproximation.Full.TWWSchafhauser
