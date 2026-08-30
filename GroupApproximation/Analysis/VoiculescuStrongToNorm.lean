import GroupApproximation.Analysis.VoiculescuSequentialUnit

/-!
# Compactness upgrades strong convergence to norm convergence

`ShulmanFill.StrongToNormOnCompactsStatement` is the one analytic step (V1a)
rests on: if `P n → 1` strongly and the `P n` are contractions, then
`‖T - P n * T‖ → 0` for every compact `T`.  This module proves it.

## The core, isolated

The content is not about operators at all.  A uniformly bounded sequence of
operators converging pointwise to zero converges *uniformly on a compact set*:
cover the set by finitely many balls of radius `ε / (2(C+1))`, use pointwise
convergence at the finitely many centres, and let the uniform bound carry the
remainder.  That is `eventually_forall_norm_le_of_isCompact`, stated for an
arbitrary compact set and an arbitrary uniformly bounded pointwise null
sequence, with nothing about compact operators in it.

It is stated separately because the lane meets the same core twice more.  (V1b)
needs it for the `0`-in-the-weak-closure step, where the totally bounded set is
the image of a ball under a compact operator again; and the refutation record
owed in `Analysis/VoiculescuQuasicentralStatement` needs the same fact to see
that a compact operator cannot absorb a vector orthogonal to the ranges of
countably many others.

## From the core to the statement

`T` compact gives a compact `K` containing the image of the closed unit ball
(`IsCompactOperator.image_closedBall_subset_compact`).  Apply the core to
`A n := 1 - P n`, uniformly bounded by `2`, pointwise null by hypothesis, on
`K`; then `T - P n * T = (1 - P n) * T` sends the unit ball into `A n '' K`, and
homogeneity turns the bound on the unit ball into the operator norm bound.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

section Core

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The core.**  A uniformly bounded, pointwise null sequence of operators is
eventually uniformly small on a compact set. -/
theorem eventually_forall_norm_le_of_isCompact
    (A : ℕ → (E →L[ℂ] F)) {C : ℝ} (hC : ∀ n, ‖A n‖ ≤ C)
    (hptwise : ∀ v : E, Tendsto (fun n ↦ A n v) atTop (𝓝 0))
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y ∈ K, ‖A n y‖ ≤ ε := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg (A 0)) (hC 0)
  set δ : ℝ := ε / (2 * (C + 1)) with hδdef
  have hδ : 0 < δ := by
    refine div_pos hε ?_
    linarith
  obtain ⟨s, hsfin, hs⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded δ hδ
  have hcentre : ∀ᶠ n in atTop, ∀ y ∈ s, ‖A n y‖ ≤ ε / 2 := by
    rw [eventually_all_finite hsfin]
    intro y _
    have h := (hptwise y).norm
    rw [norm_zero] at h
    exact h.eventually_le_const (by linarith : (0 : ℝ) < ε / 2)
  refine hcentre.mono fun n hn y hy ↦ ?_
  obtain ⟨z, hzs, hz⟩ := Set.mem_iUnion₂.mp (hs hy)
  have hzy : ‖y - z‖ ≤ δ := by
    rw [← dist_eq_norm]
    exact le_of_lt (Metric.mem_ball.mp hz)
  have hsplit : A n y = A n (y - z) + A n z := by
    rw [← map_add]
    congr 1
    abel
  have h1 : ‖A n (y - z)‖ ≤ C * δ :=
    le_trans ((A n).le_opNorm (y - z))
      (mul_le_mul (hC n) hzy (norm_nonneg _) hC0)
  have h2 : C * δ ≤ ε / 2 := by
    rw [hδdef]
    rw [mul_div_assoc']
    refine div_le_of_le_mul₀ (by linarith) (by linarith) ?_
    nlinarith
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have := hn z hzs
  linarith

end Core

section Main

/-- **Against a compact operator, strong convergence to the identity is norm
convergence.**  This closes the analytic step (V1a) was reduced to. -/
theorem strongToNormOnCompacts : StrongToNormOnCompactsStatement := by
  intro H _ _ _ P hP hstrong T hT
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨K, hKcompact, hKsub⟩ :=
    hT.image_closedBall_subset_compact (𝕜₁ := ℂ) (r := 1)
  have hbound : ∀ n : ℕ, ‖(1 : H →L[ℂ] H) - P n‖ ≤ 2 := by
    intro n
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    linarith [hP n]
  have hptwise : ∀ v : H,
      Tendsto (fun n ↦ ((1 : H →L[ℂ] H) - P n) v) atTop (𝓝 0) := by
    intro v
    have h := (hstrong v).const_sub v
    rw [sub_self] at h
    exact h.congr fun n ↦ rfl
  have hcore := eventually_forall_norm_le_of_isCompact
    (fun n ↦ (1 : H →L[ℂ] H) - P n) hbound hptwise hKcompact
    (half_pos hε)
  refine hcore.mono fun n hn ↦ ?_
  have hop : ‖T - P n * T‖ ≤ ε / 2 := by
    have hrw : T - P n * T = ((1 : H →L[ℂ] H) - P n) * T := by
      rw [sub_mul, one_mul]
    rw [hrw]
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun x ↦ ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hunit : T (‖x‖⁻¹ • x) ∈ K := by
        refine hKsub ⟨‖x‖⁻¹ • x, ?_, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
          norm_norm]
        rw [inv_mul_cancel₀ (ne_of_gt hxpos)]
      have := hn _ hunit
      rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.map_smul_of_tower,
        norm_smul, norm_inv, norm_norm] at this
      show ‖((1 : H →L[ℂ] H) - P n) (T x)‖ ≤ ε / 2 * ‖x‖
      rw [inv_mul_le_iff₀ hxpos] at this
      linarith [this]
  simp only [norm_norm]
  linarith [hop]

end Main

end

end ShulmanFill
end GroupApproximation
