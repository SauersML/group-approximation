import GroupApproximation.Analysis.VoiculescuSqrtCommutator
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A uniform modulus for the square-root commutator

The corona square-root lemma is qualitative: given *sequences*, null commutators
stay null after square roots.  A recursion cannot use it in that form, because a
recursion makes one choice at a time and needs to know, at stage `j`, that some
single operator already available has a square-root commutator below `2⁻ʲ`.

The gap closes for free, because the corona lemma quantifies over a sequence in
*both* arguments.  `VoiculescuSqrtCommutator.tendsto_norm_commutator_sqrt_bh`
takes an arbitrary bounded positive sequence `a` and an arbitrary bounded
sequence `b`; so if the uniform statement failed, the witnesses at
`δ = 1/(n+1)` would assemble into exactly such a pair, and the lemma would
contradict them.  That is the whole proof of `exists_delta_norm_commutator_sqrt`
below: a single application of the sequence form to the sequence of
counterexamples.

The bounds `‖a‖ ≤ M` and `‖b‖ ≤ M` are what make that assembly possible — the
counterexamples have to land in `ℓ^∞` — so they are hypotheses of the modulus
rather than an artefact of the statement.  They cost nothing where it is used:
the operators the recursion feeds it are contractions.

`tendsto_norm_commutator_sqrt_of_modulus` runs the implication backwards, from
the modulus to the sequence form, so the two are equivalent and the contradiction
argument gave up nothing.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The uniform modulus.**  On operators of norm at most `M`, a small enough
commutator with a positive `a` forces a small commutator with `√a`, with a
threshold that does not depend on `a` or `b`. -/
theorem exists_delta_norm_commutator_sqrt (M ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : H →L[ℂ] H, 0 ≤ a → ‖a‖ ≤ M → ‖b‖ ≤ M →
      ‖a * b - b * a‖ < δ → ‖CFC.sqrt a * b - b * CFC.sqrt a‖ < ε := by
  rcases subsingleton_or_nontrivial H with hsub | hnt
  · haveI := hsub
    refine ⟨1, one_pos, fun a b _ _ _ _ ↦ ?_⟩
    have h : CFC.sqrt a * b - b * CFC.sqrt a = 0 :=
      ContinuousLinearMap.ext fun x ↦ Subsingleton.elim _ _
    rw [h, norm_zero]
    exact hε
  · haveI := hnt
    by_contra hcon
    push Not at hcon
    choose A B hA0 hAM hBM hcomm hbad using fun n : ℕ ↦
      hcon (1 / ((n : ℝ) + 1)) (by positivity)
    let a : BoundedCStarSequence (fun _ : ℕ ↦ H →L[ℂ] H) :=
      ⟨A, memℓp_infty ⟨M, by rintro _ ⟨n, rfl⟩; exact hAM n⟩⟩
    let b : BoundedCStarSequence (fun _ : ℕ ↦ H →L[ℂ] H) :=
      ⟨B, memℓp_infty ⟨M, by rintro _ ⟨n, rfl⟩; exact hBM n⟩⟩
    have hcoeA : ∀ n, a n = A n := fun _ ↦ rfl
    have hcoeB : ∀ n, b n = B n := fun _ ↦ rfl
    have hnull : Tendsto (fun n ↦ ‖a n * b n - b n * a n‖) atTop (𝓝 0) := by
      simp only [hcoeA, hcoeB]
      exact squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (hcomm n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hsq := tendsto_norm_commutator_sqrt_bh atTop a b
      (fun n ↦ by rw [hcoeA]; exact hA0 n) hnull
    simp only [hcoeA, hcoeB] at hsq
    exact absurd (ge_of_tendsto' hsq hbad) (not_le.mpr hε)

/-- **The modulus is not weaker than the sequence form it came from.**  Running
it along a bounded positive sequence with null commutators returns exactly
`tendsto_norm_commutator_sqrt_bh`, so the contradiction argument gave nothing
away. -/
theorem tendsto_norm_commutator_sqrt_of_modulus
    (hmod : ∀ M ε : ℝ, 0 < ε → ∃ δ > 0, ∀ a b : H →L[ℂ] H, 0 ≤ a → ‖a‖ ≤ M →
      ‖b‖ ≤ M → ‖a * b - b * a‖ < δ → ‖CFC.sqrt a * b - b * CFC.sqrt a‖ < ε)
    (a b : BoundedCStarSequence fun _ : ℕ ↦ H →L[ℂ] H) (ha : ∀ n, 0 ≤ a n)
    (hab : Tendsto (fun n ↦ ‖a n * b n - b n * a n‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖CFC.sqrt (a n) * b n - b n * CFC.sqrt (a n)‖) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hmod'⟩ := hmod (max ‖a‖ ‖b‖) ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hab δ hδ
  refine ⟨N, fun n hn ↦ ?_⟩
  have hlt : ‖a n * b n - b n * a n‖ < δ := by
    have := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  have hgoal := hmod' (a n) (b n) (ha n)
    (le_trans (boundedCStarSequence_coord_norm_le _ a n) (le_max_left _ _))
    (le_trans (boundedCStarSequence_coord_norm_le _ b n) (le_max_right _ _)) hlt
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]

end

end ShulmanFill
end GroupApproximation
